#!/usr/bin/env python3
"""Generate RISC-V differential test cases (see x86gen.py / README.md).

    rvgen.py <kernel-objdump.txt> <outdir> <seed> <vlen> [states_per_instr] [per_template]

Snippets `c_<j>` end in `ret` (ra = the trampoline's kt_back; the model halts).  Branch templates
mark the taken path by `addi t6, t6, 1`.  ra, gp, tp are not part of the test (kernel instructions
writing ra are tested with t6 in its place)."""
import json
import os
import random
import re
import sys

W = 4096
MID = 16384
rng = random.Random()
REGS = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
        's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
IDX = {r: i for i, r in enumerate(REGS)}
IDX['fp'] = 8
FREE = [r for r in REGS if r not in ('zero', 'ra', 'sp', 'gp', 'tp')]


def r64():
    return rng.getrandbits(64)


def R():
    return rng.choice(FREE)


class Roles:
    def __init__(self):
        self.ptr = set()
        self.count = set()
        self.shift = set()
        self.seg = 0


def analyze(lines):
    roles = Roles()
    for text in lines:
        text = re.sub(r'^\d+:\s*', '', text.strip())
        if not text or text.startswith('.'):
            continue
        parts = text.split(None, 1)
        op = parts[0]
        args = [a.strip() for a in re.split(r',(?![^(]*\))', parts[1])] if len(parts) > 1 else []
        for a in args:
            m = re.match(r'^(-?\d+)?\((\w+)\)$', a)
            if m:
                roles.ptr.add(m.group(2))
        if op in ('beqz', 'bnez', 'beq', 'bne', 'bgeu'):
            for a in args[:-1]:
                roles.count.add(a)
        if op == 'vsetvli':
            roles.count.add(args[1])
        if op.endswith('.vx') and op.split('.')[0] in ('vsll', 'vsrl', 'vror'):
            roles.shift.add(args[2])
        m = re.match(r'^v[ls]seg(\d)e64\.v$', op)
        if m:
            roles.seg = int(m.group(1))
    return roles


def gval(role):
    if role == 'count':
        k = rng.random()
        if k < 0.7:
            return ('d', rng.choice([0, 1, 2, 3, 4, 5, 7, 8, 9, 16, 17, rng.randrange(100)]))
        if k < 0.85:
            return ('d', rng.randrange(1 << 56))
        return ('p', rng.choice([1, 2, 3]), MID + 8 * rng.randrange(-32, 32))
    k = rng.random()
    if k < 0.8:
        return ('d', r64())
    if k < 0.9:
        return ('d', rng.choice([0, 1, (1 << 64) - 1, 1 << 63]))
    return ('d', rng.randrange(200))


def enc(v):
    if v[0] == 'd':
        return '%x' % (v[1] % (1 << 64)), False
    return '%x' % ((v[1] << 56) + v[2]), True


def make_state(roles, vlmax):
    g = {i: gval('data') for i in range(32)}
    g[0] = ('d', 0)
    g[1] = g[3] = g[4] = ('d', 0)
    g[2] = ('p', 3, MID + 16 * rng.randrange(-32, 32))
    for r in roles.count:
        if r in IDX and IDX[r] not in (0, 1, 3, 4):
            g[IDX[r]] = gval('count')
    pair = [r for r in roles.count if r in IDX]
    if len(pair) == 2 and rng.random() < 0.4:
        a, b = IDX[pair[0]], IDX[pair[1]]
        if rng.random() < 0.5:
            g[b] = g[a]
        elif g[a][0] == 'p':
            g[b] = ('p', g[a][1], g[a][2] + 8 * rng.choice([-1, 1]))
    for r in roles.shift:
        g[IDX[r]] = ('d', rng.choice([rng.randrange(64), rng.randrange(64), rng.randrange(128), r64()]))
    for r in roles.ptr:
        if r in IDX and IDX[r] not in (0, 1, 3, 4):
            base = MID + 8 * rng.randrange(-200, 200)
            if rng.random() < 0.03:
                base += 4
            g[IDX[r]] = ('p', 3 if r == 'sp' else rng.choice([1, 2, 3]), base)
    out = []
    for i in range(32):
        h, p = enc(g[i])
        out.append('G %d %s%s' % (i, h, ' P' if p else ''))
    for i in range(32):
        out.append('V %d %s' % (i, ' '.join('%x' % (r64() if l < vlmax else 0) for l in range(8))))
    out.append('L %d' % rng.choice([vlmax, vlmax, rng.randrange(vlmax + 1)]))
    out.append('F 0 0 0 0')
    return out


CONTROL = {'j', 'bnez', 'beqz', 'bne', 'beq', 'bgeu', 'ret', 'nop', 'auipc'}
UNMODELLED = {'lbu', 'sb', 'vle8.v', 'vse8.v'}


def kernel_instrs(dis):
    seen = set()
    for ln in open(dis):
        m = re.match(r'^\s+[0-9a-f]+:\t(.*)$', ln.rstrip('\n'))
        if not m:
            continue
        text = re.sub(r'\s*#.*$', '', m.group(1)).strip()
        op = text.split()[0]
        if op == '.insn':
            raise SystemExit('undecoded instruction in the kernel disassembly: ' + text)
        if op in CONTROL or op in UNMODELLED:
            continue
        if op == 'vsetvli' and 'e64,m1' not in text:
            continue
        a = text.split(None, 1)[1].split(',')
        if a[0] == 'ra':     # keep ra as the return address
            text = text.replace('ra', 't6', 1)
        text = re.sub(r'\bra\b', 't6', text) if op in ('sd', 'mv', 'xor', 'and', 'or') else text
        seen.add(text)
    return sorted(seen)


def V(lo=0, hi=32):
    return 'v%d' % rng.randrange(lo, hi)


def mem(nf=1):
    b = rng.choice(FREE + ['sp'])
    return '%d(%s)' % (8 * rng.randrange(-60, 60), b)


def t_rv():
    c = rng.randrange(27)
    if c == 0:
        return ['%s %s, %s, %s' % (rng.choice(['xor', 'or', 'and', 'add', 'sub', 'andn']), R(), R(), R())]
    if c == 1:
        op = rng.choice(['xori', 'ori', 'andi', 'addi'])
        return ['%s %s, %s, %d' % (op, R(), R(), rng.randrange(-2048, 2048))]
    if c == 2:
        return ['%s %s, %s, %d' % (rng.choice(['slli', 'srli', 'rori']), R(), R(), rng.randrange(64))]
    if c == 3:
        return ['li %s, %d' % (R(), rng.randrange(-2048, 2048))]
    if c == 4:
        return ['mv %s, %s' % (R(), rng.choice(FREE + ['sp']))]
    if c == 5:
        return ['not %s, %s' % (R(), R())]
    if c == 6:
        r = R()
        return ['1: auipc %s, %%pcrel_hi(.LRC+%d)' % (r, 8 * rng.randrange(32)), 'ld %s, %%pcrel_lo(1b)(%s)' % (r, r)]
    if c == 7:
        return ['ld %s, %s' % (R(), mem())]
    if c == 8:
        return ['sd %s, %s' % (R(), mem())]
    if c == 9:
        cnd = rng.choice(['beqz %s, 1f' % R(), 'bnez %s, 1f' % R(), 'beq %s, %s, 1f' % (R(), R()),
                          'bne %s, %s, 1f' % (R(), R()), 'bgeu %s, %s, 1f' % (R(), R())])
        return [cnd, 'ret', '1: addi t6, t6, 1']
    if c == 10:
        return ['j 1f', 'ret', '1: addi t6, t6, 1']
    if c == 11:
        return ['vsetvli %s, %s, e64, m1, %s, %s' % (R(), R(), rng.choice(['ta', 'tu']), rng.choice(['ma', 'mu']))]
    if c == 12:
        return ['%s %s, %s, %s' % (rng.choice(['vxor.vv', 'vand.vv', 'vor.vv', 'vandn.vv']), V(), V(), V())]
    if c == 13:
        return ['vnot.v %s, %s' % (V(), V())]
    if c == 14:
        return ['%s %s, %s, %d' % (rng.choice(['vsll.vi', 'vsrl.vi']), V(), V(), rng.randrange(32))]
    if c == 15:
        return ['vror.vi %s, %s, %d' % (V(), V(), rng.randrange(64))]
    if c == 16:
        return ['%s %s, %s, %s' % (rng.choice(['vsll.vx', 'vsrl.vx', 'vror.vx']), V(), V(), R())]
    if c == 17:
        return ['vxor.vx %s, %s, %s' % (V(), V(), R())]
    if c == 18:
        return ['vmv.v.i %s, %d' % (V(), rng.randrange(-16, 16))]
    if c == 19:
        return ['vmv.v.x %s, %s' % (V(), R())]
    if c == 20:
        return ['vmv.v.v %s, %s' % (V(), V())]
    if c in (21, 22):
        nf = rng.randrange(2, 9)
        d = rng.randrange(0, 33 - nf)
        b = rng.choice(FREE + ['sp'])
        return ['%s%de64.v v%d, (%s)' % ('vlseg' if c == 21 else 'vsseg', nf, d, b)]
    if c == 23:
        return ['vsetvli zero, %s, e64, m1, ta, ma' % R(), 'vxor.vv %s, %s, %s' % (V(), V(), V())]
    if c == 24:
        return ['xor %s, %s, %s' % (R(), R(), R())]
    if c == 25:
        return ['andn %s, %s, %s' % (R(), R(), R())]
    return ['rori %s, %s, %d' % (R(), R(), rng.randrange(64))]


def main():
    dis, outdir, seed, vlen = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    nstate = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    ntempl = int(sys.argv[6]) if len(sys.argv) > 6 else 40
    vlmax = vlen // 64
    rng.seed(seed * 1000 + vlen)
    snips, states = [], []

    def add(lines, src, n):
        j = len(snips)
        snips.append(lines)
        roles = analyze(lines)
        for _ in range(n):
            states.append((j, rng.getrandbits(63), make_state(roles, vlmax), src, ' ; '.join(lines)))

    for t in kernel_instrs(dis):
        if t.startswith('ld ') and re.search(r'\(t\d\)$', t) and False:
            continue
        add([t], 'kernel', nstate)
    for _ in range(ntempl * 27):
        add(t_rv(), 'tmpl-rv', 2)
    d = os.path.join(outdir, 'rv%d' % vlen)
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, 'cases.S'), 'w') as f:
        f.write('.option norvc\n.option norelax\n.attribute arch, "rv64gcv_zbb_zvkb"\n.text\n.globl kt_text0\nkt_text0:\n')
        for j, lines in enumerate(snips):
            f.write('.globl c_%d\n.type c_%d, @function\nc_%d:\n' % (j, j, j))
            for ln in lines:
                f.write('\t%s\n' % ln)
            if lines[-1].strip() != 'ret':
                f.write('\tret\n')
        f.write('.section .rodata\n.balign 64\n.LRC:\n')
        for _ in range(64):
            f.write('\t.quad 0x%x\n' % r64())
        f.write('.section .data.rel.ro\n.globl kt_ro_addr\n.balign 8\nkt_ro_addr:\n\t.quad .LRC\n')
        f.write('.section .note.GNU-stack,"",@progbits\n')
    with open(os.path.join(d, 'table.S'), 'w') as f:
        f.write('.section .data.rel.ro\n.globl kt_cases\n.balign 8\nkt_cases:\n')
        for j in range(len(snips)):
            f.write('\t.quad c_%d\n' % j)
        f.write('.section .note.GNU-stack,"",@progbits\n')
    meta = []
    with open(os.path.join(d, 'states.txt'), 'w') as f:
        for j, sd, lines, src, text in states:
            f.write('C %d %x\n' % (j, sd))
            for ln in lines:
                f.write(ln + '\n')
            f.write('E\n')
            meta.append({'snip': j, 'src': src, 'text': text})
    json.dump(meta, open(os.path.join(d, 'meta.json'), 'w'))
    print('rv%d' % vlen, len(snips), 'snippets', len(states), 'states')


if __name__ == '__main__':
    main()
