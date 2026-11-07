#!/usr/bin/env python3
"""Generate AArch64 differential test cases (see x86gen.py / README.md).

    armgen.py <kernel-objdump.txt> <outdir> <seed> [states_per_instr] [per_template]

Snippets `c_<j>`: the instruction(s), then `b kt_back` (a tail call: the translator's
`.tailcall`); literal loads get their literal after the branch.  x18 is the trampoline's branch
register (the kernels never use it): not randomised, not compared."""
import json
import os
import random
import re
import sys

W = 4096
MID = 16384
rng = random.Random()


def r64():
    return rng.getrandbits(64)


def xr(s):
    s = s.strip()
    if s in ('sp', 'wsp'):
        return 31
    m = re.match(r'^[xw](\d+)$', s)
    return int(m.group(1)) if m else None


def split_args(s):
    return [a.strip() for a in re.split(r',(?![^\[\{]*[\]\}])', s)]


class Roles:
    def __init__(self):
        self.ptr = {}      # reg -> list of byte offsets accessed relative to it (pre/offset forms)
        self.count = set()
        self.pairs = []
        self.align16 = set()
        self.data = set()     # operands of data operations


def analyze(lines):
    roles = Roles()
    for text in lines:
        text = re.sub(r'^\d+:\s*', '', text.strip())
        if not text or text.startswith('.'):
            continue
        parts = text.split(None, 1)
        op = parts[0]
        args = split_args(parts[1]) if len(parts) > 1 else []
        for a in args:
            m = re.match(r'^\[(\w+)(?:, #(-?\w+))?\](!?)(?:, #(-?\w+))?$', a)
            if m:
                b = xr(m.group(1))
                roles.ptr.setdefault(b, []).append(int(m.group(2), 0) if m.group(2) else 0)
        if op in ('eor', 'bic', 'ror') and not args[0].startswith('v'):
            for a in args[:3]:
                if xr(a) is not None and xr(a) != 31:
                    roles.data.add(xr(a))
        if op in ('cmp', 'subs', 'cbz'):
            roles.count.add(xr(args[0]))
            if op == 'subs':
                roles.count.add(xr(args[1]))
        if op in ('add', 'sub') and not args[0].startswith('v'):
            if xr(args[1]) != 31:
                roles.count.add(xr(args[1]))
    return roles


def gval(role):
    if role == 'count':
        k = rng.random()
        if k < 0.6:
            return ('d', rng.choice([0, 1, 2, 3, 4, 5, 6, 7, 8, 63, 64, rng.randrange(200)]))
        if k < 0.7:
            return ('d', rng.choice([rng.randrange(1 << 32), rng.randrange(1 << 55), 1 << 31]))
        if k < 0.85:
            return ('d', rng.randrange(1 << 56))
        return ('p', rng.choice([1, 2, 3]), MID + 16 * rng.randrange(-32, 32))
    if role == 'ptr':
        return ('p', rng.choice([1, 2, 3]), MID + 16 * rng.randrange(-32, 32))
    k = rng.random()          # data: never a pointer (the model's pointer encoding is not the address)
    if k < 0.75:
        return ('d', r64())
    if k < 0.85:
        return ('d', rng.choice([0, 1, (1 << 64) - 1, 1 << 63]))
    return ('d', rng.choice([0, 1, 2, 3, 8, 64, rng.randrange(200)]))


def enc(v):
    if v[0] == 'd':
        return '%x' % (v[1] % (1 << 64)), False
    return '%x' % ((v[1] << 56) + v[2]), True


def make_state(roles):
    g = {i: gval(rng.choice(['data', 'data', 'count', 'ptr'])) for i in range(31)}
    for r in roles.data:
        g[r] = gval('data')
    g[18] = ('d', 0)
    g[31] = ('p', 3, MID + 16 * rng.randrange(-32, 32))
    for r in roles.count:
        if r is not None and r != 18:
            g[r] = gval('count')
    for b, offs in roles.ptr.items():
        if b is None or b == 18:
            continue
        reg = 3 if b == 31 else rng.choice([1, 2, 3])
        base = MID + 16 * rng.randrange(-100, 100)
        if b != 31 and rng.random() < 0.03:
            base += rng.choice([4, 8])
        g[b] = ('p', reg, base)
    out = []
    for i in range(32):
        h, p = enc(g[i])
        out.append('G %d %s%s' % (i, h, ' P' if p else ''))
    for i in range(32):
        out.append('V %d %s' % (i, ' '.join('%x' % w for w in [r64(), r64()] + [0] * 6)))
    out.append('F %d %d %d %d' % tuple(rng.randrange(2) for _ in range(4)))
    return out


CONTROL = {'b', 'ret', 'cbz', 'nop'}


def kernel_instrs(dis):
    seen = set()
    for ln in open(dis):
        m = re.match(r'^\s+[0-9a-f]+:\t(.*)$', ln.rstrip('\n'))
        if not m:
            continue
        text = re.sub(r'\s*//.*$', '', m.group(1)).strip()
        op = text.split()[0]
        if op == '.insn':
            raise SystemExit('undecoded instruction in the kernel disassembly: ' + text)
        if op in CONTROL or op.startswith('b.') or op.startswith('.'):
            continue
        ml = re.match(r'^ldr\s+([qx]\d+), [0-9a-f]+ <', text)
        if ml:
            text = 'ldr %s, LIT' % ml.group(1)
        seen.add(text)
    return sorted(seen)


def V(k='16b'):
    return 'v%d.%s' % (rng.randrange(32), k)


def X(no_sp=True):
    while True:
        r = rng.randrange(31)
        if r != 18:
            return 'x%d' % r


def memx(size=8, wb_ok=True):
    b = rng.choice(['sp', X()])
    off = size * rng.randrange(-16 if wb_ok else 0, 16) if b != 'sp' else 16 * rng.randrange(0, 32)
    k = rng.random()
    if wb_ok and k < 0.15:
        return '[%s, #%d]!' % (b, off)
    if wb_ok and k < 0.3:
        return '[%s], #%d' % (b, off)
    if off == 0 and k < 0.5:
        return '[%s]' % b
    return '[%s, #%d]' % (b, off)


def t_arm():
    c = rng.randrange(30)
    if c == 0:
        return ['eor %s, %s, %s' % (V(), V(), V())]
    if c == 1:
        return ['bic %s, %s, %s' % (V(), V(), V())]
    if c == 2:
        return ['eor3 %s, %s, %s, %s' % (V(), V(), V(), V())]
    if c == 3:
        return ['bcax %s, %s, %s, %s' % (V(), V(), V(), V())]
    if c == 4:
        return ['rax1 %s, %s, %s' % (V('2d'), V('2d'), V('2d'))]
    if c == 5:
        return ['xar %s, %s, %s, #%d' % (V('2d'), V('2d'), V('2d'), rng.randrange(64))]
    if c == 6:
        return ['shl %s, %s, #%d' % (V('2d'), V('2d'), rng.randrange(64))]
    if c == 7:
        return ['sri %s, %s, #%d' % (V('2d'), V('2d'), rng.randrange(1, 65))]
    if c == 8:
        return ['add %s, %s, %s' % (V('2d'), V('2d'), V('2d'))]
    if c == 9:
        return ['tbl %s, {%s}, %s' % (V(), V(), V())]
    if c == 10:
        return ['%s %s, %s, %s' % (rng.choice(['zip1', 'zip2']), V('2d'), V('2d'), V('2d'))]
    if c == 11:
        return ['mov %s, %s' % (V(), V())]
    if c == 12:
        return ['movi %s, #0' % V('2d')]
    if c == 13:
        return ['%s %s, %s, %s, ror #%d' % (rng.choice(['eor', 'bic']), X(), X(), X(), rng.randrange(64))]
    if c == 14:
        return ['%s %s, %s, %s' % (rng.choice(['eor', 'bic']), X(), X(), X())]
    if c == 15:
        return ['ror %s, %s, #%d' % (X(), X(), rng.randrange(64))]
    if c == 16:
        return ['mov %s, %s' % (rng.choice([X(), X(), 'sp']), rng.choice([X(), X(), 'sp']))]
    if c == 17:
        return ['mov %s, #0x%x' % (X(), rng.choice([rng.randrange(1 << 16), rng.randrange(1 << 16) << 16, 0xffffffffffff0000 | rng.randrange(1 << 16)]))]
    if c == 18:
        return ['%s %s, %s, #0x%x' % (rng.choice(['add', 'sub', 'subs']), X(), X(), rng.randrange(1 << 12))]
    if c == 19:
        return ['cmp %s, #0x%x' % (X(), rng.randrange(70))]
    if c == 20:
        return ['csel %s, %s, %s, %s' % (X(), X(), X(), rng.choice(['eq', 'ne', 'cs', 'cc', 'gt', 'hs', 'lo']))]
    if c == 21:
        r = rng.choice(['q%d' % rng.randrange(32), 'x%d' % rng.choice([i for i in range(31) if i != 18]), 'd%d' % rng.randrange(32)])
        size = {'q': 16, 'x': 8, 'd': 8}[r[0]]
        return ['ldr %s, %s' % (r, memx(size, False))]
    if c == 22:
        r = rng.choice(['q%d' % rng.randrange(32), 'x%d' % rng.choice([i for i in range(31) if i != 18]), 'd%d' % rng.randrange(32)])
        size = {'q': 16, 'x': 8, 'd': 8}[r[0]]
        return ['str %s, %s' % (r, memx(size, False))]
    if c in (23, 24):
        k = rng.choice(['q', 'x', 'd'])
        if k == 'x':
            a, b = rng.sample([i for i in range(31) if i != 18], 2)
        else:
            a, b = rng.sample(range(32), 2)
        size = {'q': 16, 'x': 8, 'd': 8}[k]
        return ['%s %s%d, %s%d, %s' % ('ldp' if c == 23 else 'stp', k, a, k, b, memx(size))]
    if c == 25:
        return ['ldr q%d, LIT' % rng.randrange(32)]
    if c == 26:
        return ['ldr x%d, LIT' % rng.choice([i for i in range(31) if i != 18])]
    if c == 27:
        return ['cmp %s, #0x%x' % (X(), rng.randrange(5)), 'b.%s 1f' % rng.choice(['eq', 'ne', 'cs', 'cc', 'gt', 'hs', 'lo']),
                'b kt_back', '1: b kt_back2']
    if c == 28:
        return ['cbz %s, 1f' % X(), 'b kt_back', '1: b kt_back2']
    return ['subs %s, %s, #0x%x' % (X(), X(), rng.randrange(4)), 'b.%s 1f' % rng.choice(['eq', 'ne', 'cs', 'cc', 'gt']),
            'b kt_back', '1: b kt_back2', ]


def emit_snip(f, j, lines):
    f.write('.globl c_%d\n.type c_%d, %%function\nc_%d:\n' % (j, j, j))
    lit = None
    for ln in lines:
        if ', LIT' in ln:
            lit = (r64(), r64())
            ln = ln.replace('LIT', '9f')
        f.write('\t%s\n' % ln)
    if not lines[-1].split(':')[-1].strip().startswith('b kt_back'):
        f.write('\tb kt_back\n')
    if lit:
        f.write('\t.balign 8\n9:\t.quad 0x%x, 0x%x\n' % lit)


def main():
    dis, outdir, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
    nstate = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    ntempl = int(sys.argv[5]) if len(sys.argv) > 5 else 40
    rng.seed(seed)
    snips, states = [], []

    def add(lines, src, n):
        j = len(snips)
        snips.append(lines)
        roles = analyze(lines)
        for _ in range(n):
            states.append((j, rng.getrandbits(63), make_state(roles), src, ' ; '.join(lines)))

    for t in kernel_instrs(dis):
        add([t], 'kernel', nstate)
    for _ in range(ntempl * 30):
        add(t_arm(), 'tmpl-arm', 2)
    d = os.path.join(outdir, 'arm')
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, 'cases.S'), 'w') as f:
        f.write('.arch armv8.2-a+sha3\n.text\n.globl kt_text0\nkt_text0:\n')
        for j, lines in enumerate(snips):
            emit_snip(f, j, lines)
        f.write('.section .rodata\n.balign 64\nkt_ro:\n\t.quad 0\n')
        f.write('.section .data.rel.ro\n.globl kt_ro_addr\n.balign 8\nkt_ro_addr:\n\t.quad kt_ro\n')
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
    print('arm', len(snips), 'snippets', len(states), 'states')


if __name__ == '__main__':
    main()
