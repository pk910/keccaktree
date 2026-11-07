#!/usr/bin/env python3
"""Generate x86-64 differential test cases.

    x86gen.py <kernel-objdump.txt> <outdir> <seed> [states_per_instr] [per_template]

Writes two test sets, `<outdir>/avx2` (VEX/scalar forms, run natively) and
`<outdir>/avx512` (EVEX forms, run under Intel SDE), each with
  cases.S      one function `c_<j>` per snippet (`<instr>... ; jmp kt_back`),
               the test constants (`kt_ro` in .rodata, `kt_dat` in .data)
  table.S      `kt_cases`: the snippet addresses, `kt_text0`
  states.txt   initial states (format: README.md)
  meta.json    per state: snippet, source (kernel instruction or template), text
Snippets: every distinct non-control instruction of the x86 kernels (operands
as in the kernels; rip-relative constants redirected into the test constants),
plus random instances of every modelled instruction form (templates), plus
control-flow templates (flag setter + jcc / jcc to another function / jmp /
call + ret).
"""
import json
import os
import random
import re
import sys

W = 4096            # words per memory region (harness.c)
MID = 16384         # byte offset of the middle of a region
GPRS = ['rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi',
        'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15']
R32 = {'eax': 'rax', 'ecx': 'rcx', 'edx': 'rdx', 'ebx': 'rbx', 'esp': 'rsp', 'ebp': 'rbp', 'esi': 'rsi',
       'edi': 'rdi'}
for _i in range(8, 16):
    R32['r%dd' % _i] = 'r%d' % _i

# constant image: word ranges by use
RO = {'data': (0, 64), 'count': (64, 96), 'shufb': (96, 128), 'perm': (128, 160), 'shift': (160, 192),
      'mask': (192, 208), 'data2': (208, 256)}
RO_WORDS = 256
DAT_WORDS = 16

rng = random.Random()


def r64():
    return rng.getrandbits(64)


def rodata_image():
    ws = []
    for q in range(RO_WORDS):
        if RO['count'][0] <= q < RO['count'][1]:
            ws.append(rng.choice([0, 1, 2, 3, 4, 5, 8, 9, 10, 63, 64, rng.randrange(0, 100), rng.randrange(0, 1 << 40)]))
        elif RO['shufb'][0] <= q < RO['shufb'][1]:
            ws.append(int.from_bytes(bytes(rng.choice([rng.randrange(16), rng.randrange(256)]) for _ in range(8)), 'little'))
        elif RO['perm'][0] <= q < RO['perm'][1]:
            ws.append(rng.choice([rng.randrange(16), rng.randrange(1 << 64)]))
        elif RO['shift'][0] <= q < RO['shift'][1]:
            ws.append(rng.choice([rng.randrange(64), rng.randrange(64), rng.randrange(80), rng.randrange(1 << 64)]))
        elif RO['mask'][0] <= q < RO['mask'][1]:
            ws.append(r64())
        else:
            ws.append(r64())
    return ws


def gname(r):
    r = r.strip()
    return R32.get(r, r)


def gidx(r):
    return GPRS.index(gname(r))


class Roles:
    def __init__(self):
        self.ptr = {}          # gpr -> (region or None, disp) : base register of a memory operand
        self.count = set()     # gprs that should mostly hold small numbers
        self.pairs = []        # (gpr, gpr) compared with each other: same kind
        self.memov = []        # (gpr base, disp, kind) memory word overrides ('count'|'ptrcmp:<gpr>'|'any')
        self.vshift = set()    # vector registers holding per-lane shift counts
        self.rep = False
        self.stack_any = False # rsp may be an unaligned stack pointer (and rsp, -64)
        self.align = 0         # aligned vector move: operand size
        self.data = set()      # data operands of data operations (never pointers: the model's pointer
                               # encoding is not the machine address; the kernels never compute on pointers)
        self.r32 = set()       # registers read by 32-bit forms (upper half zero: the translator's domain)
        self.memptr = []       # (base, disp): memory word that may hold a pointer (add [m], imm)


MEMRE = re.compile(r'\[(\w+)(?:([+-])(0x[0-9a-f]+|\d+|kt_ro\+\d+|kt_dat\+\d+))?\]')


def parse_mem(a):
    m = re.search(r'\[(\w+)(?:\s*([+-])\s*([^\]]+))?\]', a)
    if not m:
        return None
    base = m.group(1)
    d = 0
    if m.group(3) and base != 'rip':
        d = int(m.group(3), 0)
        if m.group(2) == '-':
            d = -d
    return base, d


def split_args(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch == '[':
            depth += 1
        elif ch == ']':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def analyze(lines, roles=None):
    roles = roles or Roles()
    for text in lines:
        text = text.strip()
        if not text or text.endswith(':') or text.startswith('1:') and len(text) == 2:
            continue
        if re.match(r'^\d+:', text):
            text = text.split(':', 1)[1].strip()
            if not text:
                continue
        parts = text.split(None, 1)
        op = parts[0]
        args = split_args(parts[1]) if len(parts) > 1 else []
        mems = [a for a in args if '[' in a]
        if op in ('vmovdqa', 'vmovdqa64') and mems:
            roles.align = {'XMMWORD': 16, 'YMMWORD': 32, 'ZMMWORD': 64}[mems[0].split()[0]]
        for a in mems:
            b, d = parse_mem(a)
            if op == 'kmovw':
                d = 0          # keep the base aligned: the byte offset is the displacement
            if b != 'rip':
                roles.ptr[gname(b)] = (3 if gname(b) == 'rsp' else roles.ptr.get(gname(b), (None, 0))[0], d)
        gargs = [gname(a) for a in args if gname(a) in GPRS]
        if op in ('cmp', 'test', 'sub', 'dec', 'shl'):
            for a in args:
                if gname(a) in GPRS and gname(a) != 'rsp':
                    roles.count.add(gname(a))
            if len(gargs) == 2:
                roles.pairs.append((gargs[0], gargs[1]))
            if op == 'cmp' and mems and not mems[0].startswith('QWORD PTR [rip') and '[rip' not in mems[0]:
                b, d = parse_mem(mems[0])
                other = [g for g in gargs]
                roles.memov.append((gname(b), d, 'ptrcmp:' + (other[0] if other else '')))
            if op == 'dec' and mems:
                b, d = parse_mem(mems[0])
                roles.memov.append((gname(b), d, 'count'))
        if op == 'bt':
            roles.count.add(gname(args[1]))
            roles.data.add(gname(args[0]))
        if op in ('xor', 'and', 'or', 'add', 'andn', 'rorx', 'btc') and not (op == 'add' and len(args) == 2 and not mems and re.match(r'^-?(0x)?\d', args[1])) \
                and not (op == 'xor' and len(args) == 2 and args[0] == args[1]):
            for a in args:
                if gname(a) in GPRS:
                    roles.data.add(gname(a))
        if op == 'add' and mems and mems[0] == args[0]:
            b, d = parse_mem(mems[0])
            roles.memptr.append((gname(b), d))
        if re.search(r'\b(e[a-d]x|e[sd]i|e[sb]p|r\d+d)\b', text) and op in ('dec', 'cmp', 'test'):
            roles.r32.add(gname(args[0]))
        if op == 'add' and not mems and len(gargs) == 1 and gargs[0] != 'rsp' and re.match(r'^-?(0x)?\d', args[1]):
            roles.count.add(gargs[0])   # a pointer or a count; count role mixes both
        if op == 'and' and args and args[0] == 'rsp':
            roles.stack_any = True
        if op in ('vpsllvq', 'vpsrlvq') and not ('[' in args[2]):
            roles.vshift.add(int(re.sub(r'\D', '', args[2])))
        if op == 'rep':
            roles.rep = True
        if op in ('push', 'pop', 'call', 'ret'):
            roles.ptr['rsp'] = (3, -8 if op in ('push', 'call') else 0)
    return roles


def gval(role):
    """a general-register value: ('d', word) or ('p', region, offset)"""
    if role == 'count':
        k = rng.random()
        if k < 0.55:
            return ('d', rng.choice([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 63, 64, 65, rng.randrange(200)]))
        if k < 0.65:
            return ('d', rng.choice([rng.randrange(1 << 32), rng.randrange(1 << 55), (1 << 56) - 1, 1 << 31, 1 << 32]))
        if k < 0.80:
            return ('d', rng.randrange(1 << 56))
        return ('p', rng.choice([1, 2, 3]), MID + 8 * rng.randrange(-64, 64))
    if role == 'pure':
        if rng.random() < 0.8:
            return ('d', r64())
        return ('d', rng.choice([0, 1, (1 << 64) - 1, 1 << 63, (1 << 63) - 1, 0x00ffffffffffffff, rng.randrange(100)]))
    if role == 'ptr':
        return ('p', rng.choice([1, 2, 3]), MID + 8 * rng.randrange(-64, 64))
    k = rng.random()
    if k < 0.7:
        return ('d', r64())
    if k < 0.8:
        return ('d', rng.choice([0, 1, (1 << 64) - 1, 1 << 63, (1 << 63) - 1, 0x00ffffffffffffff]))
    if k < 0.9:
        return gval('count')
    return gval('ptr')


def enc(v):
    if v[0] == 'd':
        return '%x' % (v[1] % (1 << 64)), False
    return '%x' % ((v[1] << 56) + v[2]), True


def make_state(roles, avx512, kind_hint=None):
    """random initial state honouring the roles; returns the text block lines (without C/E)"""
    g = {}
    for r in GPRS:
        g[r] = gval(rng.choice(['data', 'data', 'count', 'ptr']))
    g['rsp'] = ('p', 3, MID + 8 * rng.randrange(-32, 32))
    for r in roles.count:
        g[r] = gval('count')
    for r in roles.data:
        g[r] = gval('pure')

    for a, b in roles.pairs:
        k = rng.random()
        if k < 0.4:     # two counts
            g[a], g[b] = gval('count'), gval('count')
            if g[a][0] == 'p':
                g[a] = ('d', rng.randrange(100))
            if g[b][0] == 'p':
                g[b] = ('d', rng.randrange(100))
            if rng.random() < 0.3:
                g[b] = g[a]
        elif k < 0.6 and a != 'rsp' and b != 'rsp':   # two pointers into one region
            reg = rng.choice([1, 2, 3])
            g[a] = ('p', reg, MID + 8 * rng.randrange(-16, 16))
            g[b] = ('p', reg, MID + 8 * rng.randrange(-16, 16)) if rng.random() < 0.7 else g[a]
    for r in roles.r32:     # the translator's domain for 32-bit forms: upper half zero, dec of non-zero
        g[r] = ('d', rng.choice([1, 2, 3, 4, rng.randrange(1, 1 << 32)]))
    mem = []
    for base, (region, disp) in roles.ptr.items():
        if base == 'rsp' and roles.stack_any:
            continue
        reg = region or rng.choice([1, 2, 3])
        eff = MID + 8 * rng.randrange(-200, 200)
        if roles.align:
            eff -= eff % roles.align
            if not avx512 and rng.random() < 0.05:
                eff += 8                  # misaligned aligned move: the CPU faults
        elif rng.random() < 0.03:
            eff += rng.choice([1, 4])     # a few misaligned accesses (the model must fail, or agree)
        g[base] = ('p', reg, eff - disp)
    if roles.stack_any:
        g['rsp'] = ('p', 3, MID + 8 * rng.randrange(-32, 32))
    if roles.rep:
        n = 8 * rng.randrange(0, 40)
        if rng.random() < 0.1:
            n += rng.randrange(1, 8)
        g['rcx'] = ('d', n)
        a, b = rng.sample([1, 2, 3], 2) if rng.random() < 0.8 else (2, 2)
        g['rsi'] = ('p', a, MID - 1024 + 8 * rng.randrange(0, 64))
        g['rdi'] = ('p', b, MID - 1024 + 8 * rng.randrange(0, 64))
        if a == b:
            g['rdi'] = ('p', b, MID + 1024 + 8 * rng.randrange(0, 64))
    for base, disp, kind in roles.memov:
        b = g.get(base)
        if not b or b[0] != 'p':
            continue
        q = (b[2] + disp) // 8
        if kind == 'count':
            w = ('d', rng.choice([1, 1, 2, 3, rng.randrange(100), rng.randrange(1 << 40), rng.randrange(1 << 56)]))
        else:
            other = kind.split(':', 1)[1]
            o = g.get(other)
            k = rng.random()
            if o and o[0] == 'p' and k < 0.7:
                w = ('p', o[1], o[2] + 8 * rng.choice([-1, 0, 0, 1, 2]))
            elif o and o[0] == 'd' and k < 0.7:
                w = ('d', max(0, o[1] + rng.choice([-1, 0, 0, 1, 2])) if o[1] < (1 << 56) else o[1])
            else:
                w = gval('count')
        mem.append((b[1], q, w))
    for base, disp in roles.memptr:
        b = g.get(base)
        if b and b[0] == 'p' and rng.random() < 0.5:
            mem.append((b[1], (b[2] + disp) // 8, ('p', rng.choice([1, 2, 3]), MID + 8 * rng.randrange(-64, 64))))
    out = []
    for i, r in enumerate(GPRS):
        h, p = enc(g[r])
        out.append('G %d %s%s' % (i, h, ' P' if p else ''))
    for i in range(32):
        lanes = []
        for l in range(8):
            if i in roles.vshift:
                lanes.append(rng.choice([rng.randrange(64), rng.randrange(64), rng.randrange(100), r64()]))
            else:
                lanes.append(r64())
        out.append('V %d %s' % (i, ' '.join('%x' % w for w in lanes)))
    for i in range(8):
        out.append('K %d %d' % (i, rng.randrange(1 << 16) if i else 0xffff))
    out.append('F %d %d 0 0' % (rng.randrange(2), rng.randrange(2)))
    for r, q, w in mem:
        h, p = enc(w)
        out.append('M %d %d %s%s' % (r, q, h, ' P' if p else ''))
    return out


def ro_ref(kind):
    lo, hi = RO[kind]
    return 'kt_ro+%d' % (8 * rng.randrange(lo, hi - 8))


def ro_kind(op):
    if op in ('vpshufb',):
        return 'shufb'
    if op in ('vpermt2q',):
        return 'perm'
    if op in ('vpsllvq', 'vpsrlvq'):
        return 'shift'
    if op in ('kmovw',):
        return 'mask'
    if op in ('cmp', 'sub', 'test', 'dec'):
        return 'count'
    return rng.choice(['data', 'data2'])


EVEX_HINT = re.compile(r'zmm|\{k|BCST|[xy]mm(1[6-9]|2\d|3[01])\b|\bk[0-7]\b')
EVEX_OPS = {'vpternlogq', 'vprolq', 'vpermt2q', 'vshufi64x2', 'kmovw', 'vmovdqa64', 'vmovdqu64', 'vpxorq',
            'vpandq', 'vpandnq', 'vporq'}


def is_evex(text):
    op = text.split()[0]
    return op in EVEX_OPS or bool(EVEX_HINT.search(text))


CONTROL = {'je', 'jne', 'ja', 'jb', 'jae', 'jbe', 'jz', 'jnz', 'jc', 'jnc', 'jmp', 'call', 'ret'}
SKIP = {'nop', 'data16', 'cs', 'nopw', 'nopl'}


def kernel_instrs(dis_path):
    """distinct non-control kernel instructions, rip operands redirected"""
    seen = {}
    lines = open(dis_path).read().splitlines()
    i = 0
    while i < len(lines):
        m = re.match(r'^\s+([0-9a-f]+):\t(.*)$', lines[i])
        if not m:
            i += 1
            continue
        text = re.sub(r'\s+#.*$', '', m.group(2)).strip()
        reloc = None
        if i + 1 < len(lines):
            mr = re.match(r'^\s+[0-9a-f]+: (R_X86_64_\w+)\t(.*)$', lines[i + 1])
            if mr:
                reloc = mr.group(2)
        i += 1
        op = text.split()[0]
        if op in CONTROL or op in SKIP or (op == 'xchg' and len(set(split_args(text.split(None, 1)[1]))) == 1):
            continue
        a0 = split_args(text.split(None, 1)[1])[0] if len(text.split(None, 1)) > 1 else ''
        if '[rip' in a0 and op not in ('cmp',):
            continue     # a store to the constants (the model refuses it: err)
        key = (text, reloc.split('+')[0].split('-')[0] if reloc else None)
        seen[key] = seen.get(key, 0) + 1
    return seen


def redirect(text, sec):
    op = text.split()[0]
    if '[rip+0x0]' not in text:
        return text
    if sec == '.data':
        return text.replace('[rip+0x0]', '[rip+kt_dat+%d]' % (8 * rng.randrange(DAT_WORDS - 1)))
    return text.replace('[rip+0x0]', '[rip+%s]' % ro_ref(ro_kind(op)))


# ---------------------------------------------------------------- templates (random instruction forms)

def vr(n, kind, hi=16):
    return '%s%d' % (kind, rng.randrange(hi))


def memop(width, kind='data'):
    b = rng.choice(['rsi', 'rdi', 'rax', 'rbx', 'r8', 'r9', 'r10', 'r11', 'rsp', 'rbp'])
    if rng.random() < 0.25:
        return '%s PTR [rip+%s]' % (width, ro_ref(kind))
    d = 8 * rng.randrange(-40, 40)
    return '%s PTR [%s%s0x%x]' % (width, b, '+' if d >= 0 else '-', abs(d))


def src_v(kind, width, hi=16, opkind='data', allow_mem=True):
    if allow_mem and rng.random() < 0.3:
        return memop(width, opkind)
    return vr(0, kind, hi)


def qword_imm_shufd():
    # whole-qword selections (the model's domain) mostly, any immediate sometimes
    if rng.random() < 0.8:
        a, b = rng.choice([0, 1]), rng.choice([0, 1])
        return (2 * a) | ((2 * a + 1) << 2) | ((2 * b) << 4) | ((2 * b + 1) << 6)
    return rng.randrange(256)


def blend_imm(n):
    if rng.random() < 0.8:
        imm = 0
        for i in range(n):
            if rng.random() < 0.5:
                imm |= 3 << (2 * i)
        return imm
    return rng.randrange(256)


def t_avx2():
    """one random VEX instruction"""
    w = rng.choice([('ymm', 'YMMWORD', 4), ('xmm', 'XMMWORD', 2)])
    K, WID, n = w
    c = rng.randrange(19)
    D, A = vr(0, K), vr(0, K)
    if c == 0:
        return ['%s %s, %s' % (rng.choice(['vmovdqu', 'vmovdqa']), D, src_v(K, WID))]
    if c == 1:
        return ['%s %s, %s' % (rng.choice(['vmovdqu', 'vmovdqa']), memop_nr(WID), A)]
    if c == 2:
        return ['%s %s, %s, %s' % (rng.choice(['vpxor', 'vpand', 'vpandn', 'vpor', 'vpaddq']), D, A, src_v(K, WID))]
    if c == 3:
        return ['%s %s, %s, %d' % (rng.choice(['vpsllq', 'vpsrlq']), D, A, rng.choice([rng.randrange(64), rng.randrange(256)]))]
    if c == 4:
        return ['%s %s, %s, %s' % (rng.choice(['vpsllvq', 'vpsrlvq']), D, A, src_v(K, WID, opkind='shift'))]
    if c == 5:
        return ['vpshufb %s, %s, %s' % (D, A, src_v(K, WID, opkind='shufb'))]
    if c == 6:
        return ['vpshufd %s, %s, %d' % (D, A, qword_imm_shufd())]
    if c == 7:
        return ['vpblendd %s, %s, %s, %d' % (D, A, src_v(K, WID), blend_imm(n))]
    if c == 8:
        return ['vpalignr %s, %s, %s, %d' % (D, A, src_v(K, WID), rng.choice([0, 8, 16, 24, 32, rng.randrange(40)]))]
    if c == 9:
        return ['%s %s, %s, %s' % (rng.choice(['vpunpcklqdq', 'vpunpckhqdq']), D, A, src_v(K, WID))]
    if c == 10:
        return ['vperm2i128 %s, %s, %s, %d' % (vr(0, 'ymm'), vr(0, 'ymm'), src_v('ymm', 'YMMWORD'), rng.randrange(256))]
    if c == 11:
        b = memop('XMMWORD') if rng.random() < 0.4 else vr(0, 'xmm')
        return ['vinserti128 %s, %s, %s, %d' % (vr(0, 'ymm'), vr(0, 'ymm'), b, rng.randrange(4))]
    if c == 12:
        return ['vextracti128 %s, %s, %d' % (memop_nr('XMMWORD'), vr(0, 'ymm'), rng.randrange(4))]
    if c == 13:
        return ['vzeroupper']
    if c == 14:
        return ['vpxor %s, %s, %s' % (D, D, D)]
    if c == 15:
        return ['%s %s, %s' % (rng.choice(['vmovdqu', 'vmovdqa']), D, A)]
    if c == 16:
        return ['vpsllvq %s, %s, %s' % (D, A, vr(0, K))]
    if c == 17:
        return ['vpshufb %s, %s, %s' % (D, A, vr(0, K))]
    return ['vpaddq %s, %s, %s' % (D, A, src_v(K, WID))]


def memop_nr(width):
    """a memory destination (no rip: the constants are read-only)"""
    b = rng.choice(['rsi', 'rdi', 'rax', 'rbx', 'r8', 'r9', 'r10', 'r11', 'rsp', 'rbp'])
    d = 8 * rng.randrange(-40, 40)
    return '%s PTR [%s%s0x%x]' % (width, b, '+' if d >= 0 else '-', abs(d))


def t_avx512():
    K, WID, n = rng.choice([('zmm', 'ZMMWORD', 8), ('zmm', 'ZMMWORD', 8), ('ymm', 'YMMWORD', 4), ('xmm', 'XMMWORD', 2)])
    D, A = vr(0, K, 32), vr(0, K, 32)

    def s(opkind='data', bc=True):
        x = rng.random()
        if bc and x < 0.15:
            if rng.random() < 0.4:
                return 'QWORD BCST [rip+%s]' % ro_ref(opkind)
            b = rng.choice(['rsi', 'rdi', 'r9', 'r10', 'rsp'])
            return 'QWORD BCST [%s+0x%x]' % (b, 8 * rng.randrange(40))
        if x < 0.4:
            return memop(WID, opkind)
        return vr(0, K, 32)
    c = rng.randrange(17)
    if c == 0:
        mask = '{k%d}' % rng.randrange(1, 8) if rng.random() < 0.5 else ''
        return ['%s %s%s, %s' % (rng.choice(['vmovdqa64', 'vmovdqu64']), D, mask, s(bc=False))]
    if c == 1:
        return ['%s %s, %s' % (rng.choice(['vmovdqa64', 'vmovdqu64']), memop_nr(WID), A)]
    if c == 2:
        return ['%s %s, %s, %s' % (rng.choice(['vpxorq', 'vpandq', 'vpandnq', 'vporq', 'vpaddq']), D, A, s())]
    if c == 3:
        return ['vprolq %s, %s, %d' % (D, A, rng.choice([rng.randrange(64), rng.randrange(256)]))]
    if c == 4:
        return ['vpternlogq %s, %s, %s, %d' % (D, A, s(), rng.randrange(256))]
    if c == 5:
        return ['%s %s, %s, %d' % (rng.choice(['vpsllq', 'vpsrlq']), D, A, rng.choice([rng.randrange(64), rng.randrange(256)]))]
    if c == 6:
        if K == 'xmm':
            K, D, A = 'ymm', vr(0, 'ymm', 32), vr(0, 'ymm', 32)
            WID = 'YMMWORD'
        return ['vshufi64x2 %s, %s, %s, %d' % (D, A, s() if WID != 'XMMWORD' else vr(0, K, 32), rng.randrange(256))]
    if c == 7:
        return ['vpermt2q %s, %s, %s' % (D, A, s())]
    if c == 8:
        return ['%s %s, %s, %s' % (rng.choice(['vpsllvq', 'vpsrlvq']), D, A, s('shift'))]
    if c == 9:
        return ['vpshufb %s, %s, %s' % (D, A, s('shufb', bc=False))]
    if c == 10:
        return ['kmovw k%d, WORD PTR [rip+%s]' % (rng.randrange(1, 8), 'kt_ro+%d' % (8 * rng.randrange(*RO['mask']) + rng.randrange(7)))]
    if c == 11:
        return ['%s %s, %s, %s' % (rng.choice(['vpunpcklqdq', 'vpunpckhqdq']), D, A, s())]
    if c == 12:
        return ['vpxorq %s, %s, %s' % (D, A, s())]
    if c == 13:
        return ['vpermt2q %s, %s, %s' % (D, A, vr(0, K, 32))]
    if c == 14:
        return ['vpaddq %s, %s, %s' % (D, A, s())]
    if c == 15:
        return ['vpalignr %s, %s, %s, %d' % (D, A, s(bc=False), rng.choice([0, 8, 16, 24, 32]))]
    return ['vpternlogq %s, %s, %s, %d' % (D, A, vr(0, K, 32), rng.randrange(256))]


def G(no_rsp=True):
    regs = [r for r in GPRS if not (no_rsp and r == 'rsp')]
    return rng.choice(regs)


def imm32():
    return rng.choice([rng.randrange(-200, 200), rng.randrange(-(1 << 31), 1 << 31), 0, 1, 8, 0x40, -1])


def t_scalar():
    c = rng.randrange(32)
    a, b = G(), G()
    if c == 0:
        return ['mov %s, %s' % (a, b)]
    if c == 1:
        return ['movabs %s, 0x%x' % (a, r64()) if rng.random() < 0.5 else 'mov %s, %d' % (a, imm32())]
    if c == 2:
        return ['mov %s, %s' % (a, memop('QWORD', 'data'))]
    if c == 3:
        return ['mov %s, %s' % (memop_nr('QWORD'), b)]
    if c == 4:
        return ['mov %s, %d' % (memop_nr('QWORD'), imm32())]
    if c == 5:
        if rng.random() < 0.3:
            return ['lea %s, [rip+%s]' % (a, ro_ref('data'))]
        return ['lea %s, [%s%+d]' % (a, G(False), 8 * rng.randrange(-100, 100))]
    if c == 6:
        return ['add %s, %d' % (G(False), rng.choice([rng.randrange(-512, 512), 8, 64, 0x140]))]
    if c == 7:
        return ['sub %s, %d' % (G(False), rng.choice([rng.randrange(0, 512), 1, 2, 8]))]
    if c == 8:
        return ['and rsp, -64']
    if c == 9:
        return ['shl %s, %d' % (a, rng.randrange(64))]
    if c == 10:
        return ['dec %s' % a]
    if c == 11:
        return ['xor %s, %s' % (a, a)]
    if c == 12:
        return ['cmp %s, %d' % (a, abs(imm32()))]
    if c == 13:
        return ['cmp %s, %s' % (a, b)]
    if c == 14:
        return ['cmp %s, %s' % (memop_nr('QWORD'), b)]
    if c == 15:
        return ['cmp %s, %s' % (a, memop('QWORD', 'count'))]
    if c == 16:
        return ['test %s, %s' % (a, rng.choice([a, b]))]
    if c == 17:
        return ['bt %s, %s' % (a, b)]
    if c == 18:
        return ['btc %s, %d' % (a, rng.randrange(64))]
    if c == 19:
        op = rng.choice(['xor', 'and', 'or', 'add'])
        x = rng.random()
        while b == a:
            b = G()
        src = b if x < 0.5 else (str(imm32()) if x < 0.75 else memop('QWORD'))
        return ['%s %s, %s' % (op, a, src)]
    if c == 20:
        return ['andn %s, %s, %s' % (a, b, G() if rng.random() < 0.6 else memop('QWORD'))]
    if c == 21:
        return ['rorx %s, %s, %d' % (a, b if rng.random() < 0.6 else memop('QWORD'), rng.randrange(64))]
    if c == 22:
        return ['xor %s, %s' % (memop_nr('QWORD'), b)]
    if c == 23:
        return ['add %s, %d' % (memop_nr('QWORD'), imm32())]
    if c == 24:
        return ['dec %s' % memop_nr('QWORD')]
    if c == 25:
        return ['push %s' % G(False)]
    if c == 26:
        return ['pop %s' % a]
    if c == 27:
        return ['xchg %s, %s' % (a, b)]
    if c == 28:
        return ['rep movsb']
    if c == 29:
        return [rng.choice(['cmp eax, %d' % rng.randrange(10), 'test eax, eax', 'dec ecx', 'mov eax, %d' % rng.randrange(40),
                            'xor eax, eax', 'mov ecx, %d' % rng.randrange(20)])]
    if c == 30:
        return ['lea rsp, [rbp-0x%x]' % (8 * rng.randrange(10))]
    return ['cmp rdx, QWORD PTR [rip+kt_dat+%d]' % (8 * rng.randrange(DAT_WORDS - 1))]


SETTERS = lambda: rng.choice([
    lambda: 'cmp %s, %d' % (G(), rng.randrange(0, 70)),
    lambda: 'cmp %s, %s' % (G(), G()),
    lambda: 'cmp %s, %s' % (memop_nr('QWORD'), G()),
    lambda: 'cmp %s, QWORD PTR [rip+kt_dat+%d]' % (G(), 8 * rng.randrange(DAT_WORDS - 1)),
    lambda: 'test %s, %s' % ((lambda r: (r, r))(G())),
    lambda: 'dec %s' % G(),
    lambda: 'dec %s' % memop_nr('QWORD'),
    lambda: 'sub rdx, %d' % rng.randrange(0, 12),
    lambda: 'xor %s, %s' % ((lambda r: (r, r))(G())),
    lambda: 'bt %s, %s' % (G(), G()),
    lambda: 'cmp eax, %d' % rng.randrange(5),
    lambda: 'test eax, eax',
    lambda: 'dec ecx',
])()


def t_control():
    c = rng.randrange(5)
    cc = rng.choice(['je', 'jne', 'jb', 'ja', 'jae', 'jbe', 'jz', 'jnz', 'jc', 'jnc'])
    if c <= 1:
        return [SETTERS(), '%s 1f' % cc, 'jmp kt_back', '1: jmp kt_back2']
    if c == 2:
        return [SETTERS(), '%s kt_back2' % cc, 'jmp kt_back']
    if c == 3:
        return ['jmp 1f', 'jmp kt_back2', '1: jmp kt_back']
    return ['call 1f', 'jmp kt_back', '1: ret']


def fix_align(ln):
    """aligned vector moves from the constants: an aligned offset"""
    if ln.split()[0] in ('vmovdqa', 'vmovdqa64'):
        ln = re.sub(r'kt_ro\+(\d+)', lambda m: 'kt_ro+%d' % (int(m.group(1)) // 64 * 64), ln)
    return ln


def main():
    dis, outdir, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
    nstate = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    ntempl = int(sys.argv[5]) if len(sys.argv) > 5 else 40
    rng.seed(seed)
    sets = {'avx2': {'snips': [], 'states': []}, 'avx512': {'snips': [], 'states': []}}

    def add(setname, lines, src, n):
        S = sets[setname]
        lines = [fix_align(ln) for ln in lines]
        r = analyze(lines)
        if src.startswith('tmpl') and (set(r.ptr) & r.data):
            return
        j = len(S['snips'])
        S['snips'].append(lines)
        roles = analyze(lines)
        for _ in range(n):
            S['states'].append((j, rng.getrandbits(63), make_state(roles, setname == 'avx512'), src, ' ; '.join(lines)))

    for (text, sec), cnt in sorted(kernel_instrs(dis).items()):
        t = redirect(text, sec)
        add('avx512' if is_evex(text) else 'avx2', [t], 'kernel', nstate)
    for _ in range(ntempl * 19):
        add('avx2', t_avx2(), 'tmpl-avx2', 2)
    for _ in range(ntempl * 17):
        add('avx512', t_avx512(), 'tmpl-avx512', 2)
    for _ in range(ntempl * 32):
        add('avx2', t_scalar(), 'tmpl-scalar', 2)
    for _ in range(ntempl * 10):
        add('avx2', t_control(), 'tmpl-control', 2)
    ro = rodata_image()
    dat = [rng.choice([0, 1, 2, 4, 5, 8, 9, rng.randrange(64), rng.randrange(1 << 50)]) for _ in range(DAT_WORDS)]
    for name, S in sets.items():
        d = os.path.join(outdir, name)
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, 'cases.S'), 'w') as f:
            f.write('.intel_syntax noprefix\n.text\n.globl kt_text0\nkt_text0:\n')
            for j, lines in enumerate(S['snips']):
                f.write('.globl c_%d\nc_%d:\n' % (j, j))
                for ln in lines:
                    f.write('\t%s\n' % ln)
                if not any(ln.split(':')[-1].strip().startswith('jmp kt_back') for ln in lines[-1:]):
                    f.write('\tjmp kt_back\n')
            f.write('.section .rodata\n.balign 64\nkt_ro:\n')
            for q in range(0, RO_WORDS, 4):
                f.write('\t.quad %s\n' % ', '.join('0x%x' % w for w in ro[q:q + 4]))
            f.write('.data\n.balign 64\nkt_dat:\n\t.quad %s\n' % ', '.join('0x%x' % w for w in dat))
            f.write('.section .data.rel.ro\n.globl kt_ro_addr\n.balign 8\nkt_ro_addr:\n\t.quad kt_ro\n')
            f.write('.section .note.GNU-stack,"",@progbits\n')
        with open(os.path.join(d, 'table.S'), 'w') as f:
            f.write('.section .data.rel.ro\n.globl kt_cases\n.balign 8\nkt_cases:\n')
            for j in range(len(S['snips'])):
                f.write('\t.quad c_%d\n' % j)
            f.write('.section .note.GNU-stack,"",@progbits\n')
        meta = []
        with open(os.path.join(d, 'states.txt'), 'w') as f:
            for n, (j, sd, lines, src, text) in enumerate(S['states']):
                f.write('C %d %x\n' % (j, sd))
                for ln in lines:
                    f.write(ln + '\n')
                f.write('E\n')
                meta.append({'snip': j, 'src': src, 'text': text})
        json.dump(meta, open(os.path.join(d, 'meta.json'), 'w'))
        print(name, len(S['snips']), 'snippets', len(S['states']), 'states')


if __name__ == '__main__':
    main()
