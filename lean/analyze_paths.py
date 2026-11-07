#!/usr/bin/env python3
"""Code-path inventory of a kernel from `kttool paths <kernel> <maxcount> <fuel> 0` output.

Usage: analyze_paths.py <kernel> <nodes> <isa> <paths.txt> <out.json> <Program.lean>

For every count the executed instruction-index path is split at the visits of the kernel's
outer loop head (the instruction, found on the largest count, whose visits cut the path into the
longest repeated identical pieces); counts whose paths agree up to the number of loop iterations
form a class.  A forward taint analysis over each path (registers, flags, stack/memory cells named
by an abstract base register + offset, the RVV `vl`) starting from the count register (x86 rdx,
AArch64 x2, RISC-V a2) lists every instruction that reads a count-derived value, the
count-dependent branches, and whether the batch body/subroutine reads the count in data
(vector registers, stores outside the stack)."""
import json, re, sys, collections

kernel, nodes, isa, src, out, progfile = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4], sys.argv[5], sys.argv[6]

# ---------------------------------------------------------------- inputs
prog = {}
for ln in open(progfile):
    m = re.match(r'^  (\..*?),?\s+-- (\d+)$', ln)
    if m:
        prog[int(m.group(2))] = m.group(1)

runs = {}
for ln in open(src):
    m = re.match(r'^COUNT (\d+) halted=(\w+) err=(\w+) tail=(.*?) rem=(\d+) steps=(\d+) gd=\[(.*?)\] ok=\[(.*?)\]$', ln)
    if m:
        c = int(m.group(1))
        tail = None if m.group(4) == 'none' else re.sub(r'^\(?some "?(.*?)"?\)?$', r'\1', m.group(4))
        gd = [int(x.replace('#64', ''), 16) for x in m.group(7).split(', ')] if m.group(7) else []
        runs[c] = dict(halted=m.group(2) == 'true', err=m.group(3) == 'true', tail=tail, rem=int(m.group(5)),
                       steps=int(m.group(6)), gd=gd,
                       ok=[x.strip() == 'true' for x in m.group(8).split(',')] if m.group(8) else [])
        continue
    m = re.match(r'^PATH (\d+) \[(.*)\]$', ln)
    if m:
        runs[int(m.group(1))]['path'] = [int(x) for x in m.group(2).split(', ')] if m.group(2) else []

COUNT_REG = {'x86': 2, 'arm': 2, 'riscv': 12}[isa]
SP = {'x86': 4, 'arm': 31, 'riscv': 2}[isa]
IN_PTR, OUT_PTR = {'x86': (6, 7), 'arm': (1, 0), 'riscv': (11, 10)}[isa]

def decode(w):
    r = w >> 56
    return dict(kind='num', value=w) if r == 0 else dict(kind='ptr', region=r % 8, offset=w & ((1 << 56) - 1))

# ---------------------------------------------------------------- def/use of one instruction
MEM_RE = r'\(\.base (\d+) \((-?\d+)\)\)'
def mems(t):
    return [(int(g), int(d)) for g, d in re.findall(MEM_RE, t)]

def m0(t):
    """the memory operand of an x86 instruction as a location: a stack/data cell, or the constants"""
    m = mems(t)
    return ('m',) + m[0] if m else ('rodata',)

def du(t):
    """(kind, uses, defs, extra): uses/defs are lists of ('r', n) / ('v', n) / ('f',) / ('m', base, disp) /
    ('vl',); kind in {'ctl','data','addr'}; extra holds abstract-address effects."""
    op = t.split()[0]
    a = t.split()
    U, D, X = [], [], {}
    if isa == 'x86':
        for g, d in mems(t):
            U.append(('r', g))           # address computation
        if op == '.mov':      U += [('r', int(a[2]))]; D += [('r', int(a[1]))]; X['copy'] = (int(a[1]), int(a[2]), 0)
        elif op == '.xchg':   U += [('r', int(a[1])), ('r', int(a[2]))]; D += [('r', int(a[1])), ('r', int(a[2]))]; X['swap'] = (int(a[1]), int(a[2]))
        elif op == '.movi':   D += [('r', int(a[1]))]
        elif op == '.lea':
            D += [('r', int(a[1]))]
            m = mems(t)
            X['copy'] = (int(a[1]), m[0][0], m[0][1]) if m else None
        elif op in ('.add', '.sub'):
            r = int(a[1]); imm = int(re.search(r'\((-?\d+)\)', t).group(1))
            U += [('r', r)]; D += [('r', r)] + ([('f',)] if op == '.sub' else []); X['shift'] = (r, imm if op == '.add' else -imm)
        elif op in ('.andi', '.shl'): U += [('r', int(a[1]))]; D += [('r', int(a[1]))]; X['fresh'] = int(a[1])
        elif op == '.dec':    U += [('r', int(a[1]))]; D += [('r', int(a[1])), ('f',)]; X['shift'] = (int(a[1]), -1)
        elif op == '.xorz':   D += [('r', int(a[1])), ('f',)]
        elif op == '.cmpi':   U += [('r', int(a[1]))]; D += [('f',)]
        elif op in ('.cmpr', '.test', '.bt'): U += [('r', int(a[1])), ('r', int(a[2]))]; D += [('f',)]
        elif op == '.cmpm':   U += [m0(t), ('r', int(a[-1]))]; D += [('f',)]
        elif op == '.cmprm':  U += [('r', int(a[1])), m0(t)]; D += [('f',)]
        elif op == '.btc':    U += [('r', int(a[1]))]; D += [('r', int(a[1]))]
        elif op in ('.alu', '.andn', '.rorx'):
            d = int(a[2]) if op == '.alu' else int(a[1])
            if op != '.rorx': U += [('r', d)] if op == '.alu' else [('r', int(a[2]))]
            g = re.search(r'\(\.reg (\d+)\)', t)
            if g and not re.search(r'\(\.base', t): U += [('r', int(g.group(1)))]
            for mm in mems(t): U += [('m',) + mm]
            D += [('r', d)]; X['fresh'] = d
        elif op == '.xorm':   U += [m0(t), ('r', int(a[-1]))]; D += [m0(t)]
        elif op == '.storeqi': D += [m0(t)]
        elif op in ('.addm', '.decm'): U += [m0(t)]; D += [m0(t), ('f',)]
        elif op == '.storeq': U += [('r', int(a[-1]))]; D += [m0(t)]; X['spill'] = (mems(t)[0], int(a[-1])) if mems(t) else None
        elif op == '.loadq':  U += [m0(t)]; D += [('r', int(a[1]))]; X['fill'] = (int(a[1]), mems(t)[0]) if mems(t) else None
        elif op in ('.jcc', '.jcct'): U += [('f',)]; X['branch'] = True
        elif op == '.push':   U += [('r', int(a[1])), ('r', SP)]; D += [('ms', -8)]; X['push'] = int(a[1])
        elif op == '.pop':    U += [('r', SP), ('ms', 0)]; D += [('r', int(a[1]))]; X['pop'] = int(a[1])
        elif op == '.call':   X['call'] = True
        elif op == '.ret':    X['ret'] = True
        elif op == '.repmovsb': U += [('r', 1), ('r', 6), ('r', 7)]; D += [('r', 1), ('r', 6), ('r', 7)]
        elif op in ('.vstore', '.vextracti128'):
            v = int(a[-1]) if op == '.vstore' else int(a[-2])
            U += [('v', v)]; D += [m0(t)]
        elif op.startswith('.v') or op == '.kmovw':
            nums = [int(x) for x in re.findall(r'(?<![\w(])(\d+)(?![\w)])', t.split('(')[0])]
            # vector op: dst = first register operand after the lane count
            regs = re.findall(r'\(\.reg (\d+)\)', t)
            hd = t.split('(')[0].split()[1:]
            if op == '.vmov':
                dst = int(hd[1]); D += [('v', dst)]
                U += [('v', int(r)) for r in regs] + [('m',) + mm for mm in mems(t)]
            elif op in ('.vperm2i128', '.vinserti128'):
                dst, src = int(hd[0]), int(hd[1]); D += [('v', dst)]; U += [('v', src)] + [('v', int(r)) for r in regs] + [('m',) + mm for mm in mems(t)]
            elif op in ('.vzeroupper', '.kmovw'):
                pass
            else:
                dst, src = int(hd[1]), int(hd[2]) if len(hd) > 2 else None
                D += [('v', dst)]; U += ([('v', src)] if src is not None else []) + [('v', int(r)) for r in regs] + [('m',) + mm for mm in mems(t)]
                if op in ('.vpternlogq', '.vpermt2q'): U += [('v', dst)]
    elif isa == 'arm':
        def lreg(s):
            m = re.match(r'\(\.(x|q|d) (\d+)\)', s)
            return ('r' if m.group(1) == 'x' else 'v', int(m.group(2)))
        lr = re.findall(r'\(\.[xqd] \d+\)', t)
        if op in ('.eorx', '.bicx'): U += [('r', int(a[2])), ('r', int(a[3]))]; D += [('r', int(a[1]))]; X['fresh'] = int(a[1])
        elif op == '.rorx':  U += [('r', int(a[2]))]; D += [('r', int(a[1]))]; X['fresh'] = int(a[1])
        elif op == '.movx':  U += [('r', int(a[2]))]; D += [('r', int(a[1]))]; X['copy'] = (int(a[1]), int(a[2]), 0)
        elif op == '.movi':  D += [('r', int(a[1]))]; X['fresh'] = int(a[1])
        elif op in ('.add', '.sub', '.subs'):
            imm = int(re.search(r'\((-?\d+)\)', t).group(1))
            U += [('r', int(a[2]))]; D += [('r', int(a[1]))] + ([('f',)] if op == '.subs' else [])
            X['copy'] = (int(a[1]), int(a[2]), imm if op == '.add' else -imm)
        elif op == '.cmp':   U += [('r', int(a[1]))]; D += [('f',)]
        elif op == '.csel':  U += [('r', int(a[2])), ('r', int(a[3])), ('f',)]; D += [('r', int(a[1]))]; X['fresh'] = int(a[1]); X['branch'] = True
        elif op in ('.ldr', '.str', '.ldp', '.stp'):
            nums = re.sub(r'\(\.[xqd] \d+\)', '', t).split()[1:]
            base = int(nums[0]); off = int(nums[1].strip('()'))
            wb = int(nums[2]) if len(nums) > 2 else 0
            addr_off = 0 if wb == 2 else off
            U += [('r', base)]
            regs = [lreg(s) for s in lr]
            cells = []
            for k, r in enumerate(regs):
                sz = 16 if r[0] == 'v' else 8
                cells.append(('m', base, addr_off + 8 * k if r[0] == 'r' else addr_off + 16 * k))
            if op in ('.ldr', '.ldp'):
                U += cells; D += regs
                X['fill_arm'] = list(zip(regs, cells))
            else:
                U += regs; D += cells
                X['spill_arm'] = list(zip(regs, cells))
            if wb: X['wb'] = (base, off)
        elif op == '.ldrlit': D += [lreg(lr[0])]
        elif op == '.cbz':   U += [('r', int(a[1]))]; X['branch'] = True
        elif op == '.bcond': U += [('f',)]; X['branch'] = True
        elif op in ('.b', '.tailcall', '.ret', '.nop', '.data'): pass
        else:   # vector ops: d a b [c]
            nums = [int(x) for x in a[1:] if x.isdigit()]
            D += [('v', nums[0])]; U += [('v', n) for n in nums[1:]]
            if op in ('.sri',): U += [('v', nums[0])]
            if op in ('.shl', '.sri', '.xar'): U = [('v', nums[1])] + ([('v', nums[2])] if op == '.xar' else []) + ([('v', nums[0])] if op == '.sri' else [])
    else:  # riscv
        nums = [int(x) for x in re.findall(r'(?<![#x\w])(-?\d+)(?![#\w])', t)]
        if op == '.op':      U += [('r', nums[1]), ('r', nums[2])]; D += [('r', nums[0])]; X['fresh'] = nums[0]
        elif op == '.opi':
            U += [('r', nums[1])]; D += [('r', nums[0])]
            if '.addi' in t:
                imm = re.search(r'\(0x([0-9a-f]+)#64\)', t)
                v = int(imm.group(1), 16) if imm else 0
                v = v - (1 << 64) if v >= 1 << 63 else v
                X['copy'] = (nums[0], nums[1], v)
            else: X['fresh'] = nums[0]
        elif op == '.li':    D += [('r', nums[0])]; X['fresh'] = nums[0]
        elif op == '.mv':    U += [('r', nums[1])]; D += [('r', nums[0])]; X['copy'] = (nums[0], nums[1], 0)
        elif op == '.not':   U += [('r', nums[1])]; D += [('r', nums[0])]; X['fresh'] = nums[0]
        elif op == '.lea':   D += [('r', nums[0])]; X['fresh'] = nums[0]
        elif op == '.ld':    U += [('r', nums[1]), ('m', nums[1], nums[2])]; D += [('r', nums[0])]; X['fill'] = (nums[0], (nums[1], nums[2]))
        elif op == '.sd':    U += [('r', nums[0]), ('r', nums[1])]; D += [('m', nums[1], nums[2])]; X['spill'] = ((nums[1], nums[2]), nums[0])
        elif op == '.br':    U += [('r', nums[0]), ('r', nums[1])]; X['branch'] = True
        elif op in ('.j', '.ret', '.nop', '.unsupported'): pass
        elif op == '.vsetvli': U += [('r', nums[1])]; D += [('r', nums[0]), ('vl',)]; X['fresh'] = nums[0]
        elif op in ('.vlseg', '.vsseg'):
            U += [('r', nums[1]), ('vl',)]
            if op == '.vlseg': D += [('v', nums[0] + k) for k in range(nums[2])]
            else: U += [('v', nums[0] + k) for k in range(nums[2])]
        elif op in ('.vmvx', '.vxorx', '.vshiftx'):
            U += [('r', nums[-1] if op != '.vshiftx' else nums[-1]), ('vl',)] + ([('v', nums[1])] if op != '.vmvx' else [])
            D += [('v', nums[0])]
        else:
            U += [('v', n) for n in nums[1:2]] + ([('v', nums[2])] if op == '.vop' else []) + [('vl',)]
            D += [('v', nums[0])]
    return U, D, X

# ---------------------------------------------------------------- taint + abstract addresses over one path
def taint_path(path):
    """returns (readers: {index: set(kinds)}, branches: set(index))"""
    sym = {r: (('reg', r), 0) for r in range(32)}   # abstract value: (root, offset)
    fresh = [0]
    def newsym():
        fresh[0] += 1
        return (('fresh', fresh[0]), 0)
    tr = {('r', COUNT_REG)}           # tainted locations
    cell_sym = {}                     # spilled abstract values
    readers = collections.defaultdict(set)
    branches = set()
    depth = 0
    def cell(base, disp):
        root, off = sym.get(base, (('reg', base), 0))
        return ('m', root, off + disp)
    for i in path:
        t = prog.get(i, '.nop')
        U, D, X = du(t)
        def norm(loc):
            if loc[0] == 'm':
                return cell(loc[1], loc[2])
            if loc[0] == 'ms':
                return cell(SP, loc[1])
            return loc
        # address operands (memory bases) and the vector length do not carry data: a count-derived
        # address or vl is recorded ('address' / 'vl') but does not taint what is loaded or computed
        addr_regs = set()
        if isa == 'x86':
            addr_regs = {('r', g) for g, _ in mems(t)}
        elif isa == 'arm' and t.split()[0] in ('.ldr', '.str', '.ldp', '.stp'):
            addr_regs = {('r', int(re.sub(r'\(\.[xqd] \d+\)', '', t).split()[1]))}
        elif isa == 'riscv' and t.split()[0] in ('.ld', '.sd', '.vlseg', '.vsseg'):
            nums_ = [int(x) for x in re.findall(r'(?<![#x\w])(-?\d+)(?![#\w])', t)]
            addr_regs = {('r', nums_[1])}
        Un = [norm(u) for u in U]
        addr_t = [u for u in Un if u in addr_regs and u in tr]
        vl_t = [u for u in Un if u == ('vl',) and u in tr]
        tainted_uses = [u for u in Un if u in tr and u not in addr_regs and u != ('vl',)]
        if addr_t: readers[i].add('address')
        if vl_t: readers[i].add('vl')
        if 'fill' in X and X['fill'] is None and 'spill' not in X:
            sym[int(t.split()[1])] = newsym()
        if tainted_uses:
            kinds = set()
            for u in tainted_uses:
                kinds.add({'r': 'gpr', 'f': 'flags', 'm': 'memory', 'v': 'vector', 'rodata': 'memory'}[u[0]])
            readers[i] |= kinds
            if X.get('branch'):
                branches.add(i)
        # vector data written under a tainted vl counts as count-dependent data
        Dn = [norm(d) for d in D]
        for d in Dn:
            if tainted_uses: tr.add(d)
            else: tr.discard(d)
        # abstract address effects
        if 'copy' in X and X['copy']:
            d, s, k = X['copy']; root, off = sym.get(s, (('reg', s), 0)); sym[d] = (root, off + k)
        if 'swap' in X:
            p, q = X['swap']; sym[p], sym[q] = sym.get(q), sym.get(p)
        if 'shift' in X:
            r, k = X['shift']; root, off = sym.get(r, (('reg', r), 0)); sym[r] = (root, off + k)
        if 'fresh' in X:
            sym[X['fresh']] = newsym()
        if X.get('spill'):
            (b, dd), s = X['spill']; cell_sym[cell(b, dd)] = sym.get(s)
        if X.get('fill'):
            r, (b, dd) = X['fill']; sym[r] = cell_sym.get(cell(b, dd)) or newsym()
        if 'spill_arm' in X:
            for (k, n), c in X['spill_arm']:
                if k == 'r': cell_sym[norm(c)] = sym.get(n)
        if 'fill_arm' in X:
            for (k, n), c in X['fill_arm']:
                if k == 'r': sym[n] = cell_sym.get(norm(c)) or newsym()
        if 'wb' in X:
            b, k = X['wb']; root, off = sym.get(b, (('reg', b), 0)); sym[b] = (root, off + k)
        if 'push' in X:
            root, off = sym[SP]; sym[SP] = (root, off - 8); cell_sym[cell(SP, 0)] = sym.get(X['push'])
        if 'pop' in X:
            v = cell_sym.get(cell(SP, 0)); root, off = sym[SP]; sym[SP] = (root, off + 8); sym[X['pop']] = v or newsym()
            tr_c = cell(SP, -8)
        if 'call' in X:
            root, off = sym[SP]; sym[SP] = (root, off - 8); depth += 1
        if 'ret' in X and depth > 0:
            root, off = sym[SP]; sym[SP] = (root, off + 8); depth -= 1
    return readers, branches

# ---------------------------------------------------------------- loop head and segments
def pieces_at(path, head):
    vis = [t for t, i in enumerate(path) if i == head]
    if not vis:
        return [tuple(path)], vis
    ps = [tuple(path[:vis[0]])]
    for a, b in zip(vis, vis[1:] + [len(path)]):
        ps.append(tuple(path[a:b]))
    return ps, vis

big = max(runs)
bp = runs[big]['path']
best = None
pos = collections.defaultdict(list)
for t, i in enumerate(bp):
    pos[i].append(t)
for i, ts in pos.items():
    if len(ts) < 2: continue
    seqs = [tuple(bp[ts[k]:ts[k + 1]]) for k in range(len(ts) - 1)]
    common = collections.Counter(seqs).most_common(1)[0]
    if common[1] < 2: continue
    # the OUTER loop: the longest piece that repeats (a batch), not the most executed one (a round)
    score = (len(common[0]), common[1])
    if best is None or score > best[0]:
        best = (score, i)
HEAD = best[1] if best else None

classes = collections.OrderedDict()
per_count = []
for c in sorted(runs):
    r = runs[c]; path = r.get('path', [])
    ps, vis = pieces_at(path, HEAD) if HEAD is not None else ([tuple(path)], [])
    pre, rest = ps[0], ps[1:]
    middle, last = rest[:-1], (rest[-1] if rest else ())
    collapsed = []
    for p in middle:
        if collapsed and collapsed[-1] == p: continue
        collapsed.append(p)
    sig = (pre, tuple(collapsed), last, r['tail'])
    cls = classes.setdefault(sig, dict(counts=[], iterations={}))
    cls['counts'].append(c); cls['iterations'][c] = len(middle)
    own = c - r['rem'] if r['tail'] else c
    ok = all(r['ok'][:own]) and not r['err'] and r['halted']
    entry = dict(count=c, steps=r['steps'], halted=r['halted'], err=r['err'], tail=r['tail'],
                 own_nodes=own, digests_ok=ok, loop_head_visits=len(vis),
                 segments=dict(entry=[0, vis[0]] if vis else [0, len(path)],
                               loop=[vis[0], vis[-1]] if vis else None,
                               exit=[vis[-1], len(path)] if vis else None))
    if r['tail']:
        pi, po = decode(r['gd'][IN_PTR]), decode(r['gd'][OUT_PTR])
        entry['handover'] = dict(remaining=r['rem'], input=pi, output=po,
                                 consistent=pi.get('kind') == 'ptr' and po.get('kind') == 'ptr' and
                                 pi['offset'] == 64 * own and po['offset'] == 32 * own and pi['region'] == 1 and po['region'] == 2)
    per_count.append(entry)

# taint over every path
readers = collections.defaultdict(set); branches = set()
for c in sorted(runs):
    rd, br = taint_path(runs[c].get('path', []))
    for i, k in rd.items(): readers[i] |= k
    branches |= br

# the batch subroutine (x86: the `.call` target up to its `.ret`); otherwise the loop body
def sub_range():
    for i in bp:
        t = prog.get(i, '')
        if t.startswith('.call'):
            return int(t.split()[1])
    return None
sub_start = sub_range()
sub_instrs = set()
if sub_start is not None:
    inside = False; depth = 0
    for i in bp:
        t = prog.get(i, '')
        if i == sub_start and not inside: inside = True; depth = 1; sub_instrs.add(i); continue
        if inside:
            sub_instrs.add(i)
            if t.startswith('.call'): depth += 1
            if t.startswith('.ret'):
                depth -= 1
                if depth == 0: break
body_instrs = set()
if HEAD is not None:
    ps, _ = pieces_at(bp, HEAD)
    if len(ps) > 2: body_instrs = set(collections.Counter(ps[1:-1]).most_common(1)[0][0])
region_instrs = sub_instrs or body_instrs
batch_readers = sorted(i for i in readers if i in region_instrs)
VECTOR_OPS = ('.v', '.eor ', '.bic ', '.eor3', '.bcax', '.rax1', '.xar', '.shl ', '.sri', '.addv', '.tbl', '.zip', '.movv', '.movi0')
def is_vector(t):
    return t.startswith(VECTOR_OPS) and not t.startswith('.vsetvli')
# data readers: a count-derived value enters a vector register (the hashed data) — address-only and vl-only
# dependencies are reported separately
batch_data_readers = sorted(i for i in batch_readers if 'vector' in readers[i] or
                            (readers[i] & {'gpr', 'memory'} and is_vector(prog.get(i, ''))))

def seg_of(i):
    if i in region_instrs: return 'batch'
    return 'frame'

res = dict(
    kernel=kernel, nodes=nodes, isa=isa, count_range=[min(runs), max(runs)],
    loop_head=dict(index=HEAD, instruction=prog.get(HEAD)) if HEAD is not None else None,
    batch_region=dict(kind='subroutine' if sub_instrs else 'loop body', start=min(region_instrs) if region_instrs else None,
                      end=max(region_instrs) if region_instrs else None, instructions=len(region_instrs)),
    classes=[dict(id=k, counts=v['counts'], iterations=v['iterations'], tail=sig[3],
                  entry_len=len(sig[0]), body_variants=[len(p) for p in sig[1]], exit_len=len(sig[2]))
             for k, (sig, v) in enumerate(classes.items())],
    per_count=per_count,
    count_dependent_branches=[dict(index=i, instruction=prog.get(i), region=seg_of(i)) for i in sorted(branches)],
    count_readers=[dict(index=i, instruction=prog.get(i), reads=sorted(readers[i]), region=seg_of(i)) for i in sorted(readers)],
    batch_count_readers=[dict(index=i, instruction=prog.get(i), reads=sorted(readers[i])) for i in batch_readers],
    batch_count_data_readers=[dict(index=i, instruction=prog.get(i), reads=sorted(readers[i])) for i in batch_data_readers],
    batch_count_address_readers=[i for i in batch_readers if 'address' in readers[i]],
    batch_count_vl_readers=len([i for i in batch_readers if 'vl' in readers[i]]),
    tail_targets=sorted(set(e['tail'] for e in per_count if e['tail'])),
    failing_counts=[e['count'] for e in per_count if not e['digests_ok']],
    inconsistent_handovers=[e['count'] for e in per_count if e.get('handover') and not e['handover']['consistent']],
)
json.dump(res, open(out, 'w'), indent=1)
print(f"{kernel}: head={HEAD} classes={len(res['classes'])} branches={len(res['count_dependent_branches'])} "
      f"batch_readers={len(batch_readers)} data={len(batch_data_readers)} addr={len(res['batch_count_address_readers'])} vl={res['batch_count_vl_readers']} failing={res['failing_counts']} "
      f"bad_handover={res['inconsistent_handovers']} tails={[x.replace('keccaktree_keccak256_', '') for x in res['tail_targets']]}")
