#!/usr/bin/env python3
"""Every-count proof of an x86 kernel: path analysis and segment plans.

    x86_all.py analyze <kernel>      -> plans/<kernel>_all.json  (frame structure, exits, source runs)

The kernel's run for any count is cut into
  * count steps (`Fr`, Asm/X86Frame.lean): instructions on registers holding numbers (the count and
    small codes), flags and pc -- the policy at the entry, the loop guard, the loop control, the exit
    dispatch;
  * generated segments (the count is data in them, or a control constant when its value is fixed):
    `P` the prologue (from the first non-count instruction after the entry policy to the loop guard),
    `B` the loop body (loop head `call 0` up to the decrement of the count),
    `X<j>` the exits (from the first non-count instruction after a dispatch with fixed register values
    to the terminal instruction: `ret` at depth 0, `tailcall`, or a taken `jcct`).
The analysis simulates the count steps (cmp/test/bt/jcc/movi/mov/sub/xorz/jmp/jcct/nop) on the kttool
paths of every count 0..64+2N (+ a few large counts) and checks that the path of every count is the
composition of these pieces.
"""
import json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
KT = os.path.join(HERE, '.lake/build/bin/kttool')

DIRS = {'x86_x1': 'X86X1', 'avx2_x2': 'Avx2X2', 'avx2_x4': 'Avx2X4', 'avx2_x5': 'Avx2X5', 'avx2_x6': 'Avx2X6',
        'avx2_x8': 'Avx2X8', 'avx2_x9': 'Avx2X9', 'avx2_x10': 'Avx2X10', 'avx512vl_x4': 'Avx512vlX4',
        'avx512_x8': 'Avx512X8', 'avx512_x9': 'Avx512X9', 'avx512vl_x4d': 'Avx512vlX4d',
        'avx512_x8d': 'Avx512X8d', 'avx512_x9d': 'Avx512X9d'}

LANES = {'x86_x1': 0, 'avx512_x8': 8, 'avx512_x9': 8, 'avx512_x8d': 8, 'avx512_x9d': 8}


def lanes_of(kernel):
    return LANES.get(kernel, 4)


def load_prog(kernel):
    d = DIRS[kernel]
    txt = open(os.path.join(HERE, f'Keccaktree/Kernels/{d}/Program.lean')).read()
    body = txt[txt.index('def prog'):]
    body = body[:body.index('\n]')]
    prog = []
    for ln in body.splitlines():
        m = re.match(r'^\s+(\..*?),?\s+-- (\d+)$', ln)
        if m:
            assert int(m.group(2)) == len(prog), (ln, len(prog))
            prog.append(m.group(1).rstrip(','))
    entry = int(re.search(r'def entry : Nat := (\d+)', txt).group(1))
    m = re.search(r'def rodata : Array \(BitVec 64\) := #\[(.*?)\]', txt, re.S)
    rodata = [int(w, 16) for w in re.findall(r'0x([0-9a-f]+)#64', m.group(1))] if m else []
    return prog, entry, rodata


def parse(ins):
    """(op, args) of an instruction text"""
    toks = re.findall(r'"[^"]*"|\(-?\d+\)|\(\.rip \d+\)|\(\.base \d+ \(-?\d+\)\)|\S+', ins)
    op = toks[0][1:]
    args = []
    for t in toks[1:]:
        if t.startswith('"'): args.append(t.strip('"'))
        elif re.match(r'^\(-?\d+\)$', t): args.append(int(t[1:-1]))
        elif re.match(r'^-?\d+$', t): args.append(int(t))
        elif t.startswith('.'): args.append(t[1:])
        else: args.append(t)
    return op, args


def cond(c, zf, cf):
    return {'e': zf, 'ne': not zf, 'b': cf, 'a': (not cf) and (not zf), 'ae': not cf, 'be': cf or zf}[c]


def fr_step(prog, rodata, pc, vals, zf, cf):
    """one count step: (new pc, vals, zf, cf, kind) or None if the instruction is not a count step;
    kind = 'tail:<name>' for a taken conditional tail call."""
    op, a = parse(prog[pc])
    v = dict(vals)
    if op == 'cmpi' and a[0] in v:
        return pc + 1, v, v[a[0]] == a[1], v[a[0]] < a[1], None
    if op == 'test' and a[0] == a[1] and a[0] in v:
        return pc + 1, v, v[a[0]] == 0, False, None
    if op == 'jcc':
        return (a[1] if cond(a[0], zf, cf) else pc + 1), v, zf, cf, None
    if op == 'jmp':
        return a[0], v, zf, cf, None
    if op == 'jcct':
        if cond(a[0], zf, cf): return pc, v, zf, cf, 'tail:' + a[1]
        return pc + 1, v, zf, cf, None
    if op in ('nop', 'vzeroupper'):
        return pc + 1, v, zf, cf, None
    if op == 'movi':
        v[a[0]] = a[1]; return pc + 1, v, zf, cf, None
    if op == 'mov' and a[1] in v:
        v[a[0]] = v[a[1]]; return pc + 1, v, zf, cf, None
    if op == 'xorz':
        v[a[0]] = 0; return pc + 1, v, True, False, None
    if op == 'sub' and a[0] in v:
        x = v[a[0]]; v[a[0]] = x - a[1]; return pc + 1, v, x == a[1], x < a[1], None
    if op == 'bt' and a[0] in v and a[1] in v:
        return pc + 1, v, zf, bool((v[a[0]] % 2 ** 64 >> (v[a[1]] % 64)) & 1), None
    if op == 'cmprm' and a[0] in v and isinstance(a[1], str) and a[1].startswith('(.rip'):
        off = int(re.search(r'\d+', a[1]).group(0))
        w = rodata[off // 8]
        return pc + 1, v, v[a[0]] == w, v[a[0]] < w, None
    return None


def paths(kernel, maxc, fuel=2000000, patch=None):
    env = dict(os.environ)
    if patch: env['KT_PATCH'] = patch
    out = subprocess.run([KT, 'paths', kernel, str(maxc), str(fuel), '0'], capture_output=True, text=True,
                         check=True, env=env).stdout
    res = {}
    for ln in out.splitlines():
        m = re.match(r'^COUNT (\d+) halted=(\w+) err=(\w+) tail=(.*?) rem=(\d+) steps=(\d+)', ln)
        if m:
            c = int(m.group(1))
            res[c] = {'halted': m.group(2) == 'true', 'err': m.group(3) == 'true',
                      'tail': None if m.group(4) == 'none' else re.sub(r'^\(some (.*)\)$', r'\1', m.group(4)),
                      'rem': int(m.group(5)), 'steps': int(m.group(6))}
        m = re.match(r'^PATH (\d+) \[(.*)\]$', ln)
        if m:
            res[int(m.group(1))]['path'] = [int(x) for x in m.group(2).split(', ')] if m.group(2) else []
    return res


def flags_at(kernel, count, step, patch=None):
    env = dict(os.environ)
    if patch: env['KT_PATCH'] = patch
    out = subprocess.run([KT, 'matches', kernel, str(count), str(step), '0'], capture_output=True, text=True,
                         check=True, env=env).stdout
    m = re.search(r'^CONTROL .* zf=(\w+) cf=(\w+) ', out, re.M)
    return m.group(1) == 'true', m.group(2) == 'true'


def analyze(kernel, patch=None):
    prog, entry, rodata = load_prog(kernel)
    pj = json.load(open(os.path.join(HERE, f'paths/{kernel}.json')))
    N = pj['nodes']
    H = pj['loop_head']['index']
    br = pj['batch_region']
    inbatch = lambda pc: br['start'] <= pc <= br['end']
    maxc = 64 + 2 * N + 2
    runs = paths(kernel, maxc, patch=patch)
    # ---- walk every count's path through the pieces
    pieces = {}           # piece name -> info
    exits = {}            # (pc, vals) -> exit info
    P0 = None; G = None; C = None
    per_count = {}
    p0_flags = set(); h_flags = set()
    for c in range(maxc + 1):
        r = runs[c]
        assert r['halted'] and not r['err'], (c, r)
        path = r['path']
        t = 0
        assert path[0] == entry
        seq = []          # pieces taken
        vals = {2: c}; zf = cf = None
        mode = 'policy'
        while True:
            pc = path[t]
            st = fr_step(prog, rodata, pc, vals, zf if zf is not None else False, cf if cf is not None else False)
            if st is not None:
                npc, vals, zf, cf, kind = st
                if kind:
                    # a taken conditional tail call: the last step of the run
                    assert t == len(path) - 1, (c, t, len(path))
                    seq.append(('ftail', mode, pc, kind[5:]))
                    break
                assert t + 1 < len(path) and path[t + 1] == npc, (c, t, pc, prog[pc], npc, path[t + 1] if t + 1 < len(path) else None)
                seq.append(('fr', mode, pc))
                t += 1
                continue
            # a non-count instruction: a segment starts here
            if mode == 'policy':
                p0_flags.add((zf, cf))
                if P0 is None: P0 = pc
                assert pc == P0, (c, pc, P0)
                # the prologue: up to the next count step
                t2 = t
                while inbatch(path[t2]) or fr_step(prog, rodata, path[t2], {2: c}, False, False) is None: t2 += 1
                if G is None: G = path[t2]
                assert path[t2] == G, (c, path[t2], G)
                seq.append(('seg', 'P', t, t2))
                vals = {2: c}   # through the prologue only the count register is known; it keeps the flags
                t = t2; mode = 'guard'; continue
            if pc == H:
                assert zf is not None and cf is not None, (c, t)
                h_flags.add((zf, cf))
                t2 = t
                while inbatch(path[t2]) or fr_step(prog, rodata, path[t2], {2: vals[2]}, False, False) is None: t2 += 1
                if C is None: C = path[t2]
                assert path[t2] == C, (c, path[t2], C)
                seq.append(('seg', 'B', t, t2))
                vals = {2: vals[2]}
                zf = True   # the batch's round counter reached zero; it does not write CF
                t = t2; mode = 'control'; continue
            # an exit: runs to the end of the path
            fl = (bool(zf), bool(cf))   # None (fresh call): clear
            key = (pc, tuple(sorted(vals.items())), fl)
            assert H not in path[t:], (c, pc)
            last = path[-1]
            op, a = parse(prog[last])
            if op == 'ret': term = ('ret', None)
            elif op == 'tailcall': term = ('tailcall', a[0])
            elif op == 'jcct': term = ('jcct', a[1])
            else: raise AssertionError((c, last, prog[last]))
            # the step index of the terminal instruction is len(path) - 1
            ex = exits.setdefault(key, {'pc': pc, 'vals': dict(vals), 'flags': fl, 'term': term, 'sources': []})
            assert ex['term'] == term, (key, ex['term'], term)
            ex['sources'].append({'count': c, 'start': t, 'end': len(path) - 1, 'tail': r['tail'], 'rem': r['rem'],
                                  'len': len(path) - 1 - t})
            seq.append(('exit', mode, key))
            break
        per_count[c] = seq
    # exit names, and each exit's source run (smallest count)
    ex_list = []
    for i, (key, ex) in enumerate(sorted(exits.items(), key=lambda kv: (kv[0][0], kv[0][1]))):
        lens = set(s['len'] for s in ex['sources'])
        assert len(lens) == 1, (key, lens)
        src = min(ex['sources'], key=lambda s: s['count'])
        assert flags_at(kernel, src['count'], src['start'], patch) == ex['flags'], (key, ex['flags'])
        ex_list.append({'name': f'X{i}', 'pc': ex['pc'], 'vals': {str(k): v for k, v in ex['vals'].items()}, 'flags': ex['flags'],
                        'term': ex['term'], 'src': src, 'len': src['len'],
                        'counts': sorted(set(s['count'] for s in ex['sources']))})
    res = {'kernel': kernel, 'dir': DIRS[kernel], 'N': N, 'entry': entry, 'P0': P0, 'G': G, 'H': H, 'C': C,
           'maxc': maxc, 'exits': ex_list, 'p0_flags': sorted(p0_flags, key=str), 'h_flags': sorted(h_flags),
           'per_count': {c: [list(map(lambda x: list(x) if isinstance(x, tuple) else x, s)) for s in seq]
                         for c, seq in per_count.items()}}
    return res


def find_plan(kernel, count, fuel=4000000, patch=None):
    env = dict(os.environ)
    if patch: env['KT_PATCH'] = patch
    out = subprocess.run(['python3', os.path.join(HERE, 'find_plan.py'), kernel, str(count), str(lanes_of(kernel)), str(fuel)],
                         capture_output=True, text=True, check=True, env=env).stdout
    return json.loads(out.splitlines()[0])


def window(plan, a, b, nodes):
    """the plan's cuts inside steps [a, b) and the rounds of `nodes` at the bounds (others: 0)"""
    cuts, rounds = plan['cuts'], plan['rounds']
    count = len(rounds[0])
    def rounds_at(step):     # rounds after `step` steps
        j = 0
        for i, t in enumerate(cuts):
            if t + 1 <= step: j = i + 1
        return rounds[j]
    keep = [t for t in cuts if a < t + 1 < b]
    rs = [rounds_at(a)] + [rounds_at(t + 1) for t in keep] + [rounds[-1] if b >= plan['end'] else rounds_at(b)]
    rs = [[r[n] if n in nodes else 0 for n in range(count)] for r in rs]
    return keep, rs


def gen_segments(kernel, patch=None):
    A = json.load(open(os.path.join(HERE, f'plans/{kernel}_all.json')))
    N, d = A['N'], A['dir']
    os.makedirs(os.path.join(HERE, 'plans'), exist_ok=True)
    runs = paths(kernel, 2 * N + 1, patch=patch)
    jobs = []
    def plan_file(name, pl):
        f = os.path.join(HERE, f'plans/{kernel}_{name}.json')
        json.dump(pl, open(f, 'w'))
        return f
    def gen(name, pl, count, env):
        f = plan_file(name, pl)
        outdir = f'Keccaktree/Kernels/{d}/Gen{name}'
        subprocess.run(['rm', '-rf', os.path.join(HERE, outdir)])
        e = dict(os.environ)
        e.update({'PLAN': f, 'OUTDIR': outdir, 'GEN': f'Gen{name}', 'NS': f'{d}.Gen{name}', 'PROG_NS': d,
                  'ISA': 'X86', 'BATCH': '1', 'SEG': '1'})
        if patch: e['KT_PATCH'] = patch
        e.update(env)
        log = os.path.join(HERE, f'plans/gen_{kernel}_{name}.log')
        with open(log, 'w') as lf:
            r = subprocess.run(['python3', os.path.join(HERE, 'gen_plan_proof.py'), kernel, d, str(count), str(lanes_of(kernel))],
                               cwd=HERE, env=e, stdout=lf, stderr=subprocess.STDOUT)
        txt = open(log).read()
        assert r.returncode == 0, (name, txt[-3000:])
        m = re.search(r'^control words per slice: (.*)$', txt, re.M)
        ctl = json.loads(m.group(1))
        nsl = len(ctl)
        print(f'  Gen{name}: {nsl} slices, ctl0={ctl[0]}', flush=True)
        return ctl[0], nsl
    info = {}
    countregs = {256 + n for ex in A['exits'] for n in map(int, ex['vals'])} | {258}
    # ---- exits
    ex_ctl = {}
    for ex in A['exits']:
        src = ex['src']; c = src['count']
        pl = find_plan(kernel, c, patch=patch) if c > 0 else {'cuts': [], 'rounds': [[]], 'end': src['end']}
        a, b = src['start'], src['end']
        if c > 0:
            r0 = [pl['rounds'][0][n] for n in range(c)]
            nodes = [n for n in range(c) if window(pl, a, b, range(c))[1][0][n] == 0 and window(pl, a, b, range(c))[1][-1][n] == 24]
        else:
            nodes = []
        if nodes:
            cuts, rounds = window(pl, a, b, nodes)
            data = {'NODES': ','.join(map(str, nodes))}
        else:
            cuts, rounds = [], [[0] * c, [0] * c]
            data = {'DATA': '0'}
        lo, hi = (4 * min(nodes), 4 * (max(nodes) + 1)) if nodes else (0, 0)
        tailterm = ex['term'][0] != 'ret'
        env = dict(data)
        env['END_CTL'] = '258,260,262,263' if tailterm else ''
        env['WRITE_OK'] = (f'fun p => p.1 == 3 || (p.1 == 2 && decide ({lo} ≤ p.2) && decide (p.2 < {hi}))'
                           if nodes else 'fun p => p.1 == 3')
        pln = {'kernel': kernel, 'count': c, 'lanes': lanes_of(kernel), 'entry': a, 'end': b, 'cuts': cuts, 'rounds': rounds}
        ctl0, nsl = gen(ex['name'], pln, c, env)
        ex_ctl[ex['name']] = ctl0
        info[ex['name']] = {'slices': nsl, 'ctl0': ctl0, 'nodes': nodes, 'count': c, 'start': a, 'end': b,
                            'base': (src['count'] - len(nodes) - (src['rem'] if src['tail'] else 0)) if nodes else None}
    # ---- body: the first iteration of a run on 2N nodes, cut at its first flag write: the prefix `Ba`
    # is proved for every flag value at the loop head (the flags are dead there), the rest `Bb` once
    prog, entry, rodata = load_prog(kernel)
    WRITERS = ('dec', 'decm', 'cmpi', 'cmpr', 'cmpm', 'cmprm', 'test', 'xorz', 'bt')
    path = runs[2 * N]['path']
    tH = path.index(A['H'])
    tC = tH + path[tH:].index(A['C'])
    tW = None
    for t in range(tH, tC):
        op, a = parse(prog[path[t]])
        assert op not in ('jcc', 'jcct'), ('flag read before the first flag write in the body', t, prog[path[t]])
        if op in WRITERS or (op == 'sub' and a[0] != 4):
            tW = t; break
    assert tW is not None
    assert all(cf is False for (zf, cf) in A['h_flags']), A['h_flags']
    pl = find_plan(kernel, 2 * N, patch=patch)
    need_x = set(v for ctl in ex_ctl.values() for v in ctl) - countregs
    b_end = set(need_x)
    for it in range(4):
        cuts, rounds = window(pl, tW + 1, tC, list(range(N)))
        env = {'NODES': ','.join(map(str, range(N))), 'END_CTL': ','.join(map(str, sorted(b_end))),
               'FORBID_CTL': '258', 'MOVES': '258:258',
               'WRITE_OK': f'fun p => p.1 == 3 || (p.1 == 2 && decide (0 ≤ p.2) && decide (p.2 < {4 * N}))'}
        pln = {'kernel': kernel, 'count': 2 * N, 'lanes': lanes_of(kernel), 'entry': tW + 1, 'end': tC, 'cuts': cuts,
               'rounds': rounds}
        bb_ctl0, nsl_b = gen('Bb', pln, 2 * N, env)
        cuts, rounds = window(pl, tH, tW + 1, list(range(N)))
        ba = {}
        for (zf, cf) in A['h_flags']:
            nm = 'Ba' + ('t' if zf else 'f')
            env = {'NODES': ','.join(map(str, range(N))), 'END_CTL': ','.join(map(str, bb_ctl0)),
                   'FORBID_CTL': '258', 'MOVES': '258:258', 'FLAGS': f'{str(zf).lower()},{str(cf).lower()}',
                   'HEAL': str(tW + 1),
                   'WRITE_OK': f'fun p => p.1 == 3 || (p.1 == 2 && decide (0 ≤ p.2) && decide (p.2 < {4 * N}))'}
            pln = {'kernel': kernel, 'count': 2 * N, 'lanes': lanes_of(kernel), 'entry': tH, 'end': tW + 1,
                   'cuts': cuts, 'rounds': rounds}
            ba[nm] = gen(nm, pln, 2 * N, env)
        ba_ctl0 = set().union(*[set(v[0]) for v in ba.values()])
        if ba_ctl0 <= b_end: break
        b_end |= ba_ctl0
    else:
        raise AssertionError('body control words do not converge')
    info['Bb'] = {'slices': nsl_b, 'ctl0': bb_ctl0, 'start': tW + 1, 'end': tC}
    for nm, (c0, nsl) in ba.items():
        info[nm] = {'slices': nsl, 'ctl0': c0, 'start': tH, 'end': tW + 1}
    # ---- prologue (from the first non-count instruction to the loop guard), in the same run; flag-free,
    # proved for every flag value it may start with
    tP = path.index(A['P0'])
    tG = tP + path[tP:].index(A['G'])
    for t in range(tP, tG):
        op, a = parse(prog[path[t]])
        assert op not in WRITERS + ('jcc', 'jcct') and not (op == 'sub' and a[0] != 4), ('prologue touches flags', prog[path[t]])
    need = sorted((ba_ctl0 | set(v for ctl in ex_ctl.values() for v in ctl)) - countregs)
    p_flags = A['p0_flags']
    if any(z is None or c is None for (z, c) in p_flags):
        # a fresh call (`LibX86.Entry`: the library normalises the control state at a call) has clear flags
        p_flags = sorted(set((False, False) if (z is None or c is None) else (z, c) for (z, c) in p_flags))
    for (zf, cf) in p_flags:
        nm = 'P' + ('t' if zf else 'f') + ('t' if cf else 'f')
        env = {'DATA': '0', 'END_CTL': ','.join(map(str, need)), 'FORBID_CTL': '258', 'MOVES': '258:258',
               'WRITE_OK': 'fun p => p.1 == 3', 'FLAGS': f'{str(zf).lower()},{str(cf).lower()}', 'HEAL': str(tG + 1)}
        pln = {'kernel': kernel, 'count': 2 * N, 'lanes': lanes_of(kernel), 'entry': tP, 'end': tG, 'cuts': [],
               'rounds': [[0] * (2 * N), [0] * (2 * N)]}
        p_ctl0, nsl = gen(nm, pln, 2 * N, env)
        info[nm] = {'slices': nsl, 'ctl0': p_ctl0, 'start': tP, 'end': tG, 'flags': [zf, cf]}
    A['segments'] = info
    json.dump(A, open(os.path.join(HERE, f'plans/{kernel}_all.json'), 'w'), indent=1, default=str)


def main():
    cmd, kernel = sys.argv[1], sys.argv[2]
    if cmd == 'analyze':
        res = analyze(kernel, os.environ.get('KT_PATCH'))
        os.makedirs(os.path.join(HERE, 'plans'), exist_ok=True)
        json.dump(res, open(os.path.join(HERE, f'plans/{kernel}_all.json'), 'w'), indent=1, default=str)
        print(f"{kernel}: N={res['N']} entry={res['entry']} P0={res['P0']} G={res['G']} H={res['H']} C={res['C']} "
              f"P0 flags={res['p0_flags']} H flags={res['h_flags']}")
        for ex in res['exits']:
            print(f"  {ex['name']}: pc={ex['pc']} vals={ex['vals']} flags={ex['flags']} term={ex['term']} len={ex['len']} "
                  f"src=count {ex['src']['count']} steps [{ex['src']['start']},{ex['src']['end']}) counts={ex['counts'][:12]}")
    elif cmd == 'gen':
        gen_segments(kernel, os.environ.get('KT_PATCH'))


if __name__ == '__main__':
    main()
