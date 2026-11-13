#!/usr/bin/env python3
"""Generate the proof files of one *plan*: a recorded kernel run on `count` nodes cut at a list of
steps, with a per-node round schedule (which nodes a slice advances by one round).  This is the
multi-batch / tail generalisation of `gen_kernel_proof.py` (whose one-batch plan is: 23 cuts, every
node advances in every slice).

    PLAN=plan.json OUTDIR=dir [GEN=GenC8] [NS=Avx2X4.C8] [PROG_NS=Avx2X4] [ISA=X86] [ISA_EXPR=X86.isa]
    gen_plan_proof.py <kernel> <Namespace-dir> <count> <lanes>

plan.json: {"entry": t0, "end": tE, "cuts": [t1, ...], "rounds": [[r_n ...] ...]} — `rounds[c]` is
the round of every node at bound `c` (bound 0 = entry, bound K = end); a slice may advance any set
of nodes by exactly one round (all to the same round).  Nodes at round 24 at the end are the ones
the kernel finished itself; if the final symbolic state carries a tail call, the hand-over
registers (count, input, output pointers) are reported as closed constants.

Environment as in gen_kernel_proof.py: SLICES, ONLY_NODE, BATCH=1 (also Batch/Final).
"""
import json, os, re, subprocess, sys

KT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '.lake/build/bin/kttool')

ISA = os.environ.get('ISA', 'X86')
ISA_EXPR = os.environ.get('ISA_EXPR', ISA + '.isa')
ISA_HOM = {'X86': 'Trace', 'Arm': 'ArmHom', 'Riscv': 'RiscvHom'}[ISA]
# segment mode: the relocation and footprint instances of the instruction set (Lean expressions) and the
# module providing the footprint (imported by the slice files)
_VLMAX = re.search(r'\d+', ISA_EXPR).group(0) if ISA == 'Riscv' else ''
RELOC_EXPR = os.environ.get('RELOC_EXPR', {'X86': 'X86.isaReloc', 'Arm': 'Arm.isaReloc', 'Riscv': f'(Riscv.isaReloc {_VLMAX})'}[ISA])
FOOT_EXPR = os.environ.get('FOOT_EXPR', {'X86': 'X86.isaFoot', 'Arm': 'Arm.isaFoot', 'Riscv': f'(Riscv.isaFoot {_VLMAX})'}[ISA])
SEG_IMPORT = {'X86': 'Keccaktree.Asm.Iter', 'Arm': 'Keccaktree.Asm.ArmFootprint', 'Riscv': 'Keccaktree.Asm.RiscvFoot'}[ISA]
PROG_NS = os.environ.get('PROG_NS')     # the kernel's Program namespace (dir name) when ≠ NS
GEN = os.environ.get('GEN', 'Gen')      # the generated module directory under the kernel's directory
CTLS = {}
PLAN = None
K = 0                                   # number of slices


def run(*args, ctl=()):
    env = dict(os.environ)
    env['KT_CTL'] = ','.join(str(v) for v in ctl)
    return subprocess.run([KT] + [str(a) for a in args], capture_output=True, text=True, check=True, env=env).stdout


# round-constant matches at general registers and stack cells are dropped for the kernels that read the round
# constants from memory only (AVX2, x86_x1); the AVX-512 kernels keep theirs.  DROP_RC=0/1 overrides.
DROP_RC = None
RC_BV = False
# per-kernel forms introduced after kernels were proved (their generated files stay as they were):
# the recursion bound for Inv defs counting the constant hypotheses too, and seg_frame's `rw` of `segAt`
# (the `show … .mem` form made Lean evaluate a slice: avx2_x6).  INV_DEPTH_ALL=0/1, SEGFRAME_RW=0/1 override.
INV_DEPTH_ALL = False
SEGFRAME_RW = False
# the recursion bound for a slice's step theorem when its output tuple (lanes + carried constants) exceeds 240
# (avx2_x9/x10 GenX3 slice 0: 252, past the default depth).  STEP_DEPTH_ALL=0/1 overrides.
STEP_DEPTH_ALL = False


def matches(kernel, count, steps, lanes, rnd_of, region_filter=None, regs_only=False):
    """the labelled locations after `steps` steps: node `n` is expected at round `rnd_of[n]`"""
    out = run('matches', kernel, count, steps, lanes)
    alloc = []
    for ln in out.splitlines():
        m = re.match(r'^\(\.(reg|mem) (\d+) \(?(-?\d+)\)?\) (\d+) (\d+) (\d+) (\d+)$', ln)
        mg = re.match(r'^\(\.gd (\d+)\) (\d+) (\d+) (\d+) (\d+)$', ln)
        if mg:
            if region_filter is not None: continue
            n_, node, round_, kind, rot = mg.groups()
            if int(round_) != rnd_of[int(node)]: continue
            if DROP_RC and 75 <= int(kind) < 99:
                # the AVX2 kernels and x86_x1 apply the round constants from memory (`vpxor`/`xor` with [RCP + rc]),
                # never from a general register: a "round constant" there is a coincidence (a pointer `1 << 56`,
                # a count 8 = RC0 rol 3)
                continue
            alloc.append((int(node), int(kind), f'(gdVar {n_})', int(rot), ln)); continue
        if not m: continue
        kind_loc, a, b, node, round_, kind, rot = m.groups()
        if int(round_) != rnd_of[int(node)]: continue
        if DROP_RC and kind_loc == 'mem' and int(a) == 3 and 75 <= int(kind) < 99:
            # likewise a stack cell equal to a rotated round constant (the spilled count 8 = RC0 rol 3)
            continue
        if kind_loc == 'reg':
            if region_filter is not None: continue
            var = f'(regVar {a} {b})'
        else:
            if region_filter is not None and int(a) != region_filter: continue
            if regs_only: continue
            var = mem_var(int(a), int(b))
        alloc.append((int(node), int(kind), var, int(rot), ln))
    # a round constant (kinds 75..98) is reported for node 0 only but is a hypothesis every node may use;
    # it belongs to the nodes at that round
    rc = [(kind, var, rot, ln) for (node, kind, var, rot, ln) in alloc if 75 <= kind < 99]
    alloc = [h for h in alloc if not (75 <= h[1] < 99)]
    for (kind, var, rot, ln) in rc:
        for n in range(count):
            if rnd_of[n] == kind - 75 or True:
                alloc.append((n, kind, var, rot, ln))
    return alloc


def control_at(kernel, count, steps, lanes):
    out = run('matches', kernel, count, steps, lanes)
    m = re.search(r'^CONTROL g=\[(.*?)\] gd=\[.*?\] k=\[(.*?)\] zf=(\w+) cf=(\w+) nf=(\w+) vf=(\w+) vl=(\d+) pc=(\d+) depth=(\d+)(?: halted=(\w+) tail=(\S*))?', out, re.M)
    g = re.sub(r'⟨(\d+), \((-?\d+)\)⟩', r'(Addr.mk \1 (\2))', m.group(1))
    halted = m.group(10) or 'false'
    tail = (m.group(11) or '').strip('"')
    zf, cf = m.group(3), m.group(4)
    if FLAGS and steps < HEAL:
        zf, cf = FLAGS
    return g, m.group(2), zf, cf, m.group(5), m.group(6), int(m.group(7)), int(m.group(8)), int(m.group(9)), halted, tail


def slice_lits(kernel, count, a, b, ctl=(), cells=()):
    env_extra = {'KT_CELLS': ','.join(str(v) for v in cells)}
    env = dict(os.environ); env['KT_CTL'] = ','.join(str(v) for v in ctl); env.update(env_extra)
    out = subprocess.run([KT, 'slice', kernel, str(count), str(a), str(b)], capture_output=True, text=True, check=True, env=env).stdout
    ctl = [int(x) for x in re.findall(r'\d+', re.search(r'^CTL (.*)$', out, re.M).group(1))]
    sc = re.search(r'^SC (.*)$', out, re.M).group(1)
    if K1 is not None and a == PLAN['entry']:
        # mask register k1 at the segment's start (written by the batch's `kmovw k1` before any masked move)
        sc, n = re.subn(r'#v\[(\d+), (\d+), ((?:\d+, )*\d+)\] (true|false) (true|false) ', lambda m: f'#v[{m.group(1)}, {K1}, {m.group(3)}] {m.group(4)} {m.group(5)} ', sc, count=1)
        assert n == 1, sc[-300:]
    if FLAGS and a < HEAL:
        # the segment is proved for these flags at its start (they are dead until the first flag write, HEAL)
        sc, n = re.subn(r'(#v\[[0-9, ]*\]) (true|false) (true|false) ', lambda m: f'{m.group(1)} {FLAGS[0]} {FLAGS[1]} ', sc, count=1)
        assert n == 1, sc[-300:]
    idx = re.search(r'^IDX (.*)$', out, re.M).group(1)
    trees = {}
    for m in re.finditer(r'^VAR (\d+) (.*)$', out, re.M):
        trees[int(m.group(1))] = m.group(2)
    err = re.search(r'^ERR (\w+)', out, re.M).group(1)
    assert err == 'false', 'symbolic slice failed'
    return ctl, sc, idx, trees


def find_ctls(kernel, count, bounds):
    need = {}
    for c in range(K):
        need[c] = set(slice_lits(kernel, count, bounds[c], bounds[c + 1])[0])
    if not SEG:
        cells = set(v for c in need for v in need[c] if v >= 288)
        for c in range(K):
            need[c] |= cells
    # segment mode: the control words the next segment needs at the end bound
    need[K] = set(END_CTL)
    # words forced to be control words at the start (closed constants the lanes need, e.g. RVV's `1 << 63`)
    need[0] |= set(START_CTL)
    for v in FORBID_CTL:
        for c in range(K):
            assert v not in need[c], f'forbidden control word {v} needed by slice {c}'
    changed = True
    while changed:
        changed = False
        for c in range(K, 0, -1):
            trees = slice_lits(kernel, count, bounds[c - 1], bounds[c], ctl=sorted(need[c - 1]))[3]
            for v in sorted(need[c]):
                t = trees.get(v, f'(.var {v})')
                # every variable the control word's value depends on must be a control word of the slice
                # before (a bare variable, or e.g. a counter cell updated in place: `.add (.var v) (.const 16)`)
                for x in re.findall(r'\(\.var (\d+)\)', t):
                    if int(x) not in need[c - 1]:
                        need[c - 1].add(int(x)); changed = True
        # a loop body: the end cut is the start cut of the next iteration
        if LOOP and not need[0] <= need[K]:
            need[K] |= need[0]; changed = True
    for v in FORBID_CTL:
        for c in range(K + 1):
            assert v not in need[c], f'forbidden control word {v} needed at cut {c}'
    return {c: sorted(need[c]) for c in range(K + 1)}


def mem_var(region, q):
    if region == 1 and q >= 0: return f'(memVar rInput (Int.ofNat (8 * {q // 8} + {q % 8})))'
    if region == 2 and q >= 0: return f'(memVar rOutput (Int.ofNat (4 * {q // 4} + {q % 4})))'
    return f'(memVar {region} ({q}))'


def var_id(v):
    m = re.match(r'\(regVar (\d+) (\d+)\)', v)
    if m: return 8 * int(m.group(1)) + int(m.group(2))
    m = re.match(r'\(gdVar (\d+)\)', v)
    if m: return 256 + int(m.group(1))
    m = re.match(r'\(memVar rInput \(Int.ofNat \(8 \* (\d+) \+ (\d+)\)\)\)', v)
    if m: r, q = 1, 8 * int(m.group(1)) + int(m.group(2))
    else:
        m = re.match(r'\(memVar rOutput \(Int.ofNat \(4 \* (\d+) \+ (\d+)\)\)\)', v)
        if m: r, q = 2, 4 * int(m.group(1)) + int(m.group(2))
        else:
            m = re.match(r'\(memVar (\d+) \(?(-?\d+)\)?\)', v)
            r, q = int(m.group(1)), int(m.group(2))
    enc = 2 * q if q >= 0 else 2 * (-q) - 1
    return 288 + 8 * enc + r


# unfolding `specQuantity`: after the restructuring of Cut.lean (`specQuantity` dispatches to `specQuantity0`
# and `specQuantityCol`), the dispatcher's arithmetic must be reduced too; detected from the source
_CUT = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'Keccaktree', 'Asm', 'Cut.lean')).read()
SPEC_UNFOLD = ('specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv, '
               'Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul') if 'def specQuantity0' in _CUT else 'specQuantity'
SIMP_SPEC = SPEC_UNFOLD + ', ' + ', '.join(f'round_lane_{k}' for k in range(25)) + ', Spec.RC'


def const_val(k):
    return '1#64' if k == 8 else ('0x8000000000000000#64' if k == 16 else '0#64')


def const_hyps(nodes):
    """the constant lanes 8..24 of the absorbed state of the nodes still at round 0"""
    return [(n, k, f'L (A {n}) {k} = {const_val(k)}') for n in nodes for k in range(8, 25)]


def quantity(node, kind):
    return f'(Spec.RC {kind - 75})' if 75 <= kind < 99 else f'(specQuantity (A {node}) {kind})'


def out_quantity(node, round_in, kind):
    if 75 <= kind < 99: return f'(Spec.RC {kind - 75})'
    if round_in is None: return f'(specQuantity (A {node}) {kind})'
    return f'(specQuantity (Spec.round {round_in} (A {node})) {kind})'


def inv_conj(alloc):
    return ' ∧\n  '.join(f'env {var} = {quantity(node, kind)}.rotateLeft {rot}' for node, kind, var, rot, _ in alloc) or 'True'


def header(ns, prog=True):
    return f'''namespace Keccaktree.Kernels.{ns}
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak
{f'open Keccaktree.Kernels.{PROG_NS} (prog rodata entry)' if PROG_NS and prog else ''}
'''


def gen_invs(ns, nsdir, count, allocs, chyps, outdir):
    with open(os.path.join(outdir, 'Invs.lean'), 'w') as f:
        f.write(f'''import Keccaktree.Asm.Cut
import Keccaktree.Proof
/-! GENERATED by lean/gen_plan_proof.py; do not edit.  The invariants at the cuts of the plan: what the
locations hold, as quantities of the nodes' sponge states `A n` (node `n` at round `rnd c n` at cut `c`). -/
''' + header(ns, prog=False) + f'''
/-- The round of node `n` at bound `c`. -/
def rndAt : Nat → Nat → Nat
''' + ''.join(f'  | {c}, {n} => {PLAN["rounds"][c][n]}\n' for c in range(K + 1) for n in range(count)) + f'''  | _, _ => 0

/-- Does slice `c` advance node `n` (by one round)? -/
def act (c n : Nat) : Bool := rndAt (c + 1) n == rndAt c n + 1

/-- The states after slice `c`. -/
def sched (A : Fin {count} → Spec.State) (c : Nat) : Fin {count} → Spec.State :=
  fun n => if act c n.val then Spec.round (rndSlice c) (A n) else A n
where rndSlice (c : Nat) : Nat := ''' + f'''match c with
''' + ''.join(f'    | {c} => {slice_round(c)}\n' for c in range(K)) + '''    | _ => 0

''')
        for c in range(K + 1):
            doc = f'The locations at bound {c}' if c < K else 'The output locations at the end of the plan'
            if len(allocs[c]) > 200 or (INV_DEPTH_ALL and len(allocs[c]) + len(chyps[c]) > 250):
                f.write('set_option maxRecDepth 100000 in\n')
            f.write(f'/-- {doc} (for states `A n` of the nodes). -/\n')
            conjs = [f'env {var} = {quantity(node, kind)}.rotateLeft {rot}' for node, kind, var, rot, _ in allocs[c]] + [h for (_, _, h) in chyps[c]]
            f.write(f'def Inv{c} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) : Prop :=\n  ' + (' ∧\n  '.join(conjs) or 'True') + '\n\n')
            if SEG:
                ids = [var_id(v) for (_, _, v, _, _) in allocs[c]]
                f.write(f'/-- The locations `Inv{c}` reads. -/\ndef locs{c} : List Nat := {ids}\n\n')
                n_all = len(allocs[c]) + len(chyps[c])
                names = [f'h{i}' for i in range(len(allocs[c]))] + [f'k{i}' for i in range(len(chyps[c]))]
                if len(ids) > 100:
                    f.write('set_option maxRecDepth 100000 in\n')
                f.write(f'theorem Inv{c}_congr (f g : Nat → BitVec 64) (A : Fin {count} → Spec.State) (h : Inv{c} f A)\n'
                        f'    (hg : ∀ v ∈ locs{c}, g v = f v) : Inv{c} g A := by\n')
                if n_all == 0:
                    f.write('  trivial\n\n')
                else:
                    f.write(f'  obtain ⟨{", ".join(names)}⟩ := h\n')
                    parts = [f'(hg _ (by decide)).trans h{i}' for i in range(len(allocs[c]))] + [f'k{i}' for i in range(len(chyps[c]))]
                    f.write('  exact ⟨' + ', '.join(parts) + '⟩\n\n')
        f.write(f'end Keccaktree.Kernels.{ns}\n')


def slice_round(c):
    """the round applied by slice c (None if it advances no node)"""
    rs = set(PLAN['rounds'][c][n] for n in range(len(PLAN['rounds'][c])) if PLAN['rounds'][c + 1][n] == PLAN['rounds'][c][n] + 1)
    assert len(rs) <= 1, f'slice {c} applies several rounds: {rs}'
    return rs.pop() if rs else 0


def gen_slice(kernel, ns, nsdir, count, lanes, c, a, b, alloc_in, alloc_out, out, only_node, chyps_in, chyps_out):
    rin, rout = PLAN['rounds'][c], PLAN['rounds'][c + 1]
    active = {n for n in range(count) if rout[n] == rin[n] + 1}
    for n in range(count):
        assert rout[n] in (rin[n], rin[n] + 1), f'slice {c}: node {n} jumps {rin[n]} -> {rout[n]}'
    r_slice = slice_round(c)
    g, k, zf, cf, nf, vf, vl, pc, depth, halted, tail = control_at(kernel, count, b, lanes)
    last = c == K - 1
    cells_needed = [var_id(v) for (_, _, v, _, _) in alloc_out if var_id(v) >= 288]
    ctl, sc, idx, trees = slice_lits(kernel, count, a, b, ctl=CTLS[c], cells=cells_needed)
    assert sorted(ctl) == CTLS[c], (c, sorted(ctl), CTLS[c])
    ctl = CTLS[c]
    ctl_next = CTLS.get(c + 1, [])
    out.write(f'''import Keccaktree.Asm.Compose
import Keccaktree.Asm.{ISA_HOM}
import Keccaktree.Asm.RoundLanes
import Keccaktree.Proof
import Keccaktree.Kernels.{PROG_NS or nsdir}.Program
import Keccaktree.Kernels.{nsdir}.{GEN}.Invs
{"import " + SEG_IMPORT if SEG else ""}
/-! GENERATED by lean/gen_plan_proof.py; do not edit.  Slice {c} of the plan: steps [{a}, {b}),
round {r_slice} of nodes {sorted(active)}. -/
''' + header(ns) + f'''
/-- The control words (cut variables kept constant). -/
def ctl{c} : List Nat := {ctl}

/-- The control state at the cut (closed). -/
def sc{c} : State (BitVec 64) := {sc}

def cut{c} : State E := cutOf ctl{c} sc{c}

def idx{c} : List Nat := {idx}

def slice{c} : List {ISA}.Instr := idx{c}.map (prog.getD · .nop)

/-- The symbolic state after the slice. -/
def result{c} : State E := {ISA_EXPR}.execTrace rodata slice{c} cut{c}

''')
    tail_lean = f'some "{tail}"' if tail else 'none'
    out.write(f'''set_option maxRecDepth 100000 in
/-- The control part after the slice (kernel-computed): what the next cut starts from. -/
theorem ctrl{c} : result{c}.g = #v[{g}] ∧ result{c}.k = #v[{k}] ∧ result{c}.zf = {zf} ∧ result{c}.cf = {cf} ∧
    result{c}.nf = {nf} ∧ result{c}.vf = {vf} ∧ result{c}.vl = {vl} ∧
    result{c}.pc = {pc} ∧ result{c}.depth = {depth} ∧ result{c}.err = false ∧ result{c}.halted = {halted if last else 'false'} ∧
    result{c}.tail = {tail_lean if last else 'none'} := by decide +kernel

set_option maxRecDepth 100000 in
/-- The symbolic run follows the recorded instruction path (kernel-computed). -/
theorem path{c} : {ISA_EXPR}.pathOk rodata prog idx{c} cut{c} = true := by decide +kernel

''')
    if ctl_next:
        for v in ctl_next:
            assert '.var' not in trees[v], f'control word {v} is not constant after slice {c}: {trees[v][:80]}'
        out.write('set_option maxRecDepth 100000 in\nset_option synthInstance.maxHeartbeats 2000000 in\n')
        out.write('/-- The control words of the next cut are constants after the slice. -/\n')
        out.write(f'theorem ctlv{c} : ' + ' ∧\n    '.join(f'readVar result{c} {v} = {trees[v]}' for v in ctl_next) + ' := by decide +kernel\n\n')
        for j, v in enumerate(ctl_next):
            proj = 'ctlv' + str(c) + ''.join('.2' for _ in range(j)) + ('.1' if j + 1 < len(ctl_next) else '')
            out.write(f'theorem ctlv{c}_{j} : readVar result{c} {v} = {trees[v]} := {proj}\n\n')
    if last and tail:
        # the hand-over registers (count, input, output) are closed constants after the slice
        hv = {}
        for n_ in HANDOVER_REGS:
            t = trees[256 + n_]
            assert '.var' not in t, f'hand-over register {n_} is not constant: {t[:80]}'
            hv[n_] = t
        out.write('set_option maxRecDepth 100000 in\n/-- The hand-over registers after the tail-calling slice (closed). -/\n')
        out.write(f'theorem handv{c} : ' + ' ∧\n    '.join(f'readVar result{c} (gdVar {n_}) = {hv[n_]}' for n_ in HANDOVER_REGS) + ' := by decide +kernel\n\n')
    outs = [(node, kind, var, rot, ln) for (node, kind, var, rot, ln) in alloc_out if only_node < 0 or node == only_node]
    vids = [var_id(v) for (_, _, v, _, _) in outs]
    CHUNK = 16
    out.write('-- The symbolic lanes at the output locations (kernel evaluations of the slice).\n')
    missing = [v for (_, _, v, _, _) in outs if var_id(v) not in trees]
    if missing:
        raise SystemExit(f'slice {c}: output locations without a symbolic value: {missing[:5]}')
    for p in range(0, len(outs), CHUNK):
        part = outs[p:p + CHUNK]
        out.write('set_option maxRecDepth 100000 in\nset_option synthInstance.maxHeartbeats 2000000 in\n')
        out.write(f'theorem outs{c}_c{p // CHUNK} : ' + ' ∧\n    '.join(f'readVar result{c} {v} = {trees[var_id(v)]}' for (_, _, v, _, _) in part) + ' := by decide +kernel\n\n')
        for j, (node, kind, var, rot, ln) in enumerate(part):
            proj = f'outs{c}_c{p // CHUNK}' + ''.join('.2' for _ in range(j)) + ('.1' if j + 1 < len(part) else '')
            out.write(f'theorem out{c}_{p + j} : readVar result{c} {var} = {trees[vids[p + j]]} := {proj}\n\n')
    hyp_all = [(i, h) for i, h in enumerate(alloc_in)]
    hyp_by = {(node, var_id(var)): (i, h) for i, h in hyp_all for (node, kind, var, rot, _) in [h]}
    chyp_by = {(n_, k_): i for i, (n_, k_, _) in enumerate(chyps_in)}
    groups = {}
    inst = []
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        tree = trees[vids[j]]
        used = []
        for x in re.findall(r'\(\.var (\d+)\)', tree):
            if int(x) not in used: used.append(int(x))
        pos = {v: i for i, v in enumerate(used)}
        sig = re.sub(r'\(\.var (\d+)\)', lambda m: '(.var v%d)' % pos[int(m.group(1))], tree)
        hk, hidx = [], []
        for v in used:
            if (node, v) in hyp_by:
                i, (_, k_, _, r_, _) = hyp_by[(node, v)]
                hk.append((k_, r_)); hidx.append(i)
            else:
                hk.append(None); hidx.append(None)
        ck = tuple(sorted(k_ for (n_, k_) in chyp_by if n_ == node)) if node in active else ()
        if any(x is None for x in hidx):
            print(f'slice {c}: WARNING output {var} (node {node}, kind {kind}) depends on unlabelled inputs '
                  f'{[v for v, x in zip(used, hidx) if x is None]}', file=sys.stderr)
        rin_node = r_slice if node in active else None
        key = (sig, tuple(hk), ck, kind, rot, rin_node)
        if key not in groups:
            groups[key] = (len(groups), used, hidx)
        g_ = groups[key][0]
        inst.append((g_, node, used, hidx, [chyp_by[(node, k_)] for k_ in ck], rin_node))
    for key, (g_, used0, hidx0) in groups.items():
        sig, hk, ck, kind, rot, rin_node = key
        params = ' '.join(f'v{i}' for i in range(len(used0)))
        params = f'({params} : Nat) ' if used0 else ''
        hyps = ' '.join(f'(h{i} : env v{i} = {quantity("n", k_)}.rotateLeft {r_})' for i, kr in enumerate(hk) if kr for (k_, r_) in [kr])
        hyps += ''.join(f' (c{k_} : L (A n) {k_} = {const_val(k_)})' for k_ in ck)
        hnames = ' '.join(f'h{i}' for i, kr in enumerate(hk) if kr)
        at_h = f' at {hnames}' if hnames else ''
        out.write(f'''set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- Lane kind {kind} (rotated by {rot}) {"of round " + str(rin_node) if rin_node is not None else "(carried)"}, for any node `n` whose quantities are at `v*`. -/
theorem lane{c}_g{g_} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) (n : Fin {count}) {params}{hyps} :
    E.eval env ({sig}) = {out_quantity('n', rin_node, kind)}.rotateLeft {rot} := by
''' + (f'''  simp only [E.eval{", " + ", ".join(hnames.split()) if hnames else ""}]
  all_goals first | decide +kernel | (simp only [Spec.RC] at *; bv_decide)

''' if 75 <= kind < 99 and RC_BV else f'''  simp only [E.eval]
  all_goals decide +kernel

''' if 75 <= kind < 99 else f'''  simp +decide only [E.eval, ternlogW, List.range, List.range.loop, List.foldl, ↓reduceIte]
  {"simp only [" + SPEC_UNFOLD + ", Spec.RC]" + at_h if hnames else "skip"}
  simp only [{SIMP_SPEC}]
  bv_decide (config := {{ timeout := 1800 }})

'''))
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        g_, node, used, hidx, cidx, rin_node = inst[j]
        hyps = ' '.join(f'(h{i} : env {var_} = {quantity(node_, kind_)}.rotateLeft {rot_})'
                        for i in hidx if i is not None for (node_, kind_, var_, rot_, _) in [alloc_in[i]])
        hyps += ''.join(f' (c{i} : {chyps_in[i][2]})' for i in cidx)
        args = ' '.join(f'({alloc_in[hyp_by[(node, v)][0]][2]})' if (node, v) in hyp_by else str(v) for v in used)
        hargs = ' '.join(f'h{i}' for i in hidx if i is not None) + ''.join(f' c{i}' for i in cidx)
        out.write(f'''/-- {ln} -/
theorem lane{c}_{j} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) {hyps} :
    E.eval env (readVar result{c} {var}) = {out_quantity(node, rin_node, kind)}.rotateLeft {rot} := by
  rw [out{c}_{j}]
  exact lane{c}_g{g_} env A ⟨{node}, by decide⟩ {args} {hargs}

''')
    print(f'slice {c}: {len(outs)} outputs, {len(groups)} generic lemmas, round {r_slice} on {sorted(active)}', file=sys.stderr)
    if len(outs) > 200 or len(alloc_in) > 200 or (STEP_DEPTH_ALL and len(outs) + len(chyps_out) > 240):
        out.write('set_option maxRecDepth 100000 in\n')
    out.write(f'/-- Slice {c}: the invariant at its start gives the invariant at its end, for the advanced states. -/\n')
    out.write(f'theorem step{c} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) (h : Inv{c} env A) :\n')
    out.write(f'    Inv{c + 1} (fun i => E.eval env (readVar result{c} i)) (sched A {c}) := by\n')
    names = ' '.join(f'h{i}' for i, _ in hyp_all) + ''.join(f' c{i}' for i in range(len(chyps_in)))
    names = names.strip()
    out.write(f'  obtain ⟨{", ".join(names.split())}⟩ := h\n' if names else '  clear h\n')
    parts = []
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        g_, node, used, hidx, cidx, rin_node = inst[j]
        parts.append(f'lane{c}_{j} env A ' + ' '.join(f'h{i}' for i in hidx if i is not None) + ''.join(f' c{i}' for i in cidx))
    # the constant lanes of the nodes still at round 0 after the slice are carried
    for (n_, k_, _) in chyps_out:
        parts.append(f'c{chyp_by[(n_, k_)]}')
    out.write(('  exact ⟨' + ', '.join(parts) + '⟩\n\n') if parts else '  trivial\n\n')
    if SEG:
        out.write(f'''set_option maxRecDepth 100000 in
/-- The addresses the slice decodes stay representable after a relocation within the bound. -/
theorem dec{c} : ({RELOC_EXPR}.traceDecodes rodata slice{c} cut{c}).all (E.addrsBelow ({BOUND})) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The cells the slice stores to. -/
theorem writes{c} : ({FOOT_EXPR}.traceWrites rodata slice{c} cut{c}).all ({WRITE_OK}) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The output locations' lanes carry no pointer. -/
theorem noptr{c} : locs{c + 1}.all (fun v => (readVar result{c} v).noPtr) = true := by decide +kernel

''')
        mv = [(MOVE_PATHS[m][c + 1], MOVE_PATHS[m][c]) for m in range(len(MOVES))]
        if COUNT_LOCS and (258, 258) in MOVES:
            mv = [(COUNT_LOCS[c + 1], COUNT_LOCS[c]) if (d, s_) == (258, 258) else p_
                  for p_, (d, s_) in zip(mv, MOVES)]
        out.write('set_option maxRecDepth 100000 in\n/-- The moved/kept words of the slice. -/\n')
        out.write(f'theorem moves{c} : ({mv} : List (Nat × Nat)).all (fun p => readVar result{c} p.1 == .var p.2) = true := by decide +kernel\n\n')
    out.write(f'end Keccaktree.Kernels.{ns}\n')


HANDOVER_REGS = {'Arm': [2, 1, 0]}.get(ISA, [2, 6, 7])   # count, input, output (x86 SysV: rdx, rsi, rdi; AAPCS64: x2, x1, x0)


def gen_batch_final(ns, nsdir, count, outdir, tail):
    rounds_end = PLAN['rounds'][K]
    done = [n for n in range(count) if rounds_end[n] == 24]
    with open(os.path.join(outdir, 'Batch.lean'), 'w') as f:
        f.write(''.join(f'import Keccaktree.Kernels.{nsdir}.{GEN}.Slice{c}\n' for c in range(K)))
        f.write(f'''/-! GENERATED: the slices chained: from the input invariant to the output locations. -/
''' + header(ns) + f'''
/-- The cut environments along the plan, from the entry environment. -/
def envAt (env0 : Nat → BitVec 64) : Nat → (Nat → BitVec 64)
  | 0 => env0
''' + ''.join(f'  | {c + 1} => fun i => E.eval (envAt env0 {c}) (readVar result{c} i)\n' for c in range(K)) +
            f'''  | _ => env0

/-- The nodes' states along the plan. -/
def AAt (A : Fin {count} → Spec.State) : Nat → (Fin {count} → Spec.State)
  | 0 => A
  | c + 1 => sched (AAt A c) c

/-! `envAt` has literal arms (compiled by well-founded recursion, not reducible): its equations. -/
theorem envAt_0 (env0 : Nat → BitVec 64) : envAt env0 0 = env0 := by simp only [envAt]
''' + ''.join(f'''theorem envAt_{c + 1} (env0 : Nat → BitVec 64) : envAt env0 {c + 1} = fun i => E.eval (envAt env0 {c}) (readVar result{c} i) := by
  simp only [envAt]
''' for c in range(K)) + f'''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The plan computes the rounds of its schedule on every node.** -/
theorem chain (env0 : Nat → BitVec 64) (A : Fin {count} → Spec.State) (h0 : Inv0 env0 A) :
    Inv{K} (envAt env0 {K}) (AAt A {K}) := by
''' + f'''  have h0' : Inv0 (envAt env0 0) (AAt A 0) := by rw [envAt_0]; exact h0
''' + ''.join(f"  have h{c + 1} : Inv{c + 1} (envAt env0 {c + 1}) (AAt A {c + 1}) := by rw [envAt_{c + 1}]; exact step{c} (envAt env0 {c}) (AAt A {c}) h{c}{chr(39) if c == 0 else ''}\n" for c in range(K)) + f'''  exact h{K}

''')
        # the per-node states along the plan, one bound at a time (unfolding `AAt A K` at once
        # duplicates `AAt A c n` in both branches of every `sched` step: exponential)
        f.write(f'''theorem sched_act (A : Fin {count} → Spec.State) (c : Nat) (n : Fin {count}) (h : act c n.val = true) :
    sched A c n = Spec.round (sched.rndSlice c) (A n) := by
  simp only [sched, h, ↓reduceIte]

theorem sched_nact (A : Fin {count} → Spec.State) (c : Nat) (n : Fin {count}) (h : act c n.val = false) :
    sched A c n = A n := by
  simp only [sched, h, Bool.false_eq_true, ↓reduceIte]

theorem rounds_succ (r : Nat) (X : Spec.State) : Spec.round r (Spec.rounds r X) = Spec.rounds (r + 1) X := by
  simp only [Spec.rounds, Spec.memo_eq]

''')
        nodes_ = [int(x) for x in os.environ.get('NODES', '').split(',') if x] or list(range(count))
        for n in range(count):
            r0n = PLAN['rounds'][0][n]
            if r0n != 0 and (ISA != 'X86' or n not in nodes_):
                # (AArch64 / RISC-V: no mid-way `aat` lemma, as their proved segments were generated)
                continue
            if r0n == 0:
                f.write(f'''set_option maxRecDepth 100000 in
theorem aat_{n} (A : Fin {count} → Spec.State) : AAt A {K} ⟨{n}, by decide⟩ = Spec.rounds {rounds_end[n]} (A ⟨{n}, by decide⟩) := by
  have h0 : AAt A 0 ⟨{n}, by decide⟩ = Spec.rounds 0 (A ⟨{n}, by decide⟩) := rfl
''')
            else:
                # a segment starting mid-way: node `n` starts at round {r0n} of some absorbed state `X n`
                f.write(f'''set_option maxRecDepth 100000 in
theorem aat_{n} (X A : Fin {count} → Spec.State) (hA : A ⟨{n}, by decide⟩ = Spec.rounds {r0n} (X ⟨{n}, by decide⟩)) :
    AAt A {K} ⟨{n}, by decide⟩ = Spec.rounds {rounds_end[n]} (X ⟨{n}, by decide⟩) := by
  have h0 : AAt A 0 ⟨{n}, by decide⟩ = Spec.rounds {r0n} (X ⟨{n}, by decide⟩) := hA
''')
            for c in range(K):
                r0, r1 = PLAN['rounds'][c][n], PLAN['rounds'][c + 1][n]
                if r1 == r0 + 1:
                    f.write(f'''  have h{c + 1} : AAt A {c + 1} ⟨{n}, by decide⟩ = Spec.rounds {r1} ({'A' if r0n == 0 else 'X'} ⟨{n}, by decide⟩) := by
    show sched (AAt A {c}) {c} ⟨{n}, by decide⟩ = _
    rw [sched_act (AAt A {c}) {c} ⟨{n}, by decide⟩ (by decide), h{c}, show sched.rndSlice {c} = {r0} from rfl, rounds_succ]
''')
                else:
                    f.write(f'''  have h{c + 1} : AAt A {c + 1} ⟨{n}, by decide⟩ = Spec.rounds {r1} ({'A' if r0n == 0 else 'X'} ⟨{n}, by decide⟩) := by
    show sched (AAt A {c}) {c} ⟨{n}, by decide⟩ = _
    rw [sched_nact (AAt A {c}) {c} ⟨{n}, by decide⟩ (by decide), h{c}]
''')
            f.write(f'  exact h{K}\n\n')
        f.write(f'end Keccaktree.Kernels.{ns}\n')
    with open(os.path.join(outdir, 'Final.lean'), 'w') as f:
        f.write(f'''import Keccaktree.Kernels.{nsdir}.{GEN}.Batch
import Keccaktree.Asm.Final
import Keccaktree.Asm.Node
import Keccaktree.Asm.Exec
/-! GENERATED: the plan on the concrete machine. -/
''' + header(ns) + f'''
/-- The slices of the plan. -/
def slices : Nat → List {ISA}.Instr
''' + ''.join(f'  | {c} => slice{c}\n' for c in range(K)) + f'''  | _ => []

/-- The concrete states along the plan. -/
def stateAt (S0 : State (BitVec 64)) : Nat → State (BitVec 64)
  | 0 => S0
  | c + 1 => {ISA_EXPR}.execTrace rodata (slices c) (stateAt S0 c)

/-- Status of a concrete state at a cut. -/
def Ok (S : State (BitVec 64)) : Prop := S.err = false ∧ S.halted = false ∧ S.tail = none

''')
        for c in range(K):
            nxt = c + 1 if c < K - 1 else None
            f.write(f'''theorem conc{c} (S0 : State (BitVec 64)) (hc : cutOf ctl{c} (stateAt S0 {c}) = cut{c}) (hs : Ok (stateAt S0 {c})) :
    envOf (stateAt S0 {c + 1}) = (fun i => E.eval (envOf (stateAt S0 {c})) (readVar result{c} i)) ∧
    ''' + (f'Ok (stateAt S0 {c + 1})' if nxt is not None else f'(stateAt S0 {c + 1}).err = false ∧ (stateAt S0 {c + 1}).halted = true ∧ (stateAt S0 {c + 1}).tail = result{c}.tail') + (f' ∧ cutOf ctl{nxt} (stateAt S0 {c + 1}) = cut{nxt}' if nxt is not None else '') + f''' := by
  have hne : ({ISA_EXPR}.execTrace rodata slice{c} cut{c}).err = false := ctrl{c}.2.2.2.2.2.2.2.2.2.1
  have h1 := slice_concrete {ISA_EXPR} rodata slice{c} ctl{c} cut{c} (stateAt S0 {c}) hc hs hne
  have h2 := slice_ctrl {ISA_EXPR} rodata slice{c} ctl{c} cut{c} (stateAt S0 {c}) hc hs hne
  simp only at h2
  obtain ⟨hg, hk, hzf, hcf, hnf, hvf, hvl, hpc, hdepth, herr, hhalted, htail⟩ := h2
  have hctrl := ctrl{c}
  have hT : stateAt S0 {c + 1} = {ISA_EXPR}.execTrace rodata slice{c} (stateAt S0 {c}) := rfl
''' + (f'''  refine ⟨h1, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hT, herr]; exact hctrl.2.2.2.2.2.2.2.2.2.1
  · rw [hT, hhalted]; exact hctrl.2.2.2.2.2.2.2.2.2.2.1
  · rw [hT, htail]; exact hctrl.2.2.2.2.2.2.2.2.2.2.2
''' if nxt is not None else f'''  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [hT, herr]; exact hctrl.2.2.2.2.2.2.2.2.2.1
  · rw [hT, hhalted]; exact hctrl.2.2.2.2.2.2.2.2.2.2.1
  · rw [hT, htail]; rfl
'''))
            if nxt is not None:
                f.write(f'''  · show cutOf ctl{nxt} (stateAt S0 {c + 1}) = cutOf ctl{nxt} sc{nxt}
    apply cutOf_eq_of_ctrl
    · rw [hT]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hg]; exact hctrl.1.trans rfl
      · rw [hk]; exact hctrl.2.1.trans rfl
      · rw [hzf]; exact hctrl.2.2.1.trans rfl
      · rw [hcf]; exact hctrl.2.2.2.1.trans rfl
      · rw [hnf]; exact hctrl.2.2.2.2.1.trans rfl
      · rw [hvf]; exact hctrl.2.2.2.2.2.1.trans rfl
      · rw [hvl]; exact hctrl.2.2.2.2.2.2.1.trans rfl
      · rw [hpc]; exact hctrl.2.2.2.2.2.2.2.1.trans rfl
      · rw [hdepth]; exact hctrl.2.2.2.2.2.2.2.2.1.trans rfl
''')
                ctln = CTLS[nxt]
                if not ctln:
                    f.write(f'    · intro i hi; simp only [ctl{nxt}, List.mem_nil_iff] at hi\n')
                else:
                    f.write(f'    · intro i hi\n      rw [hT]\n      simp only [ctl{nxt}, List.mem_cons, List.mem_nil_iff, or_false] at hi\n')
                    f.write('      rcases hi with ' + ' | '.join('rfl' for _ in ctln) + '\n')
                    for j, v in enumerate(ctln):
                        f.write(f'      · rw [h1]\n        show E.eval (envOf (stateAt S0 {c})) (readVar result{c} {v}) = envOf sc{nxt} {v}\n        rw [ctlv{c}_{j}]; (try simp only [E.eval]); all_goals decide +kernel\n')
            f.write('\n')
        conc_chain = ''.join(f'  have c{c} := conc{c} S0 c{c - 1}.2.2 c{c - 1}.2.1\n' for c in range(1, K))
        f.write(f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem env_chain (S0 : State (BitVec 64)) (hc : cutOf ctl0 S0 = cut0) (hs : Ok S0) :
    envOf (stateAt S0 {K}) = envAt (envOf S0) {K} := by
  show envOf (stateAt S0 {K}) = envAt (envOf (stateAt S0 0)) {K}
  have c0 := conc0 S0 hc hs
''' + conc_chain + f'''  rw [''' + ', '.join(f'c{c}.1' for c in range(K - 1, -1, -1)) + f''']
  simp only [envAt]

''' + ''.join(f'''theorem run_slice{c} (S0 : State (BitVec 64)) (hc : cutOf ctl{c} (stateAt S0 {c}) = cut{c}) (hs : Ok (stateAt S0 {c})) :
    {ISA_EXPR}.run rodata prog idx{c}.length (stateAt S0 {c}) = stateAt S0 {c + 1} := by
  have h := {ISA_EXPR}.run_of_pathOk rodata prog idx{c} (envOf (stateAt S0 {c})) cut{c} path{c}
  rw [← hc, eval_cutOf ctl{c} (stateAt S0 {c}) hs] at h
  exact h

''' for c in range(K)) + f'''/-- The number of instructions of the plan. -/
def planLen : Nat := ''' + ' + '.join(f'idx{c}.length' for c in range(K)) + f'''

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem run_plan (S0 : State (BitVec 64)) (hc : cutOf ctl0 S0 = cut0) (hs : Ok S0) :
    {ISA_EXPR}.run rodata prog planLen S0 = stateAt S0 {K} := by
  show {ISA_EXPR}.run rodata prog planLen (stateAt S0 0) = stateAt S0 {K}
  have c0 := conc0 S0 hc hs
''' + conc_chain + f'''  unfold planLen
  repeat rw [Isa.run_add]
  rw [run_slice0 S0 hc hs''' + ''.join(f', run_slice{c} S0 c{c - 1}.2.2 c{c - 1}.2.1' for c in range(1, K)) + f''']

/-- The control part of the entry state (pointers, count, stack pointer; closed). -/
def entryCtrl : State (BitVec 64) := {ISA}.initState (fun _ => 0#64) 0 {count} entry

/-- The entry state of the kernel on `count` nodes of the message `input`. -/
def entryState (input : Int → BitVec 64) : State (BitVec 64) := {{ entryCtrl with mem := initMem input 0 }}

set_option maxRecDepth 100000 in
theorem entry_cut (input : Int → BitVec 64) : cutOf ctl0 (entryState input) = cut0 := by
  apply cutOf_eq_of_ctrl
  · exact ⟨Eq.trans (rfl : (entryState input).g = entryCtrl.g) (show entryCtrl.g = sc0.g by decide +kernel),
      Eq.trans (rfl : (entryState input).k = entryCtrl.k) (show entryCtrl.k = sc0.k by decide +kernel),
      Eq.trans (rfl : (entryState input).zf = entryCtrl.zf) (show entryCtrl.zf = sc0.zf by decide +kernel),
      Eq.trans (rfl : (entryState input).cf = entryCtrl.cf) (show entryCtrl.cf = sc0.cf by decide +kernel),
      Eq.trans (rfl : (entryState input).nf = entryCtrl.nf) (show entryCtrl.nf = sc0.nf by decide +kernel),
      Eq.trans (rfl : (entryState input).vf = entryCtrl.vf) (show entryCtrl.vf = sc0.vf by decide +kernel),
      Eq.trans (rfl : (entryState input).vl = entryCtrl.vl) (show entryCtrl.vl = sc0.vl by decide +kernel),
      Eq.trans (rfl : (entryState input).pc = entryCtrl.pc) (show entryCtrl.pc = sc0.pc by decide +kernel),
      Eq.trans (rfl : (entryState input).depth = entryCtrl.depth) (show entryCtrl.depth = sc0.depth by decide +kernel)⟩
  · intro i hi
    simp only [ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
''' + ('    rcases hi with ' + ' | '.join('rfl' for _ in CTLS[0]) + '\n' +
       ''.join((f'    · exact Eq.trans (rfl : envOf (entryState input) {v} = envOf entryCtrl {v}) (show envOf entryCtrl {v} = envOf sc0 {v} by decide +kernel)\n' if v < 288 else
                f'    · show initMem input 0 (memVarRegion {v}) (memVarIndex {v}) = envOf sc0 {v}\n      simp +decide only [initMem, memVarRegion, memVarIndex, ↓reduceIte]\n      try decide +kernel\n')
               for v in CTLS[0]) if CTLS[0] else '') + f'''
theorem entry_ok (input : Int → BitVec 64) : Ok (entryState input) := ⟨rfl, rfl, rfl⟩

/-- The state after the kernel call (`planLen` instructions, up to and including the final `ret` / tail jump). -/
def finalState (input : Int → BitVec 64) : State (BitVec 64) := {ISA_EXPR}.run rodata prog planLen (entryState input)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem kernel_correct (input : Int → BitVec 64) (A : Fin {count} → Spec.State)
    (h0 : Inv0 (envOf (entryState input)) A) :
    (finalState input).halted = true ∧ (finalState input).err = false ∧ (finalState input).tail = result{K - 1}.tail ∧
    Inv{K} (envOf (finalState input)) (AAt A {K}) := by
  have hb : finalState input = stateAt (entryState input) {K} := run_plan (entryState input) (entry_cut input) (entry_ok input)
  have c0 := conc0 (entryState input) (entry_cut input) (entry_ok input)
''' + ''.join(f'  have c{c} := conc{c} (entryState input) c{c - 1}.2.2 c{c - 1}.2.1\n' for c in range(1, K)) + f'''  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hb]; exact c{K - 1}.2.2.1
  · rw [hb]; exact c{K - 1}.2.1
  · rw [hb]; exact c{K - 1}.2.2.2
  · rw [hb, env_chain (entryState input) (entry_cut input) (entry_ok input)]
    exact chain (envOf (entryState input)) A h0

/-- The words of node `n` of the message. -/
def nodeWords (input : Int → BitVec 64) (n : Nat) (w : Nat) : BitVec 64 := input (Int.ofNat (8 * n + w))

theorem entry_mem_input (input : Int → BitVec 64) (q : Int) : envOf (entryState input) (memVar rInput q) = input q := by
  rw [envOf_mem]; show initMem input 0 rInput q = input q
  simp only [initMem, ↓reduceIte]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem entry_inv (input : Int → BitVec 64) :
    Inv0 (envOf (entryState input)) (fun n => absorbNode (nodeWords input n)) := by
  refine ⟨''' + ', '.join(
      [f'(by rw [entry_mem_input]; simp only [{SPEC_UNFOLD}, absorbNode_lane{w}, nodeWords, rotl0]; try rfl)' for n in range(count) for w in range(8)] +
      [f'(absorbNode_lane{k_} _)' for n in range(count) for k_ in range(8, 25)]) + f'''⟩

''')
        # the output words of the finished nodes: projections of Inv_K by position
        outs = ALLOC_END
        pos = {(node, kind): i for i, (node, kind, var, rot, ln) in enumerate(outs)}
        f.write(f'''set_option maxRecDepth 100000 in
/-- The output word `4n+w` of a state satisfying the final invariant, for any states `A`. -/
theorem invK_word (Sf : State (BitVec 64)) (A : Fin {count} → Spec.State) (h : Inv{K} (envOf Sf) A)
    (n w : Nat) (hn : n ∈ {done}) (hw : w < 4) :
    Sf.mem rOutput (Int.ofNat (4 * n + w)) = L (A ⟨n, by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn; omega⟩) w := by
  simp only [Inv{K}, {SPEC_UNFOLD}, rotl0, envOf_mem] at h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases w with _ | _ | _ | _ | w <;> (try omega) <;> rcases hn with ''' + ' | '.join('rfl' for _ in done) + '''
''' + ''.join(f'  · exact h{"".join(".2" for _ in range(pos[(n, w)]))}{".1" if pos[(n, w)] + 1 < len(outs) else ""}\n'
               for w in range(4) for n in done) + f'''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The kernel computes keccak256 of every node it finishes**: the call on `{count}` nodes halts
without a model fault; byte `8w+i` of the digest of each node in `{done}` is byte `i` of output word
`4n+w`{"; the remaining nodes are handed over by the tail call (`handover`)" if tail else ""}. -/
theorem kernel_keccak256 (input : Int → BitVec 64) :
    (finalState input).halted = true ∧ (finalState input).err = false ∧
    ∀ n w i : Nat, n ∈ {done} → w < 4 → i < 8 →
      ((finalState input).mem rOutput (Int.ofNat (4 * n + w))).extractLsb' (8 * i) 8 =
        Spec.keccak256 64 (nodeBytes (nodeWords input n)) (8 * w + i) := by
  obtain ⟨hh, he, _, hout⟩ := kernel_correct input (fun n => absorbNode (nodeWords input n)) (entry_inv input)
  generalize finalState input = Sf at hh he hout ⊢
  refine ⟨hh, he, ?_⟩
  intro n w i hn hw hi
  have key := invK_word Sf _ hout n w hn hw
  rw [key]
  have hr : ∀ m : Fin {count}, m.val ∈ {done} → AAt (fun n => absorbNode (nodeWords input n)) {K} m = Spec.rounds 24 (absorbNode (nodeWords input m.val)) := by
    intro m hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases m with ⟨m, hm'⟩
    simp only at hm
    rcases hm with ''' + ' | '.join('rfl' for _ in done) + '\n' + ''.join(f'    · exact aat_{n} _\n' for n in done) + f'''  rw [hr _ hn, absorbNode_keccak, squeezeByte_eq]
  have h1 : (8 * w + i) / 8 = w := by omega
  have h2 : (8 * w + i) % 8 = i := by omega
  rw [h1, h2]
  simp only [Spec.keccakF, Fin.val_mk]

''')
        if tail:
            f.write(f'''/-- **The hand-over**: the call ends in a tail call to `{tail}` with the remaining nodes:
the count, input and output registers are the closed constants of the final symbolic state. -/
theorem handover (input : Int → BitVec 64) :
    (finalState input).tail = some "{tail}" ∧
    ''' + ' ∧\n    '.join(f'(finalState input).gd.getD {n_} 0 = E.eval (envOf (stateAt (entryState input) {K - 1})) (readVar result{K - 1} (gdVar {n_}))' for n_ in HANDOVER_REGS) + f''' := by
  have hb : finalState input = stateAt (entryState input) {K} := run_plan (entryState input) (entry_cut input) (entry_ok input)
  have c0 := conc0 (entryState input) (entry_cut input) (entry_ok input)
''' + ''.join(f'  have c{c} := conc{c} (entryState input) c{c - 1}.2.2 c{c - 1}.2.1\n' for c in range(1, K)) + f'''  refine ⟨?_, ''' + ', '.join('?_' for _ in HANDOVER_REGS) + f'''⟩
  · rw [hb, c{K - 1}.2.2.2]; exact ctrl{K - 1}.2.2.2.2.2.2.2.2.2.2.2
''' + ''.join(f'''  · rw [hb]; have := congrFun c{K - 1}.1 (gdVar {n_}); rw [envOf_gd (stateAt (entryState input) {K}) ⟨{n_}, by decide⟩] at this
    simp only [Vector.getD, Vector.getElem?_eq_getElem (by decide : {n_} < 32)] at this ⊢; exact this
''' for n_ in HANDOVER_REGS) + f'''
''')
        f.write(f'end Keccaktree.Kernels.{ns}\n')


def gen_seg(kernel, ns, nsdir, count, lanes, outdir, bounds):
    """Seg.lean: the slice certificates and the segment at any relocated position."""
    ctlK = CTLS[K]
    scK = slice_lits(kernel, count, bounds[K], bounds[K] + 1, ctl=ctlK)[1]
    with open(os.path.join(outdir, 'Seg.lean'), 'w') as f:
        f.write(f"""import Keccaktree.Kernels.{nsdir}.{GEN}.Batch
{seg_file_imports()}/-! GENERATED by lean/gen_plan_proof.py; do not edit.  The segment's slice certificates and the
segment at every relocated position. -/
""" + header(ns) + f"""
/-- The address bound of the relocations. -/
def B : Int := {BOUND}

/-- The control words at the end of the segment (what the next segment starts from). -/
def ctl{K} : List Nat := {ctlK}

/-- The control state at the end of the segment (closed). -/
def sc{K} : State (BitVec 64) := {scK}

""")
        for c in range(K):
            ctln = CTLS[c + 1]
            glue_simp = ', '.join([f'ctl{c + 1}', 'List.all_cons', 'List.all_nil', 'Bool.and_true'] + [f'ctlv{c}_{j}' for j in range(len(ctln))])
            f.write(f"""set_option maxRecDepth 100000 in
/-- Slice {c}, certified. -/
def cert{c} : SliceCert {ISA_EXPR} {RELOC_EXPR} rodata prog B where
  ctl := ctl{c}
  sc := sc{c}
  idx := idx{c}
  ctl' := ctl{c + 1}
  sc' := sc{c + 1}
  path := path{c}
  dec := dec{c}
  glue := by
    show List.all ctl{c + 1} (fun v => E.fold (readVar result{c} v) == cutVar ctl{c + 1} sc{c + 1} v &&
      ctlTreeOk B (cutVar ctl{c + 1} sc{c + 1} v)) = true
    """ + (f"simp only [{glue_simp}]\n    decide +kernel" if ctln else "rfl") + f"""
  cells := by decide +kernel
  ctrl := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11, h12⟩ := ctrl{c}
    exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel), h3.trans (by decide +kernel),
      h4.trans (by decide +kernel), h5.trans (by decide +kernel), h6.trans (by decide +kernel),
      h7.trans (by decide +kernel), h8.trans (by decide +kernel), h9.trans (by decide +kernel), h11, h12⟩

""")
        def at(c):
            return 'S0' if c == 0 else f'(segAt{c} S0)'
        f.write("/-! The concrete states along the segment (one plain definition each: unfolded by delta). -/\n" +
                ''.join(f"def segAt{c + 1} (S0 : State (BitVec 64)) : State (BitVec 64) := {ISA_EXPR}.execTrace rodata slice{c} {at(c)}\n"
                        for c in range(K)) + f"""
/-- The number of instructions of the segment. -/
def segLen : Nat := """ + ' + '.join(f'idx{c}.length' for c in range(K)) + "\n\n")
        chain = ''.join(f"  have s{c} := (cert{c}).step ρ hρ hw {at(c)} s{c - 1}.2.2.2 s{c - 1}.2.2.1\n" for c in range(1, K))
        hyps = """(ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S0 : State (BitVec 64))
    (hc : relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0) (hs : SliceCert.Ok S0)"""
        f.write(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The segment at a relocated position**: from a concrete state whose cut is the segment's first
cut relocated by `ρ`, the fetch-execute loop runs the recorded path to the end cut relocated by `ρ`. -/
theorem seg_run {hyps} :
    {ISA_EXPR}.run rodata prog segLen S0 = segAt{K} S0 ∧ SliceCert.Ok (segAt{K} S0) ∧
    relocState ρ (cutOf ctl{K} sc{K}) = cutOf ctl{K} (segAt{K} S0) := by
  have s0 := (cert0).step ρ hρ hw S0 hc hs
{chain}  refine ⟨?_, s{K - 1}.2.2.1, s{K - 1}.2.2.2⟩
  show {ISA_EXPR}.run rodata prog (""" + ' + '.join(f'(cert{c}).idx.length' for c in range(K)) + f""") S0 = _
  repeat rw [Isa.run_add]
  rw [""" + ', '.join(f"s{c}.1, show {ISA_EXPR}.execTrace rodata (cert{c}).slice {at(c)} = segAt{c + 1} S0 from rfl" for c in range(K)) + f"""]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The lanes along the segment at a relocated position**: the invariants hold at the relocated
locations (base variables read through `ρ.var`). -/
theorem seg_data {hyps}
    (A : Fin {count} → Spec.State) (h0 : Inv0 (fun i => envOf S0 (ρ.var i)) A) :
    Inv{K} (fun i => envOf (segAt{K} S0) (ρ.var i)) (AAt A {K}) := by
  have s0 := (cert0).step ρ hρ hw S0 hc hs
{chain}""" + ''.join(f"""  have i{c + 1} : Inv{c + 1} (fun i => envOf (segAt{c + 1} S0) (ρ.var i)) (AAt A {c + 1}) := by
    apply Inv{c + 1}_congr _ _ _ (step{c} _ _ {'h0' if c == 0 else f'i{c}'})
    intro v hv
    show envOf ({ISA_EXPR}.execTrace rodata (cert{c}).slice {at(c)}) (ρ.var v) = _
    rw [s{c}.2.1]
    exact (cert{c}).data ρ hρ {at(c)} v (List.all_eq_true.mp noptr{c} v hv)
""" for c in range(K)) + f"""  exact i{K}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The memory the segment does not store to**: a cell whose base location no slice may store to
(`{WRITE_OK}` false) keeps its value. -/
theorem seg_frame {hyps}
    (r : Region) (q : Int) (hq : ({WRITE_OK}) (r, q - ρ.wshift r) = false) :
    (segAt{K} S0).mem r q = S0.mem r q := by
  have s0 := (cert0).step ρ hρ hw S0 hc hs
{chain}""" + ''.join(f"""  have m{c + 1} : (segAt{c + 1} S0).mem r q = {at(c)}.mem r q := by
    {(f"rw [show segAt{c + 1} S0 = {ISA_EXPR}.execTrace rodata (cert{c}).slice {at(c)} from rfl, s{c}.2.1]" if SEGFRAME_RW else f"show ({ISA_EXPR}.execTrace rodata (cert{c}).slice {at(c)}).mem r q = _" + chr(10) + f"    rw [s{c}.2.1]")}
    apply (cert{c}).frame {FOOT_EXPR} ρ {at(c)} {'hc' if c == 0 else f's{c - 1}.2.2.2'} r q
    intro hm
    have := List.all_eq_true.mp writes{c} _ hm
    exact absurd (hq.symm.trans this) (by decide)
""" for c in range(K)) + f"""  rw [""" + ', '.join(f'm{c}' for c in range(K, 0, -1)) + f"""]

""" + (seg_moves_text() if MOVES and not (COUNT_LOCS and (258, 258) in MOVES) else '')
       + (seg_count_text() if COUNT_LOCS and (258, 258) in MOVES else '') + (seg_flags_text() if FLAG_OBL else '')
       + (seg_facts_text() if ISA == 'X86' else '') + f"""end Keccaktree.Kernels.{ns}
""")


def seg_file_imports():
    """the imports of Seg.lean after the batch module.  AArch64: its footprint module and the flags module
    line (empty without FLAG_OBL; kept so the proved AArch64 segments regenerate byte-identically); x86 and
    RISC-V: `Iter` (the footprint comes with the slices), plus `X86Kernel` for x86 (`SegFacts`) and the flags
    module with FLAG_OBL."""
    if ISA == 'Arm':
        return f'import {SEG_IMPORT}\n{FLAG_IMPORT}\n'
    return ('import Keccaktree.Asm.Iter\n' + ('import Keccaktree.Asm.X86Kernel\n' if ISA == 'X86' else '')
            + (FLAG_IMPORT + '\n' if FLAG_IMPORT else ''))


def seg_facts_text():
    """the segment as a `SegFacts` bundle (and the count register kept, when it is a moved word)"""
    t = f"""set_option maxRecDepth 100000 in
/-- The segment, bundled. -/
def facts : X86K.SegFacts rodata prog where
  ctl0 := ctl0
  sc0 := sc0
  ctlK := ctl{K}
  scK := sc{K}
  len := segLen
  wok := ({WRITE_OK})
  run := fun ρ hρ hw S0 hc hs => by
    obtain ⟨h1, h2, h3⟩ := seg_run ρ hρ hw S0 hc hs
    rw [h1]; exact ⟨h2, h3⟩
  frame := fun ρ hρ hw S0 hc hs r q hq => by
    rw [(seg_run ρ hρ hw S0 hc hs).1]; exact seg_frame ρ hρ hw S0 hc hs r q hq

"""
    if (258, 258) in MOVES and COUNT_LOCS and (COUNT_LOCS[0], COUNT_LOCS[K]) != (258, 258):
        l0, lK = COUNT_LOCS[0], COUNT_LOCS[K]
        def side(v):
            return '258' if v == 258 else f'(ρ.var {v})'
        rws = '  rw [Reloc.var_lt ρ 258 (by decide)] at this\n' if 258 in (l0, lK) else ''
        t += f"""/-- The count register is carried through the segment: it is saved to / restored from the stack cell
`{l0 if l0 != 258 else lK}` (the batch uses `rdx` for its scalar node). -/
theorem facts_rdx (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S0 : State (BitVec 64))
    (hc : relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0) (hs : SliceCert.Ok S0) :
    envOf (X86.isa.run rodata prog segLen S0) {side(lK)} = envOf S0 {side(l0)} := by
  have := seg_count ρ hρ hw S0 hc hs
{rws}  rw [(seg_run ρ hρ hw S0 hc hs).1]; exact this

"""
    elif (258, 258) in MOVES:
        t += f"""/-- The count register is carried through the segment. -/
theorem facts_rdx (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S0 : State (BitVec 64))
    (hc : relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0) (hs : SliceCert.Ok S0) :
    envOf (X86.isa.run rodata prog segLen S0) 258 = envOf S0 258 := by
  have := seg_moves ρ hρ hw S0 hc hs 258 258 (by simp)
  rw [Reloc.var_lt ρ 258 (by decide)] at this
  rw [(seg_run ρ hρ hw S0 hc hs).1]; exact this

"""
    return t


def seg_count_text():
    """seg_count: the count's location at the segment's end holds what its location at the start held"""
    def at(c):
        return 'S0' if c == 0 else '(segAt%d S0)' % c
    L = []
    L.append('set_option maxRecDepth 100000 in')
    L.append('set_option maxHeartbeats 40000000 in')
    L.append('/-- **The count**, followed through the stack cell the batch saves it to. -/')
    L.append('theorem seg_count (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S0 : State (BitVec 64))')
    L.append('    (hc : relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0) (hs : SliceCert.Ok S0) :')
    L.append('    envOf (segAt%d S0) (ρ.var %d) = envOf S0 (ρ.var %d) := by' % (K, COUNT_LOCS[K], COUNT_LOCS[0]))
    L.append('  have s0 := (cert0).step ρ hρ hw S0 hc hs')
    for c in range(1, K):
        L.append('  have s%d := (cert%d).step ρ hρ hw %s s%d.2.2.2 s%d.2.2.1' % (c, c, at(c), c - 1, c - 1))
    for c in range(K):
        d, src = COUNT_LOCS[c + 1], COUNT_LOCS[c]
        L.append('  have v%d : envOf (segAt%d S0) (ρ.var %d) = envOf %s (ρ.var %d) := by' % (c + 1, c + 1, d, at(c), src))
        L.append('    have hm : readVar result%d %d = .var %d := by' % (c, d, src))
        L.append('      have := List.all_eq_true.mp moves%d (%d, %d) (by simp)' % (c, d, src))
        L.append('      simpa using this')
        L.append('    show envOf (%s.execTrace rodata (cert%d).slice %s) (ρ.var %d) = _' % (ISA_EXPR, c, at(c), d))
        L.append('    rw [s%d.2.1, (cert%d).data ρ hρ %s %d (by show (readVar result%d %d).noPtr = true; rw [hm]; rfl)]' % (c, c, at(c), d, c, d))
        L.append('    show E.eval _ (readVar result%d %d) = _' % (c, d))
        L.append('    rw [hm]; rfl')
    L.append('  rw [%s]' % ', '.join('v%d' % c for c in range(K, 0, -1)))
    L.append('')
    return '\n'.join(L) + '\n'


def count_locs(kernel, count, bounds):
    """where the count (rdx) lives at each bound: 258, or the stack cell a batch saves it to
    (`storeq [base + D], rdx` ... `loadq rdx, [base + D]`, e.g. the 5-node kernels whose scalar node uses rdx)"""
    txt = open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            f'Keccaktree/Kernels/{PROG_NS or NSDIR}/Program.lean')).read()
    body = txt[txt.index('def prog'):]
    prog = {}
    for ln in body[:body.index('\n]')].splitlines():
        m = re.match(r'^\s+(\..*?),?\s+-- (\d+)$', ln)
        if m: prog[int(m.group(2))] = m.group(1).rstrip(',')
    st = {pc: (int(m.group(1)), int(m.group(2))) for pc, i in prog.items()
          for m in [re.match(r'^\.storeq \(\.base (\d+) \((-?\d+)\)\) 2$', i)] if m}
    ld = {pc: (int(m.group(1)), int(m.group(2))) for pc, i in prog.items()
          for m in [re.match(r'^\.loadq 2 \(\.base (\d+) \((-?\d+)\)\)$', i)] if m}
    if not st:
        return None
    out = run('paths', kernel, count, 2000000, 0)
    path = None
    for ln in out.splitlines():
        m = re.match(r'^PATH (\d+) \[(.*)\]$', ln)
        if m and int(m.group(1)) == count:
            path = [int(x) for x in m.group(2).split(', ')] if m.group(2) else []
    assert path is not None
    def cell_at(step, bd):
        o = run('matches', kernel, count, step, 0)
        gd = re.search(r'gd=\[(.*?)\]', o).group(1).split(', ')
        w = int(gd[bd[0]].replace('#64', ''), 16)
        reg, off = w >> 56, (w & ((1 << 56) - 1)) + bd[1]
        assert off % 8 == 0
        q = off // 8
        return 288 + 8 * (2 * q if q >= 0 else 2 * (-q) - 1) + reg
    locs, loc, cells = [], 258, {}
    for c, b in enumerate(bounds):
        for t in range(bounds[c - 1] if c else 0, b):
            pc = path[t]
            if pc in st and loc == 258:
                # rdx holds the count: saved (later stores of rdx spill the scalar node's data, not the count)
                if st[pc] not in cells:
                    cells[st[pc]] = cell_at(t, st[pc])
                loc = cells[st[pc]]
            elif pc in ld and loc != 258 and cells.get(ld[pc]) == loc:
                loc = 258
        locs.append(loc)
    return locs


def seg_moves_text():
    """seg_moves: at the end of the segment, d holds what s held at its start.  With MOVE_CHAIN (AArch64)
    every move is followed along its path of locations (one theorem per move); without it each word is
    moved in the first slice and kept afterwards (x86, RISC-V: one theorem over all moves)."""
    return seg_moves_chain_text() if MOVE_CHAIN else seg_moves_kept_text()


def seg_moves_kept_text():
    """seg_moves without MOVE_CHAIN: `d` holds `s` after the first slice and is kept by the others"""
    def at(c):
        return 'S0' if c == 0 else '(segAt%d S0)' % c
    L = []
    L.append('set_option maxRecDepth 100000 in')
    L.append('set_option maxHeartbeats 40000000 in')
    L.append('/-- **The moved words**: at the end of the segment, `d` holds what `s` held at its start. -/')
    L.append('theorem seg_moves (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S0 : State (BitVec 64))')
    L.append('    (hc : relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0) (hs : SliceCert.Ok S0)')
    L.append('    (d s : Nat) (hp : (d, s) ∈ (%s : List (Nat × Nat))) :' % (MOVES,))
    L.append('    envOf (segAt%d S0) (ρ.var d) = envOf S0 (ρ.var s) := by' % K)
    L.append('  have s0 := (cert0).step ρ hρ hw S0 hc hs')
    for c in range(1, K):
        L.append('  have s%d := (cert%d).step ρ hρ hw %s s%d.2.2.2 s%d.2.2.1' % (c, c, at(c), c - 1, c - 1))
    for c in range(K):
        src = 's' if c == 0 else 'd'
        L.append('  have v%d : envOf (segAt%d S0) (ρ.var d) = envOf %s (ρ.var %s) := by' % (c + 1, c + 1, at(c), src))
        L.append('    have hm : readVar result%d d = .var %s := by' % (c, src))
        L.append('      have := List.all_eq_true.mp moves%d (d, %s) (by' % (c, src))
        L.append('        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp ⊢')
        if c == 0:
            L.append('        exact hp)')
        else:
            L.append('        rcases hp with %s <;> simp)' % (' | '.join('⟨rfl, rfl⟩' for _ in MOVES)))
        L.append('      simpa using this')
        L.append('    show envOf (%s.execTrace rodata (cert%d).slice %s) (ρ.var d) = _' % (ISA_EXPR, c, at(c)))
        L.append('    rw [s%d.2.1, (cert%d).data ρ hρ %s d (by show (readVar result%d d).noPtr = true; rw [hm]; rfl)]' % (c, c, at(c), c))
        L.append('    show E.eval _ (readVar result%d d) = _' % c)
        L.append('    rw [hm]; rfl')
    L.append('  rw [%s]' % ', '.join('v%d' % c for c in range(K, 0, -1)))
    L.append('')
    return '\n'.join(L) + '\n'


def seg_moves_chain_text():
    """seg_moves with MOVE_CHAIN: each move along its path of locations `MOVE_PATHS[m]`, one location per cut"""
    def at(c):
        return 'S0' if c == 0 else '(segAt%d S0)' % c
    hyps = ('(ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S0 : State (BitVec 64))\n'
            '    (hc : relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0) (hs : SliceCert.Ok S0)')
    L = []
    for m, (d, s_) in enumerate(MOVES):
        path = MOVE_PATHS[m]
        L.append('set_option maxRecDepth 100000 in')
        L.append('set_option maxHeartbeats 40000000 in')
        L.append('/-- Move %d: at the end of the segment, `%d` holds what `%d` held at its start (path %s). -/' % (m, d, s_, path))
        L.append('theorem seg_move%d %s :' % (m, hyps))
        L.append('    envOf (segAt%d S0) (ρ.var %d) = envOf S0 (ρ.var %d) := by' % (K, d, s_))
        L.append('  have s0 := (cert0).step ρ hρ hw S0 hc hs')
        for c in range(1, K):
            L.append('  have s%d := (cert%d).step ρ hρ hw %s s%d.2.2.2 s%d.2.2.1' % (c, c, at(c), c - 1, c - 1))
        for c in range(K):
            l0, l1 = path[c], path[c + 1]
            L.append('  have v%d : envOf (segAt%d S0) (ρ.var %d) = envOf %s (ρ.var %d) := by' % (c + 1, c + 1, l1, at(c), l0))
            L.append('    have hm : readVar result%d %d = .var %d := by' % (c, l1, l0))
            L.append('      have := List.all_eq_true.mp moves%d (%d, %d) (by decide)' % (c, l1, l0))
            L.append('      simpa using this')
            L.append('    show envOf (' + ISA_EXPR + '.execTrace rodata (cert%d).slice %s) (ρ.var %d) = _' % (c, at(c), l1))
            L.append('    rw [s%d.2.1, (cert%d).data ρ hρ %s %d (by show (readVar result%d %d).noPtr = true; rw [hm]; rfl)]' % (c, c, at(c), l1, c, l1))
            L.append('    show E.eval _ (readVar result%d %d) = _' % (c, l1))
            L.append('    rw [hm]; rfl')
        L.append('  rw [%s]' % ', '.join('v%d' % c for c in range(K, 0, -1)))
        L.append('')
    L.append('/-- **The moved words**: at the end of the segment, `d` holds what `s` held at its start. -/')
    L.append('theorem seg_moves %s' % hyps)
    L.append('    (d s : Nat) (hp : (d, s) ∈ (%s : List (Nat × Nat))) :' % (MOVES,))
    L.append('    envOf (segAt%d S0) (ρ.var d) = envOf S0 (ρ.var s) := by' % K)
    L.append('  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp')
    L.append('  rcases hp with %s' % ' | '.join('⟨rfl, rfl⟩' for _ in MOVES))
    for m in range(len(MOVES)):
        L.append('  · exact seg_move%d ρ hρ hw S0 hc hs' % m)
    L.append('')
    return '\n'.join(L) + '\n'


def seg_flags_text():
    """seg_flags: the segment's slices neither read nor write the flags, so it runs from any flags"""
    def at(c):
        return 'S0' if c == 0 else '(segAt%d S0)' % c
    L = ['set_option maxRecDepth 100000 in', 'set_option maxHeartbeats 40000000 in',
         '/-- **The segment from any flags**: no slice reads or writes the flags, so the state at the relocated',
         'cut with its flags replaced runs the same path to the end state with those flags. -/',
         'theorem seg_flags (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S0 : State (BitVec 64))',
         '    (hc : relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0) (hs : SliceCert.Ok S0) (z c n v : Bool) :',
         '    %s.run rodata prog segLen (S0.withFlags z c n v) = (segAt%d S0).withFlags z c n v := by' % (ISA_EXPR, K),
         '  have s0 := (cert0).step ρ hρ hw S0 hc hs']
    for c in range(1, K):
        L.append('  have s%d := (cert%d).step ρ hρ hw %s s%d.2.2.2 s%d.2.2.1' % (c, c, at(c), c - 1, c - 1))
    for c in range(K):
        hc_ = 'hc' if c == 0 else 's%d.2.2.2' % (c - 1)
        hs_ = 'hs' if c == 0 else 's%d.2.2.1' % (c - 1)
        L.append('  have f%d := %s.cpath_flags %s rodata prog idx%d (by decide +kernel) %s z c n v ((cert%d).cpath_at ρ hρ hw %s %s %s)'
                 % (c, ISA_EXPR, FLAG_OBL, c, at(c), c, at(c), hc_, hs_))
        L.append('  have r%d : %s.run rodata prog idx%d.length (%s.withFlags z c n v) = (segAt%d S0).withFlags z c n v := by'
                 % (c, ISA_EXPR, c, at(c), c + 1))
        L.append('    rw [%s.run_of_cpath rodata prog _ _ f%d.1]; exact f%d.2' % (ISA_EXPR, c, c))
    L.append('  show %s.run rodata prog (%s) (S0.withFlags z c n v) = _' % (ISA_EXPR, ' + '.join('idx%d.length' % c for c in range(K))))
    L.append('  repeat rw [Isa.run_add]')
    L.append('  rw [%s]' % ', '.join('r%d' % c for c in range(K)))
    L.append('')
    return '\n'.join(L) + '\n'


def move_paths(kernel, count, bounds):
    """the location of every moved word at every cut: without MOVE_CHAIN, `s` at the start and `d` after the
    first slice (kept); with MOVE_CHAIN=1, followed through the slices' trees (a word copied from the tracked
    location; `d` preferred, then staying in place)"""
    paths = []
    for (d, s_) in MOVES:
        if not MOVE_CHAIN:
            paths.append([s_] + [d] * K)
            continue
        path = [s_]
        for c in range(K):
            trees = slice_lits(kernel, count, bounds[c], bounds[c + 1], ctl=CTLS[c])[3]
            cur = path[-1]
            want = '(.var %d)' % cur
            cands = [v for v, t in trees.items() if t == want]
            if cur not in trees:
                cands.append(cur)
            if c == K - 1:
                assert d in cands, f'move {d}:{s_}: {d} does not hold .var {cur} after the last slice (cands {cands})'
                path.append(d)
            elif d in cands:
                path.append(d)
            elif cur in cands:
                path.append(cur)
            else:
                assert cands, f'move {d}:{s_}: value of {cur} lost in slice {c}'
                path.append(sorted(cands)[0])
        paths.append(path)
    print(f'move paths: {paths}', file=sys.stderr)
    return paths


ALLOC_END = []
COUNT_LOCS = None
NSDIR = None
SEG = bool(os.environ.get('SEG'))
FLAGS = os.environ.get('FLAGS', '').split(',') if os.environ.get('FLAGS') else None   # zf,cf override at the start
HEAL = int(os.environ.get('HEAL', '0'))
K1 = int(os.environ['K1']) if os.environ.get('K1') else None   # k1 override at the segment's start   # the override applies to states before this step
END_CTL = [int(x) for x in os.environ.get('END_CTL', '').split(',') if x]
FORBID_CTL = [int(x) for x in os.environ.get('FORBID_CTL', '').split(',') if x]
START_CTL = [int(x) for x in os.environ.get('START_CTL', '').split(',') if x]
WRITE_OK = os.environ.get('WRITE_OK', 'fun _ => true')   # Lean: (Region × Int) → Bool, the cells a slice may store to
BOUND = os.environ.get('BOUND', '2 ^ 54')
LOOP = bool(os.environ.get('LOOP'))      # segment mode: a loop body (end control words = start control words)
# words the segment moves (in its first slice) or keeps: 'd:s,d:s' (d holds what s held at the start)
MOVES = [tuple(int(y) for y in x.split(':')) for x in os.environ.get('MOVES', '').split(',') if x]
MOVE_CHAIN = bool(os.environ.get('MOVE_CHAIN'))
# segment mode: the ISA's flag-oblivious instructions (e.g. Arm.flagObl): emit `seg_flags`
FLAG_OBL = os.environ.get('FLAG_OBL', '')
FLAG_IMPORT = {'Arm.flagObl': 'import Keccaktree.Asm.ArmFlags'}.get(FLAG_OBL, 'import Keccaktree.Asm.Flags' if FLAG_OBL else '')
MOVE_PATHS = []                   # the address bound of the relocation certificates


def main():
    global PLAN, K, ALLOC_END
    kernel, nsdir, count, lanes = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    global DROP_RC, INV_DEPTH_ALL, SEGFRAME_RW, STEP_DEPTH_ALL
    flag = lambda n, dflt: (os.environ[n] == '1') if n in os.environ else dflt
    INV_DEPTH_ALL = flag('INV_DEPTH_ALL', ISA == 'X86' and kernel in ('avx2_x9', 'avx2_x10'))
    SEGFRAME_RW = flag('SEGFRAME_RW', ISA == 'X86' and kernel in ('avx2_x6', 'avx2_x9', 'avx2_x10'))
    STEP_DEPTH_ALL = flag('STEP_DEPTH_ALL', ISA == 'X86' and kernel in ('avx2_x9', 'avx2_x10'))
    DROP_RC = (os.environ['DROP_RC'] == '1') if 'DROP_RC' in os.environ else \
        (ISA == 'X86' and kernel.startswith(('avx2_', 'x86_x1')))
    # x86b (AVX-512 kernels, which keep their RC hypotheses): an RC lane may need its hypotheses and bv_decide;
    # every other kernel keeps the plain `decide` form its proved slices were generated with.  RC_BV=0/1 overrides.
    global RC_BV
    RC_BV = (os.environ['RC_BV'] == '1') if 'RC_BV' in os.environ else (ISA == 'X86' and not DROP_RC)
    ns = os.environ.get('NS', nsdir)
    PLAN = json.load(open(os.environ['PLAN']))
    only_node = int(os.environ.get('ONLY_NODE', '-1'))
    outdir = os.environ.get('OUTDIR', '.')
    os.makedirs(outdir, exist_ok=True)
    cuts = PLAN['cuts']
    bounds = [PLAN['entry']] + [t + 1 for t in cuts] + [PLAN['end']]
    K = len(bounds) - 1
    assert len(PLAN['rounds']) == K + 1, (len(PLAN['rounds']), K + 1)
    assert all(len(r) == count for r in PLAN['rounds'])
    slices = os.environ.get('SLICES')
    slices = [] if slices == 'none' else ([int(x) for x in slices.split(',')] if slices else list(range(K)))
    global COUNT_LOCS, NSDIR
    NSDIR = nsdir
    if (258, 258) in MOVES and ISA == 'X86':
        COUNT_LOCS = count_locs(kernel, count, bounds)
        if COUNT_LOCS and all(v == 258 for v in COUNT_LOCS):
            COUNT_LOCS = None
        print(f'count locations: {COUNT_LOCS}', file=sys.stderr)
    CTLS.update(find_ctls(kernel, count, bounds))
    print(f'control words per slice: {[CTLS[c] for c in range(K)]}', file=sys.stderr)
    MOVE_PATHS[:] = move_paths(kernel, count, bounds)
    allocs = {}
    # NODES (x86): the nodes the plan tracks (default all); the others are not hashed in the plan (a segment
    # after earlier batches, e.g. the exit of a kernel's loop with the remaining nodes)
    nodes = [int(x) for x in os.environ.get('NODES', '').split(',') if x] or list(range(count))

    def alloc_at(c, mode):
        # the invariant's locations at bound c: 'input' (the input words), 'out' (matches in the output region),
        # 'regs' (matches in registers), 'mem<r>' (matches in region r), 'all' (every match)
        if mode == 'input':
            return [(n, w, mem_var(1, 8 * n + w), 0, f'input word {w} of node {n}') for n in range(count) for w in range(8)]
        if mode == 'out':
            return matches(kernel, count, bounds[c], lanes, PLAN['rounds'][c], region_filter=2)
        if mode == 'regs':
            return matches(kernel, count, bounds[c], lanes, PLAN['rounds'][c], regs_only=True)
        if mode.startswith('mem'):
            return matches(kernel, count, bounds[c], lanes, PLAN['rounds'][c], region_filter=int(mode[3:]))
        assert mode == 'all', mode
        return matches(kernel, count, bounds[c], lanes, PLAN['rounds'][c])
    def no_rc(al, mode):
        # at a segment's ends (non-default modes) round constants are never live: a word that merely equals one
        # (a pointer, a count, the constant lane 8) is not claimed
        return al if mode in ('input', 'out') else [h for h in al if not (75 <= h[1] < 99)]
    # start / end invariants: INV0 / INVK (rvu) when set; otherwise the input words of the tracked nodes (or, for
    # a segment starting mid-way, the matches then) and the output region (or every match, ending mid-way) (x86;
    # = 'input' / 'out' for a plan starting at round 0 and ending at round 24)
    if 'INV0' in os.environ:
        allocs[0] = no_rc(alloc_at(0, os.environ['INV0']), os.environ['INV0'])
    elif all(PLAN['rounds'][0][n] == 0 for n in nodes):
        allocs[0] = [(n, w, mem_var(1, 8 * n + w), 0, f'input word {w} of node {n}') for n in nodes for w in range(8)]
    else:
        # a segment starting mid-way (e.g. after the first flag write of a batch): the locations then
        allocs[0] = matches(kernel, count, bounds[0], lanes, PLAN['rounds'][0])
    for c in range(1, K):
        allocs[c] = matches(kernel, count, bounds[c], lanes, PLAN['rounds'][c])
        if os.environ.get('NO_RC_MID'):
            # round constants are loaded and used within a round: a word that merely equals one at a cut (a pointer
            # or count kept as data, e.g. the misaligned input pointer) is not claimed
            allocs[c] = [h for h in allocs[c] if not (75 <= h[1] < 99)]
    if 'INVK' in os.environ:
        allocs[K] = no_rc(alloc_at(K, os.environ['INVK']), os.environ['INVK'])
    elif all(PLAN['rounds'][K][n] == 24 for n in nodes):
        allocs[K] = matches(kernel, count, bounds[K], lanes, PLAN['rounds'][K], region_filter=2)
    else:
        allocs[K] = matches(kernel, count, bounds[K], lanes, PLAN['rounds'][K])
    for c in range(0, K + 1):
        allocs[c] = [h for h in allocs[c] if h[0] in nodes]
    if ISA == 'X86' and os.environ.get('PRUNE_RC', '1') == '1' and os.environ.get('DATA') != '0':
        # a round-constant match (kinds 75..98, input independent, so prone to coincidences) is kept only
        # if the location's tree after the slice is built from constants and hypothesis-backed locations:
        # drops leftover registers that merely hold an RC-valued word at the cut (e.g. a dead register at an
        # exit's start, a padding node hashed from uninitialised stack, a pointer word equal to a rotated RC)
        for c in range(K):
            if c not in slices and c + 1 not in slices:
                continue
            backed = {var_id(v) for (_, _, v, _, _) in allocs[c]}
            cells = [var_id(v) for (_, _, v, _, _) in allocs[c + 1] if var_id(v) >= 288]
            _, _, _, trees = slice_lits(kernel, count, bounds[c], bounds[c + 1], ctl=CTLS[c], cells=cells)
            keep, dropped = [], 0
            for h in allocs[c + 1]:
                if 75 <= h[1] < 99:
                    t = trees.get(var_id(h[2]), '')
                    leaves = {int(x) for x in re.findall(r'\.var (\d+)', t)}
                    if '.ptr' in t or not leaves <= backed:
                        dropped += 1
                        continue
                keep.append(h)
            if dropped:
                print(f'cut {c + 1}: dropped {dropped} unbacked round-constant matches', file=sys.stderr)
            allocs[c + 1] = keep
    ALLOC_END = allocs[K]
    chyps = {c: const_hyps([n for n in nodes if PLAN['rounds'][c][n] == 0]) for c in range(K + 1)}
    if os.environ.get('DATA') == '0':
        # a segment without data claims (frame code): no lane invariants
        allocs = {c: [] for c in range(K + 1)}
        chyps = {c: [] for c in range(K + 1)}
    if only_node >= 0:
        allocs = {c: [h for h in al if h[0] == only_node] for c, al in allocs.items()}
    gen_invs(ns, nsdir, count, allocs, chyps, outdir)
    for c in slices:
        a, b = bounds[c], bounds[c + 1]
        with open(os.path.join(outdir, f'Slice{c}.lean'), 'w') as f:
            gen_slice(kernel, ns, nsdir, count, lanes, c, a, b, allocs[c], allocs[c + 1], f, only_node, chyps[c], chyps[c + 1])
        print(f'slice {c}: steps [{a},{b}) in={len(allocs[c])} out={len(allocs[c + 1])}', file=sys.stderr)
    if os.environ.get('BATCH'):
        tail = control_at(kernel, count, bounds[K], lanes)[10]
        gen_batch_final(ns, nsdir, count, outdir, tail)
        if SEG:
            os.remove(os.path.join(outdir, 'Final.lean'))
            gen_seg(kernel, ns, nsdir, count, lanes, outdir, bounds)


if __name__ == '__main__':
    main()
