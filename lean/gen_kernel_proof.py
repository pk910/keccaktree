#!/usr/bin/env python3
"""Generate the per-slice proof files of a kernel from kttool's output.

    gen_kernel_proof.py <kernel> <Namespace> <count> <lanes> <entry_t> <end_t> <cut_t1> ... <cut_t23>

Scan line numbers `t` denote the state after `t+1` steps.  `entry_t` is the
scan line executing the batch's first instruction (state before it = after
`entry_t` steps), `end_t` the line executing the batch's `ret`.  Slice 0 runs
from the batch entry to cut 1; slice c (1 ≤ c ≤ 22) from cut c to cut c+1;
slice 23 from cut 23 to after the `ret`.

Environment: SLICES=0,5,23 (default all), ONLY_NODE=n, OUTDIR=dir, BATCH=1 (also Batch/Final),
ISA=X86|Arm (the `Isa` of the kernel, default X86).

Control words: the cut variables that must stay constant (pointers/counts in
data registers or stack cells; empty for the x86 kernels) are found per slice
by kttool and united over the batch (pass 1), then every slice is generated
with the union (pass 2), so that a control word stays a constant across all
cuts.
"""
import os, re, subprocess, sys

KT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '.lake/build/bin/kttool')

ISA = os.environ.get('ISA', 'X86')                 # X86 | Arm | Riscv: the namespace of the Instr type
ISA_EXPR = os.environ.get('ISA_EXPR', ISA + '.isa')  # the Isa term (e.g. `(Riscv.isa 2)`)
ISA_HOM = {'X86': 'Trace', 'Arm': 'ArmHom', 'Riscv': 'RiscvHom'}[ISA]
PROG_NS = os.environ.get('PROG_NS')                 # namespace of Program.lean when it differs from <Namespace> (RVV variants)
CTLS = {}          # slice -> its control words

def run(*args, ctl=()):
    env = dict(os.environ)
    env['KT_CTL'] = ','.join(str(v) for v in ctl)
    return subprocess.run([KT] + [str(a) for a in args], capture_output=True, text=True, check=True, env=env).stdout

def matches(kernel, count, steps, lanes, rnd, region_filter=None):
    out = run('matches', kernel, count, steps, lanes)
    alloc = []
    for ln in out.splitlines():
        m = re.match(r'^\(\.(reg|mem) (\d+) \(?(-?\d+)\)?\) (\d+) (\d+) (\d+) (\d+)$', ln)
        mg = re.match(r'^\(\.gd (\d+)\) (\d+) (\d+) (\d+) (\d+)$', ln)
        if mg:
            if region_filter is not None: continue
            n_, node, round_, kind, rot = mg.groups()
            if int(round_) != rnd: continue
            alloc.append((int(node), int(kind), f'(gdVar {n_})', int(rot), ln)); continue
        if not m: continue
        kind_loc, a, b, node, round_, kind, rot = m.groups()
        if int(round_) != rnd: continue
        if kind_loc == 'reg':
            if region_filter is not None: continue
            var = f'(regVar {a} {b})'
        else:
            if region_filter is not None and int(a) != region_filter: continue
            var = mem_var(int(a), int(b))
        alloc.append((int(node), int(kind), var, int(rot), ln))
    # a round constant (kinds 75..98) is reported for node 0 only but is a hypothesis every node may use
    alloc += [(n, kind, var, rot, ln) for (node, kind, var, rot, ln) in list(alloc) if kind >= 75
              for n in range(count) if n != node]
    return alloc

def control_at(kernel, count, steps, lanes):
    """control part (g, k, zf, cf, pc, depth) of the concrete state after `steps` steps"""
    out = run('matches', kernel, count, steps, lanes)
    m = re.search(r'^CONTROL g=\[(.*?)\] gd=\[.*?\] k=\[(.*?)\] zf=(\w+) cf=(\w+) nf=(\w+) vf=(\w+) vl=(\d+) pc=(\d+) depth=(\d+)', out, re.M)
    g = re.sub(r'⟨(\d+), \((-?\d+)\)⟩', r'(Addr.mk \1 (\2))', m.group(1))
    return g, m.group(2), m.group(3), m.group(4), m.group(5), m.group(6), int(m.group(7)), int(m.group(8)), int(m.group(9))

def slice_lits(kernel, count, a, b, ctl=()):
    out = run('slice', kernel, count, a, b, ctl=ctl)
    ctl = [int(x) for x in re.findall(r'\d+', re.search(r'^CTL (.*)$', out, re.M).group(1))]
    sc = re.search(r'^SC (.*)$', out, re.M).group(1)
    idx = re.search(r'^IDX (.*)$', out, re.M).group(1)
    trees = {}
    for m in re.finditer(r'^VAR (\d+) (.*)$', out, re.M):
        trees[int(m.group(1))] = m.group(2)
    err = re.search(r'^ERR (\w+)', out, re.M).group(1)
    assert err == 'false', 'symbolic slice failed'
    return ctl, sc, idx, trees

def find_ctls(kernel, count, bounds):
    """The control words of every slice: what its own address arithmetic needs (kttool's
    fixpoint), the stack cells any slice needs (constant through the batch), and, backwards,
    whatever a later cut's control word is a bare variable of after the slice before it."""
    need = {}
    for c in range(24):
        need[c] = set(slice_lits(kernel, count, bounds[c], bounds[c + 1])[0])
    cells = set(v for c in need for v in need[c] if v >= 288)
    for c in range(24):
        need[c] |= cells
    changed = True
    while changed:
        changed = False
        for c in range(23, 0, -1):
            trees = slice_lits(kernel, count, bounds[c - 1], bounds[c], ctl=sorted(need[c - 1]))[3]
            for v in sorted(need[c]):
                t = trees[v]
                m = re.fullmatch(r'\(\.var (\d+)\)', t)
                if m and int(m.group(1)) not in need[c - 1]:
                    need[c - 1].add(int(m.group(1))); changed = True
                elif not m:
                    # a closed expression (constant folding happens in `E.closed`): e.g. the stack pointer after `addi`
                    assert '.var' not in t, f'control word {v} of cut {c} is computed by slice {c - 1}: {t[:100]}'
    return {c: sorted(need[c]) for c in range(24)}

def mem_var(region, q):
    """the Lean text of a memory variable; the input and output regions are written with their names
    and node-relative indices so that the kernel theorems match the invariants syntactically"""
    if region == 1 and q >= 0: return f'(memVar rInput (Int.ofNat (8 * {q // 8} + {q % 8})))'
    if region == 2 and q >= 0: return f'(memVar rOutput (Int.ofNat (4 * {q // 4} + {q % 4})))'
    return f'(memVar {region} ({q}))'

def var_id(v):
    """numeric id of a variable expression (regVar r l) / (gdVar n) / (memVar region q)"""
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

# the spec side: `specQuantity (Spec.round r (A n)) kind` → lanes of the round → `round_lane_k` (Asm/RoundLanes.lean)
# → expressions in the atoms `L (A n) j`; the round constant becomes a literal.
SIMP_SPEC = '''specQuantity, ''' + ', '.join(f'round_lane_{k}' for k in range(25)) + ''', Spec.RC'''

def const_hyps(count, only_node):
    """lanes 8..24 of the absorbed single-block state: 0x01 at lane 8, 0x80<<56 at lane 16, 0 elsewhere"""
    hs = []
    for n in range(count):
        if only_node >= 0 and n != only_node: continue
        for k in range(8, 25):
            v = '1#64' if k == 8 else ('0x8000000000000000#64' if k == 16 else '0#64')
            hs.append((n, k, f'L (A {n}) {k} = {v}'))
    return hs

def gen_slice(kernel, ns, count, lanes, c, a, b, alloc_in, alloc_out, out, only_node, round_in):
    g, k, zf, cf, nf, vf, vl, pc, depth = control_at(kernel, count, b, lanes)
    chyps = const_hyps(count, only_node) if c == 0 else []
    """alloc_in: hypotheses at the cut (node, kind, var, rot, comment); round_in: the spec round applied
    by the slice (so the output quantities are of `Spec.round round_in (A n)`)."""
    ctl, sc, idx, trees = slice_lits(kernel, count, a, b, ctl=CTLS[c])
    assert sorted(ctl) == CTLS[c], (c, sorted(ctl), CTLS[c])
    ctl = CTLS[c]
    ctl_next = CTLS.get(c + 1, [])
    out.write(f'''import Keccaktree.Asm.Compose
import Keccaktree.Asm.{ISA_HOM}
import Keccaktree.Asm.RoundLanes
import Keccaktree.Proof
import Keccaktree.Kernels.{PROG_NS or ns}.Program
import Keccaktree.Kernels.{ns}.Gen.Invs
/-! GENERATED by lean/gen_kernel_proof.py; do not edit.  Slice {c} of the batch: steps [{a}, {b}). -/
namespace Keccaktree.Kernels.{ns}
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak
{f'open Keccaktree.Kernels.{PROG_NS} (prog rodata entry)' if PROG_NS else ''}

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
    out.write(f'''set_option maxRecDepth 100000 in
/-- The control part after the slice (kernel-computed): what the next cut starts from. -/
theorem ctrl{c} : result{c}.g = #v[{g}] ∧ result{c}.k = #v[{k}] ∧ result{c}.zf = {zf} ∧ result{c}.cf = {cf} ∧
    result{c}.nf = {nf} ∧ result{c}.vf = {vf} ∧ result{c}.vl = {vl} ∧
    result{c}.pc = {pc} ∧ result{c}.depth = {depth} ∧ result{c}.err = false ∧ result{c}.halted = {'true' if c == 23 else 'false'} ∧
    result{c}.tail = none := by decide +kernel

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
    # the output locations
    outs = [(node, kind, var, rot, ln) for (node, kind, var, rot, ln) in alloc_out if only_node < 0 or node == only_node]
    vids = [var_id(v) for (_, _, v, _, _) in outs]
    # kernel evaluation of the slice, in chunks (one `decide +kernel` each; the `Decidable` instance of a
    # conjunction of hundreds of large equations is too big to synthesize)
    CHUNK = 16
    out.write('-- The symbolic lanes at the output locations (kernel evaluations of the slice).\n')
    for p in range(0, len(outs), CHUNK):
        part = outs[p:p + CHUNK]
        out.write('set_option maxRecDepth 100000 in\nset_option synthInstance.maxHeartbeats 2000000 in\n')
        out.write(f'theorem outs{c}_c{p // CHUNK} : ' + ' ∧\n    '.join(f'readVar result{c} {v} = {trees[var_id(v)]}' for (_, _, v, _, _) in part) + ' := by decide +kernel\n\n')
        for j, (node, kind, var, rot, ln) in enumerate(part):
            proj = f'outs{c}_c{p // CHUNK}' + ''.join('.2' for _ in range(j)) + ('.1' if j + 1 < len(part) else '')
            out.write(f'theorem out{c}_{p + j} : readVar result{c} {var} = {trees[vids[p + j]]} := {proj}\n\n')
    hyp_all = [(i, h) for i, h in enumerate(alloc_in)]
    hyp_by = {(node, var_id(var)): (i, h) for i, h in hyp_all for (node, kind, var, rot, _) in [h]}
    chyp_by = {(n_, k): i for i, (n_, k, _) in enumerate(chyps)}
    # one generic lemma per tree shape (the nodes of a SIMD kernel compute the same tree on renamed variables)
    groups = {}
    inst = []   # per output j: (group, node, vars (in group order), hyp indices, chyp indices)
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        tree = trees[vids[j]]
        used = []
        for x in re.findall(r'\(\.var (\d+)\)', tree):
            if int(x) not in used: used.append(int(x))
        pos = {v: i for i, v in enumerate(used)}
        sig = re.sub(r'\(\.var (\d+)\)', lambda m: '(.var v%d)' % pos[int(m.group(1))], tree)
        hk = []
        hidx = []
        for v in used:
            if (node, v) in hyp_by:
                i, (_, k_, _, r_, _) = hyp_by[(node, v)]
                hk.append((k_, r_)); hidx.append(i)
            else:
                hk.append(None); hidx.append(None)
        ck = tuple(sorted(k for (n_, k) in chyp_by if n_ == node))
        if any(x is None for x in hidx):
            print(f'slice {c}: WARNING output {var} (node {node}, kind {kind}) depends on unlabelled inputs '
                  f'{[v for v, x in zip(used, hidx) if x is None]}', file=sys.stderr)
        key = (sig, tuple(hk), ck, kind, rot)
        if key not in groups:
            groups[key] = (len(groups), used, hidx)
        g = groups[key][0]
        inst.append((g, node, used, hidx, [chyp_by[(node, k)] for k in ck]))
    for key, (g, used0, hidx0) in groups.items():
        sig, hk, ck, kind, rot = key
        params = ' '.join(f'v{i}' for i in range(len(used0)))
        hyps = ' '.join(f'(h{i} : env v{i} = {quantity("n", k_)}.rotateLeft {r_})' for i, kr in enumerate(hk) if kr for (k_, r_) in [kr])
        hyps += ''.join(f' (c{k} : L (A n) {k} = {"1#64" if k == 8 else ("0x8000000000000000#64" if k == 16 else "0#64")})' for k in ck)
        hnames = ' '.join(f'h{i}' for i, kr in enumerate(hk) if kr)
        at_h = f' at {hnames}' if hnames else ''
        out.write(f'''set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- Lane kind {kind} (rotated by {rot}) of round {round_in}, for any node `n` whose quantities are at `v*`. -/
theorem lane{c}_g{g} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) (n : Fin {count}) ({params} : Nat) {hyps} :
    E.eval env ({sig}) = (specQuantity (Spec.round {round_in} (A n)) {kind}).rotateLeft {rot} := by
  simp +decide only [E.eval, ternlogW, List.range, List.range.loop, List.foldl, ↓reduceIte]
  {"simp only [specQuantity, Spec.RC]" + at_h if hnames else "skip"}
  simp only [{SIMP_SPEC}]
  bv_decide (config := {{ timeout := 1800 }})

''')
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        g, node, used, hidx, cidx = inst[j]
        hyps = ' '.join(f'(h{i} : env {var_} = {quantity(node_, kind_)}.rotateLeft {rot_})'
                        for i in hidx if i is not None for (node_, kind_, var_, rot_, _) in [alloc_in[i]])
        hyps += ''.join(f' (c{i} : {chyps[i][2]})' for i in cidx)
        args = ' '.join(f'({alloc_in[hyp_by[(node, v)][0]][2]})' if (node, v) in hyp_by else str(v) for v in used)
        hargs = ' '.join(f'h{i}' for i in hidx if i is not None) + ''.join(f' c{i}' for i in cidx)
        out.write(f'''/-- {ln} -/
theorem lane{c}_{j} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) {hyps} :
    E.eval env (readVar result{c} {var}) = (specQuantity (Spec.round {round_in} (A {node})) {kind}).rotateLeft {rot} := by
  rw [out{c}_{j}]
  exact lane{c}_g{g} env A ⟨{node}, by decide⟩ {args} {hargs}

''')
    print(f'slice {c}: {len(outs)} outputs, {len(groups)} generic lemmas', file=sys.stderr)
    # the step theorem
    out.write(f'/-- Slice {c}: the invariant at its start gives the output invariant, for the next round\'s states. -/\n')
    out.write(f'theorem step{c} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) (h : Inv{c} env A) :\n')
    out.write(f'    Inv{c + 1} (fun i => E.eval env (readVar result{c} i)) (fun n => Spec.round {round_in} (A n)) := by\n')
    names = ' '.join(f'h{i}' for i, _ in hyp_all) + ''.join(f' c{i}' for i in range(len(chyps)))
    names = names.strip()
    if names:
        out.write(f'  obtain ⟨{", ".join(names.split())}⟩ := h\n')
    else:
        out.write('  clear h\n')
    parts = []
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        g, node, used, hidx, cidx = inst[j]
        parts.append(f'lane{c}_{j} env A ' + ' '.join(f'h{i}' for i in hidx if i is not None) +
                     ''.join(f' c{i}' for i in cidx))
    out.write('  exact ⟨' + ', '.join(parts) + '⟩\n\n')
    out.write(f'end Keccaktree.Kernels.{ns}\n')

def quantity(node, kind):
    """the spec quantity of a match: `specQuantity (A node) kind`, or a round constant (kinds 75..98)"""
    return f'(specQuantity (A {node}) {kind})' if kind < 75 else f'(Spec.RC {kind - 75})'

def inv_conj(alloc):
    return ' ∧\n  '.join(f'env {var} = {quantity(node, kind)}.rotateLeft {rot}' for node, kind, var, rot, _ in alloc) or 'True'

def gen_invs(ns, count, allocs, chyps, outdir):
    """Invs.lean: `Inv{c}` = what the locations hold at cut c (c = 0..23), `Inv24` = the output locations after the batch."""
    with open(os.path.join(outdir, 'Invs.lean'), 'w') as f:
        f.write(f'''import Keccaktree.Asm.Cut
import Keccaktree.Proof
/-! GENERATED by lean/gen_kernel_proof.py; do not edit.  The invariants at the cuts of the batch:
what the locations (register lanes, general registers, memory words) hold, as quantities of the
nodes' sponge states `A n` (after `c` rounds at cut `c`); `Inv24` are the output locations. -/
namespace Keccaktree.Kernels.{ns}
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak

''')
        for c in range(25):
            doc = f'The locations at the start of slice {c}' if c < 24 else 'The output locations after the batch'
            f.write(f'/-- {doc} (for states `A n` of the nodes). -/\n')
            f.write(f'def Inv{c} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) : Prop :=\n  ' + inv_conj(allocs[c]) +
                    (''.join(f' ∧\n  {h}' for (_, _, h) in chyps) if c == 0 else '') + '\n\n')
        f.write(f'end Keccaktree.Kernels.{ns}\n')

def chain_haves(count):
    """the chain of slice steps with explicitly nested environments and states (no `envAt` unfolding needed)"""
    env = 'env0'
    A = 'A'
    out = []
    for c in range(24):
        src = 'step0 env0 A h0' if c == 0 else f'step{c} _ _ h{c}'
        out.append(f'  have h{c + 1} := {src}\n')
    return ''.join(out)

def gen_final(ns, count, outdir):
    """The concrete-machine theorem: run the 24 slices from a state with the entry cut's control part."""
    with open(os.path.join(outdir, 'Final.lean'), 'w') as f:
        f.write(f'''import Keccaktree.Kernels.{ns}.Gen.Batch
import Keccaktree.Asm.Final
import Keccaktree.Asm.Node
import Keccaktree.Asm.Exec
/-! GENERATED: the batch on the concrete machine. -/
namespace Keccaktree.Kernels.{ns}
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak
{f'open Keccaktree.Kernels.{PROG_NS} (prog rodata entry)' if PROG_NS else ''}

/-- The slices of the batch. -/
def slices : Nat → List {ISA}.Instr
''' + ''.join(f'  | {c} => slice{c}\n' for c in range(24)) + f'''  | _ => []

/-- The concrete states along the batch. -/
def stateAt (S0 : State (BitVec 64)) : Nat → State (BitVec 64)
  | 0 => S0
  | c + 1 => {ISA_EXPR}.execTrace rodata (slices c) (stateAt S0 c)

/-- Status of a concrete state at a cut. -/
def Ok (S : State (BitVec 64)) : Prop := S.err = false ∧ S.halted = false ∧ S.tail = none

''')
        # per step: from cutOf (stateAt c) = cut c, derive the next
        for c in range(24):
            nxt = c + 1 if c < 23 else None
            f.write(f'''theorem conc{c} (S0 : State (BitVec 64)) (hc : cutOf ctl{c} (stateAt S0 {c}) = cut{c}) (hs : Ok (stateAt S0 {c})) :
    envOf (stateAt S0 {c + 1}) = (fun i => E.eval (envOf (stateAt S0 {c})) (readVar result{c} i)) ∧
    ''' + (f'Ok (stateAt S0 {c + 1})' if nxt is not None else f'(stateAt S0 {c + 1}).err = false ∧ (stateAt S0 {c + 1}).halted = true') + (f' ∧ cutOf ctl{nxt} (stateAt S0 {c + 1}) = cut{nxt}' if nxt is not None else '') + f''' := by
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
''' if nxt is not None else f'''  refine ⟨h1, ?_, ?_⟩
  · rw [hT, herr]; exact hctrl.2.2.2.2.2.2.2.2.2.1
  · rw [hT, hhalted]; exact hctrl.2.2.2.2.2.2.2.2.2.2.1
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
                        f.write(f'      · rw [h1]\n        show E.eval (envOf (stateAt S0 {c})) (readVar result{c} {v}) = envOf sc{nxt} {v}\n        rw [ctlv{c}_{j}]; rfl\n')
            f.write('\n')
        f.write(f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The cut environment after the batch is the chained symbolic one. -/
theorem env_chain (S0 : State (BitVec 64)) (hc : cutOf ctl0 S0 = cut0) (hs : Ok S0) :
    envOf (stateAt S0 24) = envAt (envOf S0) 24 := by
  show envOf (stateAt S0 24) = envAt (envOf (stateAt S0 0)) 24
  have c0 := conc0 S0 hc hs
''' + ''.join(f'  have c{c} := conc{c} S0 c{c - 1}.2.2 c{c - 1}.2.1\n' for c in range(1, 24)) + f'''  rw [''' + ', '.join(f'c{c}.1' for c in range(23, -1, -1)) + f''']
  simp only [envAt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The batch on the concrete machine**: from any concrete state at the
batch entry with the entry cut's control part (`hc`) whose input locations
hold the nodes' words (`Inv0`), the output locations after the 24 slices
hold the digest lanes of `Spec.rounds 24` of every node. -/
theorem batch_correct (S0 : State (BitVec 64)) (A : Fin {count} → Spec.State)
    (hc : cutOf ctl0 S0 = cut0) (hs : Ok S0) (h0 : Inv0 (envOf S0) A) :
    Inv24 (envOf (stateAt S0 24)) (fun n => Spec.rounds 24 (A n)) := by
  rw [env_chain S0 hc hs]
  exact chain (envOf S0) A h0

/-! ### The fetch-execute loop follows the recorded paths -/

''' + ''.join(f'''theorem run_slice{c} (S0 : State (BitVec 64)) (hc : cutOf ctl{c} (stateAt S0 {c}) = cut{c}) (hs : Ok (stateAt S0 {c})) :
    {ISA_EXPR}.run rodata prog idx{c}.length (stateAt S0 {c}) = stateAt S0 {c + 1} := by
  have h := {ISA_EXPR}.run_of_pathOk rodata prog idx{c} (envOf (stateAt S0 {c})) cut{c} path{c}
  rw [← hc, eval_cutOf ctl{c} (stateAt S0 {c}) hs] at h
  exact h

''' for c in range(24)) + f'''/-- The number of instructions of the batch. -/
def batchLen : Nat := ''' + ' + '.join(f'idx{c}.length' for c in range(24)) + f'''

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem run_batch (S0 : State (BitVec 64)) (hc : cutOf ctl0 S0 = cut0) (hs : Ok S0) :
    {ISA_EXPR}.run rodata prog batchLen S0 = stateAt S0 24 := by
  show {ISA_EXPR}.run rodata prog batchLen (stateAt S0 0) = stateAt S0 24
  have c0 := conc0 S0 hc hs
''' + ''.join(f'  have c{c} := conc{c} S0 c{c - 1}.2.2 c{c - 1}.2.1\n' for c in range(1, 24)) + f'''  unfold batchLen
  repeat rw [Isa.run_add]
  rw [run_slice0 S0 hc hs''' + ''.join(f', run_slice{c} S0 c{c - 1}.2.2 c{c - 1}.2.1' for c in range(1, 24)) + f''']

/-- The control part of the entry state (pointers, count, stack pointer; closed). -/
def entryCtrl : State (BitVec 64) := {ISA}.initState (fun _ => 0#64) 0 {count} entry

/-- The entry state of the kernel on `count` nodes of the message `input`
(`initState input 0 count entry`: the control part and the input region). -/
def entryState (input : Int → BitVec 64) : State (BitVec 64) := {{ entryCtrl with mem := initMem input 0 }}

set_option maxRecDepth 100000 in
/-- The entry state has the entry cut's control part (the pointers, the count,
the stack pointer) for any message. -/
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

/-- The state after the kernel call (`batchLen` instructions, up to and including the final `ret`). -/
def finalState (input : Int → BitVec 64) : State (BitVec 64) := {ISA_EXPR}.run rodata prog batchLen (entryState input)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The kernel call on the concrete machine**: `count` nodes, from the
kernel entry to (and including) the final `ret`: the run halts without a
model fault, and the output locations hold the digest lanes of
`Spec.rounds 24` of every node whose words were in the input locations. -/
theorem kernel_correct (input : Int → BitVec 64) (A : Fin {count} → Spec.State)
    (h0 : Inv0 (envOf (entryState input)) A) :
    (finalState input).halted = true ∧ (finalState input).err = false ∧
    Inv24 (envOf (finalState input)) (fun n => Spec.rounds 24 (A n)) := by
  have hb : finalState input = stateAt (entryState input) 24 := run_batch (entryState input) (entry_cut input) (entry_ok input)
  have c0 := conc0 (entryState input) (entry_cut input) (entry_ok input)
''' + ''.join(f'  have c{c} := conc{c} (entryState input) c{c - 1}.2.2 c{c - 1}.2.1\n' for c in range(1, 24)) + f'''  refine ⟨?_, ?_, ?_⟩
  · rw [hb]; exact c23.2.2
  · rw [hb]; exact c23.2.1
  · rw [hb, env_chain (entryState input) (entry_cut input) (entry_ok input)]
    exact chain (envOf (entryState input)) A h0

/-! ### keccak256 of every node -/

/-- The words of node `n` of the message. -/
def nodeWords (input : Int → BitVec 64) (n : Nat) (w : Nat) : BitVec 64 := input (Int.ofNat (8 * n + w))

theorem entry_mem_input (input : Int → BitVec 64) (q : Int) : envOf (entryState input) (memVar rInput q) = input q := by
  rw [envOf_mem]; show initMem input 0 rInput q = input q
  simp only [initMem, ↓reduceIte]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The input locations at entry hold the nodes' words: the entry invariant
for the sponge states of the nodes. -/
theorem entry_inv (input : Int → BitVec 64) :
    Inv0 (envOf (entryState input)) (fun n => absorbNode (nodeWords input n)) := by
  refine ⟨''' + ', '.join(
      [f'(by rw [entry_mem_input]; simp only [specQuantity, absorbNode_lane{w}, nodeWords, rotl0]; try rfl)' for n in range(count) for w in range(8)] +
      [f'(absorbNode_lane{k} _)' for n in range(count) for k in range(8, 25)]) + f'''⟩

set_option maxRecDepth 100000 in
/-- The output word `4n+w` of a state satisfying `Inv24`, for any states `A`
(proved apart from the kernel theorem: the kernel typechecker must never have
to compare terms containing the concrete `Spec.rounds 24 …` states). -/
theorem inv24_word (Sf : State (BitVec 64)) (A : Fin {count} → Spec.State) (h : Inv24 (envOf Sf) A)
    (n w : Nat) (hn : n < {count}) (hw : w < 4) :
    Sf.mem rOutput (Int.ofNat (4 * n + w)) = L (A ⟨n, hn⟩) w := by
  simp only [Inv24, specQuantity, rotl0, envOf_mem] at h
  rcases n with ''' + ' | '.join(['_'] * count + ['n']) + ''' <;> rcases w with _ | _ | _ | _ | w <;> (try omega)
''' + ''.join(f'  · exact h{"".join(".2" for _ in range(4 * n + w))}{".1" if 4 * n + w + 1 < 4 * count else ""}\n' for n in range(count) for w in range(4)) + f'''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The kernel computes keccak256 of every node**: the kernel call on
`count` nodes halts without a model fault, and byte `8w+i` of the digest of
node `n` (`Spec.keccak256` of its 64 bytes) is byte `i` of output word
`4n+w`. -/
theorem kernel_keccak256 (input : Int → BitVec 64) :
    (finalState input).halted = true ∧ (finalState input).err = false ∧
    ∀ n w i : Nat, n < {count} → w < 4 → i < 8 →
      ((finalState input).mem rOutput (Int.ofNat (4 * n + w))).extractLsb' (8 * i) 8 =
        Spec.keccak256 64 (nodeBytes (nodeWords input n)) (8 * w + i) := by
  obtain ⟨hh, he, hout⟩ := kernel_correct input (fun n => absorbNode (nodeWords input n)) (entry_inv input)
  generalize finalState input = Sf at hh he hout ⊢
  refine ⟨hh, he, ?_⟩
  intro n w i hn hw hi
  have key := inv24_word Sf _ hout n w hn hw
  rw [key, absorbNode_keccak, squeezeByte_eq]
  have h1 : (8 * w + i) / 8 = w := by omega
  have h2 : (8 * w + i) % 8 = i := by omega
  rw [h1, h2]
  simp only [Spec.keccakF, Fin.val_mk]

end Keccaktree.Kernels.{ns}
''')

def main():
    kernel, ns, count, lanes = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    entry_t, end_t = int(sys.argv[5]), int(sys.argv[6])
    cuts = [int(x) for x in sys.argv[7:]]           # cut_t1 .. cut_t23
    assert len(cuts) == 23
    only_node = int(os.environ.get('ONLY_NODE', '-1'))
    outdir = os.environ.get('OUTDIR', '.')
    slices = os.environ.get('SLICES')
    slices = [] if slices == 'none' else ([int(x) for x in slices.split(',')] if slices else list(range(24)))
    # step boundaries: state after n steps
    bounds = [entry_t] + [t + 1 for t in cuts] + [end_t]   # bounds[c] = start of slice c; bounds[c+1] = its end (the batch ret excluded)
    # pass 1: the control words of every slice, united
    CTLS.update(find_ctls(kernel, count, bounds))
    print(f'control words per slice: {[CTLS[c] for c in range(24)]}', file=sys.stderr)
    # the invariants at every cut (and the outputs), once
    allocs = {}
    allocs[0] = [(n, w, mem_var(1, 8 * n + w), 0, f'input word {w} of node {n}') for n in range(count) for w in range(8)]
    for c in range(1, 24):
        allocs[c] = matches(kernel, count, bounds[c], lanes, c)
    allocs[24] = matches(kernel, count, bounds[24], lanes, 24, region_filter=2)
    if only_node >= 0:
        allocs = {c: [h for h in al if h[0] == only_node] for c, al in allocs.items()}
    gen_invs(ns, count, allocs, const_hyps(count, only_node), outdir)
    for c in slices:
        a, b = bounds[c], bounds[c + 1]
        alloc_in, alloc_out = allocs[c], allocs[c + 1]
        with open(os.path.join(outdir, f'Slice{c}.lean'), 'w') as f:
            gen_slice(kernel, ns, count, lanes, c, a, b, alloc_in, alloc_out, f, only_node, c)
        print(f'slice {c}: steps [{a},{b}) in={len(alloc_in)} out={len(alloc_out)}', file=sys.stderr)
    if os.environ.get('BATCH'):
        gen_final(ns, count, outdir)

        with open(os.path.join(outdir, 'Batch.lean'), 'w') as f:
            f.write(''.join(f'import Keccaktree.Kernels.{ns}.Gen.Slice{c}\n' for c in range(24)))
            f.write(f'''/-! GENERATED: the slices chained: from the input invariant to the output locations. -/
namespace Keccaktree.Kernels.{ns}
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak

/-- The cut environments along the batch, from the entry environment. -/
def envAt (env0 : Nat → BitVec 64) : Nat → (Nat → BitVec 64)
  | 0 => env0
''' + ''.join(f'  | {c + 1} => fun i => E.eval (envAt env0 {c}) (readVar result{c} i)\n' for c in range(24)) +
            f'''  | _ => env0

/-- The nodes' states along the batch: `c` rounds applied. -/
def AAt (A : Fin {count} → Spec.State) : Nat → (Fin {count} → Spec.State)
  | 0 => A
  | c + 1 => fun n => Spec.round c (AAt A c n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The batch computes Keccak-f[1600] on every node**: if the input words
are in place at the batch entry (`Inv0`), the output locations after the
24 slices hold the digest lanes of `Spec.rounds 24` of each node's state. -/
theorem chain (env0 : Nat → BitVec 64) (A : Fin {count} → Spec.State) (h0 : Inv0 env0 A) :
    Inv24 (envAt env0 24) (fun n => Spec.rounds 24 (A n)) := by
''' + chain_haves(count) + f'''  simp only [envAt]
  simp only [Spec.rounds, Spec.memo_eq]
  exact h24

end Keccaktree.Kernels.{ns}
''')

if __name__ == '__main__':
    main()
