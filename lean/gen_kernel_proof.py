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

ISA = os.environ.get('ISA', 'X86')
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
            var = f'(memVar {a} {b})'
        alloc.append((int(node), int(kind), var, int(rot), ln))
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
                    assert t.startswith('(.const '), f'control word {v} of cut {c} is computed by slice {c - 1}: {t[:100]}'
    return {c: sorted(need[c]) for c in range(24)}

def var_id(v):
    """numeric id of a variable expression (regVar r l) / (memVar region q)"""
    m = re.match(r'\(regVar (\d+) (\d+)\)', v)
    if m: return 8 * int(m.group(1)) + int(m.group(2))
    m = re.match(r'\(gdVar (\d+)\)', v)
    if m: return 256 + int(m.group(1))
    m = re.match(r'\(memVar (\d+) \(?(-?\d+)\)?\)', v)
    r, q = int(m.group(1)), int(m.group(2))
    enc = 2 * q if q >= 0 else 2 * (-q) - 1
    return 288 + 8 * enc + r

SIMP_SPEC = '''specQuantity, L_round, L_mk, Nat.reduceMod, Nat.reduceDiv,
    Fin.mk5_0, Fin.mk5_1, Fin.mk5_2, Fin.mk5_3, Fin.mk5_4, Fin.isValue, Fin.reduceAdd, Fin.reduceSub, Fin.reduceMul,
    Spec.round, Spec.iota, Spec.chi, Spec.pi, Spec.rho, Spec.theta, Spec.rhoOffset, Spec.RC,
    lane_0, lane_1, lane_2, lane_3, lane_4, lane_5, lane_6, lane_7, lane_8, lane_9, lane_10, lane_11, lane_12,
    lane_13, lane_14, lane_15, lane_16, lane_17, lane_18, lane_19, lane_20, lane_21, lane_22, lane_23, lane_24'''

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
import Keccaktree.Asm.{"ArmHom" if ISA == "Arm" else "Trace"}
import Keccaktree.Proof
import Keccaktree.Kernels.{ns}.Program
/-! GENERATED by lean/gen_kernel_proof.py; do not edit.  Slice {c} of the batch: steps [{a}, {b}). -/
namespace Keccaktree.Kernels.{ns}
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak

/-- The control words (cut variables kept constant). -/
def ctl{c} : List Nat := {ctl}

/-- The control state at the cut (closed). -/
def sc{c} : State (BitVec 64) := {sc}

def cut{c} : State E := cutOf ctl{c} sc{c}

def idx{c} : List Nat := {idx}

def slice{c} : List {ISA}.Instr := idx{c}.map (prog.getD · .nop)

/-- The symbolic state after the slice. -/
def result{c} : State E := {ISA}.isa.execTrace rodata slice{c} cut{c}

''')
    out.write(f'''set_option maxRecDepth 100000 in
/-- The control part after the slice (kernel-computed): what the next cut starts from. -/
theorem ctrl{c} : result{c}.g = #v[{g}] ∧ result{c}.k = #v[{k}] ∧ result{c}.zf = {zf} ∧ result{c}.cf = {cf} ∧
    result{c}.nf = {nf} ∧ result{c}.vf = {vf} ∧ result{c}.vl = {vl} ∧
    result{c}.pc = {pc} ∧ result{c}.depth = {depth} ∧ result{c}.err = false ∧ result{c}.halted = false ∧
    result{c}.tail = none := by decide +kernel

''')
    if ctl_next:
        for v in ctl_next:
            assert trees[v].startswith('(.const '), f'control word {v} is not constant after slice {c}: {trees[v][:80]}'
        out.write('set_option maxRecDepth 100000 in\n')
        out.write('/-- The control words of the next cut are constants after the slice. -/\n')
        out.write(f'theorem ctlv{c} : ' + ' ∧\n    '.join(f'readVar result{c} {v} = {trees[v]}' for v in ctl_next) + ' := by decide +kernel\n\n')
        for j, v in enumerate(ctl_next):
            proj = 'ctlv' + str(c) + ''.join('.2' for _ in range(j)) + ('.1' if j + 1 < len(ctl_next) else '')
            out.write(f'theorem ctlv{c}_{j} : readVar result{c} {v} = {trees[v]} := {proj}\n\n')
    # the output locations
    outs = [(node, kind, var, rot, ln) for (node, kind, var, rot, ln) in alloc_out if only_node < 0 or node == only_node]
    vids = [var_id(v) for (_, _, v, _, _) in outs]
    out.write('set_option maxRecDepth 100000 in\n')
    out.write('/-- The symbolic lanes at the output locations (one kernel evaluation of the slice). -/\n')
    out.write(f'theorem outs{c} : ' + ' ∧\n    '.join(f'readVar result{c} {v} = {trees[var_id(v)]}' for (_, _, v, _, _) in outs) + ' := by decide +kernel\n\n')
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        proj = 'outs' + str(c) + ''.join('.2' for _ in range(j)) + ('.1' if j + 1 < len(outs) else '')
        out.write(f'theorem out{c}_{j} : readVar result{c} {var} = {trees[vids[j]]} := {proj}\n\n')
    # invariants
    def inv_conj(alloc):
        return ' ∧\n  '.join(f'env {var} = (specQuantity (A {node}) {kind}).rotateLeft {rot}' for node, kind, var, rot, _ in alloc) or 'True'
    out.write(f'/-- What the locations hold at the start of slice {c} (for states `A n` of the nodes). -/\n')
    out.write(f'def Inv{c} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) : Prop :=\n  ' + inv_conj(alloc_in) +
              ''.join(f' ∧\n  {h}' for (_, _, h) in chyps) + '\n\n')
    out.write(f'/-- What the output locations hold after slice {c}. -/\n')
    out.write(f'def Out{c} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) : Prop :=\n  ' + inv_conj(outs) + '\n\n')
    hyp_all = [(i, h) for i, h in enumerate(alloc_in)]
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        tree = trees[vids[j]]
        used = set(int(x) for x in re.findall(r'\(\.var (\d+)\)', tree))
        hyps_n = [(i, h) for i, h in hyp_all if h[0] == node and var_id(h[2]) in used]
        hyps = ' '.join(f'(h{i} : env {var_} = (specQuantity (A {node_}) {kind_}).rotateLeft {rot_})' for i, (node_, kind_, var_, rot_, _) in hyps_n)
        hyps += ''.join(f' (c{i} : {h})' for i, (n_, _, h) in enumerate(chyps) if n_ == node)
        hnames = ' '.join(f'h{i}' for i, _ in hyps_n)
        at_h = f' at {hnames}' if hnames else ''
        out.write(f'''set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- {ln} -/
theorem lane{c}_{j} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) {hyps} :
    E.eval env (readVar result{c} {var}) = (specQuantity (Spec.round {round_in} (A {node})) {kind}).rotateLeft {rot} := by
  rw [out{c}_{j}]
  simp only [E.eval]
  {"simp only [specQuantity]" + at_h if hnames else "skip"}
  conv => rhs; simp +decide only [{SIMP_SPEC}]
  bv_decide

''')
    # the step theorem
    out.write(f'/-- Slice {c}: the invariant at its start gives the output invariant, for the next round\'s states. -/\n')
    out.write(f'theorem step{c} (env : Nat → BitVec 64) (A : Fin {count} → Spec.State) (h : Inv{c} env A) :\n')
    out.write(f'    Out{c} (fun i => E.eval env (readVar result{c} i)) (fun n => Spec.round {round_in} (A n)) := by\n')
    names = ' '.join(f'h{i}' for i, _ in hyp_all) + ''.join(f' c{i}' for i in range(len(chyps)))
    names = names.strip()
    if names:
        out.write(f'  obtain ⟨{", ".join(names.split())}⟩ := h\n')
    else:
        out.write('  clear h\n')
    parts = []
    for j, (node, kind, var, rot, ln) in enumerate(outs):
        tree = trees[vids[j]]
        used = set(int(x) for x in re.findall(r'\(\.var (\d+)\)', tree))
        hyps_n = [i for i, h in hyp_all if h[0] == node and var_id(h[2]) in used]
        parts.append(f'lane{c}_{j} env A ' + ' '.join(f'h{i}' for i in hyps_n) +
                     ''.join(f' c{i}' for i, (n_, _, _) in enumerate(chyps) if n_ == node))
    out.write('  exact ⟨' + ', '.join(parts) + '⟩\n\n')
    out.write(f'end Keccaktree.Kernels.{ns}\n')

def gen_final(ns, count, outdir):
    """The concrete-machine theorem: run the 24 slices from a state with the entry cut's control part."""
    with open(os.path.join(outdir, 'Final.lean'), 'w') as f:
        f.write(f'''import Keccaktree.Kernels.{ns}.Gen.Batch
import Keccaktree.Asm.Final
import Keccaktree.Asm.Node
/-! GENERATED: the batch on the concrete machine. -/
namespace Keccaktree.Kernels.{ns}
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak

/-- The slices of the batch. -/
def slices : Nat → List {ISA}.Instr
''' + ''.join(f'  | {c} => slice{c}\n' for c in range(24)) + '''  | _ => []

/-- The whole batch trace. -/
def batchTrace : List {ISA}.Instr := (List.range 24).foldr (fun c acc => slices c ++ acc) []

/-- The concrete states along the batch. -/
def stateAt (S0 : State (BitVec 64)) : Nat → State (BitVec 64)
  | 0 => S0
  | c + 1 => {ISA}.isa.execTrace rodata (slices c) (stateAt S0 c)

theorem stateAt_batch (S0 : State (BitVec 64)) : {ISA}.isa.execTrace rodata batchTrace S0 = stateAt S0 24 := by
  simp only [batchTrace, List.range, List.range.loop, List.foldr, Isa.execTrace, List.foldl_append]
  rfl

/-- Status of a concrete state at a cut. -/
def Ok (S : State (BitVec 64)) : Prop := S.err = false ∧ S.halted = false ∧ S.tail = none

''')
        # per step: from cutOf (stateAt c) = cut c, derive the next
        for c in range(24):
            nxt = c + 1 if c < 23 else None
            f.write(f'''theorem conc{c} (S0 : State (BitVec 64)) (hc : cutOf ctl{c} (stateAt S0 {c}) = cut{c}) (hs : Ok (stateAt S0 {c})) :
    envOf (stateAt S0 {c + 1}) = (fun i => E.eval (envOf (stateAt S0 {c})) (readVar result{c} i)) ∧
    Ok (stateAt S0 {c + 1})''' + (f' ∧ cutOf ctl{nxt} (stateAt S0 {c + 1}) = cut{nxt}' if nxt is not None else '') + f''' := by
  have hne : ({ISA}.isa.execTrace rodata slice{c} cut{c}).err = false := ctrl{c}.2.2.2.2.2.2.2.2.2.1
  have h1 := slice_concrete {ISA}.isa rodata slice{c} ctl{c} cut{c} (stateAt S0 {c}) hc hs hne
  have h2 := slice_ctrl {ISA}.isa rodata slice{c} ctl{c} cut{c} (stateAt S0 {c}) hc hs hne
  simp only at h2
  obtain ⟨hg, hk, hzf, hcf, hnf, hvf, hvl, hpc, hdepth, herr, hhalted, htail⟩ := h2
  have hctrl := ctrl{c}
  refine ⟨h1, ⟨?_, ?_, ?_⟩''' + (', ?_' if nxt is not None else '') + f'''⟩
  · show (stateAt S0 {c + 1}).err = false; simp only [stateAt, slices]; rw [herr]; exact hctrl.2.2.2.2.2.2.2.2.2.1
  · show (stateAt S0 {c + 1}).halted = false; simp only [stateAt, slices]; rw [hhalted]; exact hctrl.2.2.2.2.2.2.2.2.2.2.1
  · show (stateAt S0 {c + 1}).tail = none; simp only [stateAt, slices]; rw [htail]; exact hctrl.2.2.2.2.2.2.2.2.2.2.2
''')
            if nxt is not None:
                f.write(f'''  · show cutOf ctl{nxt} (stateAt S0 {c + 1}) = cutOf ctl{nxt} sc{nxt}
    apply cutOf_eq_of_ctrl
    · simp only [stateAt, slices]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hg, hctrl.1]; rfl
      · rw [hk, hctrl.2.1]; rfl
      · rw [hzf, hctrl.2.2.1]; rfl
      · rw [hcf, hctrl.2.2.2.1]; rfl
      · rw [hnf, hctrl.2.2.2.2.1]; rfl
      · rw [hvf, hctrl.2.2.2.2.2.1]; rfl
      · rw [hvl, hctrl.2.2.2.2.2.2.1]; rfl
      · rw [hpc, hctrl.2.2.2.2.2.2.2.1]; rfl
      · rw [hdepth, hctrl.2.2.2.2.2.2.2.2.1]; rfl
''')
                ctln = CTLS[nxt]
                if not ctln:
                    f.write(f'    · intro i hi; simp only [ctl{nxt}, List.mem_nil_iff] at hi\n')
                else:
                    f.write(f'    · intro i hi\n      simp only [ctl{nxt}, List.mem_cons, List.mem_nil_iff, or_false] at hi\n')
                    f.write('      rcases hi with ' + ' | '.join('rfl' for _ in ctln) + '\n')
                    for j, v in enumerate(ctln):
                        f.write(f'      · simp only [h1, ctlv{c}_{j}, E.eval]; decide +kernel\n')
            f.write('\n')
        f.write(f'''/-- The cut environment after the batch is the chained symbolic one. -/
theorem env_chain (S0 : State (BitVec 64)) (hc : cutOf ctl0 S0 = cut0) (hs : Ok S0) :
    envOf (stateAt S0 24) = envAt (envOf S0) 24 := by
  have c0 := conc0 S0 hc hs
''' + ''.join(f'  have c{c} := conc{c} S0 c{c - 1}.2.2 c{c - 1}.2.1\n' for c in range(1, 24)) + '''  simp only [envAt]
''' + ''.join(f'  rw [← c{c}.1]\n' for c in range(23, -1, -1)) + f'''
/-- **The batch on the concrete machine**: from any concrete state at the
batch entry with the entry cut's control part (`hc`) whose input locations
hold the nodes' words (`Inv0`), the output locations after the batch hold
the digest lanes of `Spec.rounds 24` of every node. -/
theorem batch_correct (S0 : State (BitVec 64)) (A : Fin {count} → Spec.State)
    (hc : cutOf ctl0 S0 = cut0) (hs : Ok S0) (h0 : Inv0 (envOf S0) A) :
    Out23 (envOf ({ISA}.isa.execTrace rodata batchTrace S0)) (fun n => Spec.rounds 24 (A n)) := by
  rw [stateAt_batch, env_chain S0 hc hs]
  exact chain (envOf S0) A h0

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
    slices = [int(x) for x in slices.split(',')] if slices else list(range(24))
    # step boundaries: state after n steps
    bounds = [entry_t] + [t + 1 for t in cuts] + [end_t]   # bounds[c] = start of slice c; bounds[c+1] = its end (the batch ret excluded)
    # pass 1: the control words of every slice, united
    CTLS.update(find_ctls(kernel, count, bounds))
    print(f'control words per slice: {[CTLS[c] for c in range(24)]}', file=sys.stderr)
    for c in slices:
        a, b = bounds[c], bounds[c + 1]
        if c == 0:
            # input words, as lanes 0..7 of the round-0 states, plus the padding lanes as constants
            alloc_in = []
            for n in range(count):
                for w in range(8):
                    alloc_in.append((n, w, f'(memVar 1 ({8 * n + w}))', 0, f'input word {w} of node {n}'))
            alloc_out = matches(kernel, count, b, lanes, 1)
        else:
            alloc_in = matches(kernel, count, a, lanes, c)
            if c == 23:
                alloc_out = matches(kernel, count, b, lanes, 24, region_filter=2)
            else:
                alloc_out = matches(kernel, count, b, lanes, c + 1)
        if only_node >= 0:
            alloc_in = [h for h in alloc_in if h[0] == only_node]
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

/-- **The batch computes Keccak-f[1600] on every node**: if the input words
are in place at the batch entry (`Inv0`), the output locations after the
24 slices hold the digest lanes of `Spec.rounds 24` of each node's state. -/
theorem chain (env0 : Nat → BitVec 64) (A : Fin {count} → Spec.State) (h0 : Inv0 env0 A) :
    Out23 (envAt env0 24) (fun n => Spec.rounds 24 (A n)) := by
''' + '  have h1 := step0 env0 A h0\n' + ''.join(f'  have h{c + 1} := step{c} _ _ h{c}\n' for c in range(1, 24)) +
            f'''  simp only [envAt] at h24 ⊢
  simp only [Spec.rounds, Spec.memo_eq]
  exact h24

end Keccaktree.Kernels.{ns}
''')

if __name__ == '__main__':
    main()
