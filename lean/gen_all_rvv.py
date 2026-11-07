#!/usr/bin/env python3
"""Emit Keccaktree/Kernels/<Ns>/All.lean: the every-count theorem of an RVV kernel configuration,
from its body variants GenB1..GenB<V> (gen_segments_rvv.sh) and the frame lemmas of RvvCommon.

    gen_all_rvv.py <kernel> <Ns> <ProgNs> <V> <s> <L>
      s = instruction index of `sub a2, a2, t0` (380 rvv, 237 rvv_zvkb), L = body length (steps)
"""
import os, re, sys

kernel, ns, pns, V, s, L = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
root = os.path.dirname(os.path.abspath(__file__))
kdir = os.path.join(root, 'Keccaktree', 'Kernels', ns)
P = L + 6  # steps per batch
base = kernel.rsplit('_v', 1)[0]            # rvv / rvv_zvkb (the symbol; one program for every VLEN)
entsel = {'rvv': '2.2.1', 'rvv_zvkb': '2.2.2'}[base]

SQ = ('specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv, '
      'Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0')


def conjuncts(w, name):
    src = open(os.path.join(kdir, f'GenB{w}', 'Invs.lean')).read()
    m = re.search(r'^def ' + name + r' \(env.*?:= *\n(.*?)\n\n', src, re.S | re.M)
    body = m.group(1)
    return [c.strip() for c in body.split(' ∧\n')]


def ctl0(w):
    src = open(os.path.join(kdir, f'GenB{w}', 'Slice0.lean')).read()
    return [int(x) for x in re.search(r'^def ctl0 : List Nat := \[(.*?)\]', src, re.M).group(1).split(',')]


def inv0_proof(w):
    out = []
    for c in conjuncts(w, 'Inv0'):
        m = re.match(r'env \(memVar rInput \(Int\.ofNat \(8 \* (\d+) \+ (\d+)\)\)\) = \(specQuantity \(A (\d+)\) (\d+)\)\.rotateLeft 0$', c)
        if m:
            n, j, n2, k = map(int, m.groups())
            assert n == n2 and j == k, c
            out.append(f'''  · show envOf S ((rho m).var (memVar rInput (Int.ofNat (8 * {n} + {j})))) = _
    rw [env_in input S m {n} {j} hin]
    show nodeWords input (m + {n}) {j} = (specQuantity (absorbNode (nodeWords input (m + {n}))) {j}).rotateLeft 0
    simp only [{SQ}, absorbNode_lane{j}]''')
            continue
        m = re.match(r'L \(A (\d+)\) (\d+) = (.*)$', c)
        assert m, c
        n, k = int(m.group(1)), int(m.group(2))
        out.append(f'''  · show L (absorbNode (nodeWords input (m + {n}))) {k} = _
    exact absorbNode_lane{k} _''')
    return len(conjuncts(w, 'Inv0')), '\n'.join(out)


def out_facts(w):
    """(node, word) of each conjunct of Inv25"""
    res = []
    for c in conjuncts(w, 'Inv25'):
        m = re.match(r'env \(memVar rOutput \(Int\.ofNat \(4 \* (\d+) \+ (\d+)\)\)\) = \(specQuantity \(A (\d+)\) (\d+)\)\.rotateLeft 0$', c)
        assert m, c
        n, j, n2, k = map(int, m.groups())
        assert n == n2 and j == k, c
        res.append((n, j))
    return res


def ctl_case(w, v):
    if v == 261:
        return f'''      · -- t0 = vl
        rw [cutVar_const_of GenB{w}.ctl0 H 261 _ (by decide) ((envOf_gdVar H 5 (by decide)).trans hf5) (by decide +kernel),
          show cutVar GenB{w}.ctl0 GenB{w}.sc0 261 = .const (BitVec.ofNat 64 {w}) by decide +kernel, rho_const]'''
    if v == 266:
        return f'''      · -- a0
        rw [cutVar_ptr_of GenB{w}.ctl0 H 266 ⟨rOutput, 32 * ((off + j : Nat) : Int)⟩ (by decide)
            ((hHenv 266 (by decide) (by decide)).trans ((envOf_gdVar S 10 (by decide)).trans hM.a0)) hwf_out (by show rOutput ≠ 0; decide),
          show cutVar GenB{w}.ctl0 GenB{w}.sc0 266 = .ptr ⟨rOutput, 0⟩ by decide +kernel, reloc_ptr_out, Int.zero_add]'''
    if v == 267:
        return f'''      · -- a1
        rw [cutVar_ptr_of GenB{w}.ctl0 H 267 ⟨rInput, 64 * ((off + j : Nat) : Int)⟩ (by decide)
            ((hHenv 267 (by decide) (by decide)).trans ((envOf_gdVar S 11 (by decide)).trans hM.a1)) hwf_in (by show rInput ≠ 0; decide),
          show cutVar GenB{w}.ctl0 GenB{w}.sc0 267 = .ptr ⟨rInput, 0⟩ by decide +kernel, reloc_ptr_in, Int.zero_add]'''
    if v == 273:
        return f'''      · -- a7 = 0
        rw [cutVar_const_of GenB{w}.ctl0 H 273 0#64 (by decide) ((hHenv 273 (by decide) (by decide)).trans ((envOf_gdVar S 17 (by decide)).trans hM.a7))
            (by decide +kernel),
          show cutVar GenB{w}.ctl0 GenB{w}.sc0 273 = .const 0#64 by decide +kernel, rho_const]'''
    if v == 286:
        return f'''      · -- t5 = 1 << 63
        rw [cutVar_const_of GenB{w}.ctl0 H 286 0x8000000000000000#64 (by decide)
            ((hHenv 286 (by decide) (by decide)).trans ((envOf_gdVar S 30 (by decide)).trans hM.t5)) (by decide +kernel),
          show cutVar GenB{w}.ctl0 GenB{w}.sc0 286 = .const 0x8000000000000000#64 by decide +kernel, rho_const]'''
    raise SystemExit(f'GenB{w}: unexpected start control word {v}')


def runch(w, K=25):
    at = lambda c: 'H' if c == 0 else f'(GenB{w}.segAt{c} H)'
    L = [f'  have hrunch : (RVc ch).run rodata prog GenB{w}.segLen H = GenB{w}.segAt{K} H := by',
         f'    have s0 := (GenB{w}.cert0).step (rho (off + j)) hρ hw0 H hc0 hHok']
    for c in range(1, K):
        L.append(f'    have s{c} := (GenB{w}.cert{c}).step (rho (off + j)) hρ hw0 {at(c)} s{c - 1}.2.2.2 s{c - 1}.2.2.1')
    L.append(f'    show (RVc ch).run rodata prog (' + ' + '.join(f'(GenB{w}.cert{c}).idx.length' for c in range(K)) + ') H = _')
    L.append('    repeat rw [Isa.run_add]')
    parts = []
    for c in range(K):
        hc = 'hc0 hHok' if c == 0 else f's{c - 1}.2.2.2 s{c - 1}.2.2.1'
        parts.append(f'(GenB{w}.cert{c}).run_ch ch (by decide +kernel) (rho (off + j)) hρ hw0 {at(c)} {hc}, s{c}.1, '
                     f'show (Riscv.isa {V}).execTrace rodata (GenB{w}.cert{c}).slice {at(c)} = GenB{w}.segAt{c + 1} H from rfl')
    L.append('    rw [' + ',\n      '.join(parts) + ']')
    return '\n'.join(L)


def batch(w):
    c0 = ctl0(w)
    ninv, inv0 = inv0_proof(w)
    outs = out_facts(w)
    nouts = len(outs)
    names = ', '.join(f'o{i}' for i in range(nouts))
    node_digests = []
    for n in range(w):
        idx = {j: i for i, (n_, j) in enumerate(outs) if n_ == n}
        assert sorted(idx) == [0, 1, 2, 3], (w, n, idx)
        cases = '\n'.join(f'''      · have := o{idx[j]}; dsimp only at this; rw [env_out Sb m {n} {j}] at this; simp only [{SQ}] at this; rw [this]; exact congrArg (fun X => L X {j}) (GenB{w}.aat_{n} _)''' for j in range(4))
        node_digests.append(f'''    have d{n} : Digest input Sb (m + {n}) := by
      apply digest_of
      intro t ht
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
{cases}''')
    alts = ' ∨ '.join(f'n - j = {i}' for i in range(w))
    pats = ' | '.join('h' for _ in range(w))
    dig_cases = '\n'.join(f'''      · have e : off + n = m + {i} := by omega
        rw [e]; exact digest_congr input Sb U _ (fun t _ => by rw [hUmem]) d{i}''' for i in range(w))
    return f'''
/-! ### The batch with `vl = {w}` -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The body's input invariant at node `m`, from the message (`{w}` nodes). -/
theorem inv0_{w} (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat) (hin : ∀ q, S.mem rInput q = input q) :
    GenB{w}.Inv0 (fun i => envOf S ((rho m).var i)) (fun n => absorbNode (nodeWords input (m + n.val))) := by
  refine ⟨{', '.join('?_' for _ in range(ninv))}⟩
{inv0}

theorem body_len{w} : GenB{w}.segLen = {L} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **A batch of `{w}` node(s)** (`vl = {w}`): from the loop head after `j` nodes with `min (c - j) {V} = {w}`,
`{P}` steps (head, body, back edge) hash nodes `off + j .. off + j + {w - 1}` and reach the loop head
after `j + {w}` nodes, or the exit if none is left. -/
theorem batch{w} (ch : Nat → Nat) (off c : Nat) (input : Int → BitVec 64) (S0 S : State (BitVec 64)) (j : Nat)
    (hb : 64 * (off + c) ≤ 2 ^ 54) (hM : Mid off c input S0 S j 7) (hj : j + {w} ≤ c) (hw : ch (c - j) = {w}) :
    Mid off c input S0 ((RVc ch).run rodata prog {P} S) (j + {w}) (if c - j - {w} = 0 then {s + 2} else 7) := by
  have hb' : 64 * (off + c) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hr0 : 0 ≤ (c : Int) - j := by omega
  have hr1 : (c : Int) - j < 2 ^ 55 := by rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; omega
  have hwf_in : (⟨rInput, 64 * ((off + j : Nat) : Int)⟩ : Addr).wf := by
    show 0 ≤ 64 * ((off + j : Nat) : Int) ∧ 64 * ((off + j : Nat) : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hwf_out : (⟨rOutput, 32 * ((off + j : Nat) : Int)⟩ : Addr).wf := by
    show 0 ≤ 32 * ((off + j : Nat) : Int) ∧ 32 * ((off + j : Nat) : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  -- head: `mv t3, a2; beqz a7; vsetvli; bnez a7`
  have ht : ((c : Int) - j).toNat = c - j := by omega
  have hhd := run_head {V} ch rodata prog prog_7 prog_8 prog_12 prog_13 S ((c : Int) - j) hM.ok.2.1 hM.ctrl.2.2.2.2.2.2.1
    hM.a2 hM.a7 hr0 hr1 (by rw [ht, hw]; omega)
  rw [ht, hw] at hhd
  have hf := H4_facts {w} S ((c : Int) - j)
  have hHenv : ∀ i, i ≠ 261 → i ≠ 284 → envOf (H4 {w} S ((c : Int) - j)) i = envOf S i := fun i a b => H4_env _ _ _ i a b
  generalize hH : H4 {w} S ((c : Int) - j) = H at hhd hf hHenv
  obtain ⟨hf14, hfvl, hf5, hfg, hfk, hfz, hfc, hfn, hfv, hfd, hfh, hfe, hft, hfm⟩ := hf
  have hHok : SliceCert.Ok H := ⟨hfe.trans hM.ok.1, hfh.trans hM.ok.2.1, hft.trans hM.ok.2.2⟩
  have hHin : ∀ q, H.mem rInput q = input q := fun q => by rw [hfm]; exact hM.inp q
  -- the body's start cut, at node `off + j`
  have hρ := rho_ok (off + j)
  have hc0 : relocState (rho (off + j)) (cutOf GenB{w}.ctl0 GenB{w}.sc0) = cutOf GenB{w}.ctl0 H := by
    apply relocState_cutOf
    · intro i hi
      simp only [GenB{w}.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with {' | '.join('rfl' for _ in c0)}
{chr(10).join(ctl_case(w, v) for v in c0)}
    · intro i hi h; simp only [GenB{w}.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
    · obtain ⟨cg, ck, cz, cc, cn, cv, _, cd⟩ := hM.ctrl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfg, cg]; decide +kernel
      · rw [hfk, ck]; decide +kernel
      · rw [hfz, cz]; decide +kernel
      · rw [hfc, cc]; decide +kernel
      · rw [hfn, cn]; decide +kernel
      · rw [hfv, cv]; decide +kernel
      · rw [hfvl]; decide +kernel
      · rw [hf14]; decide +kernel
      · rw [hfd, cd]; decide +kernel
  -- the body
  have hw0 : (rho (off + j)).within GenB{w}.B := rho_within (off + j) (by omega)
  have sr := GenB{w}.seg_run (rho (off + j)) hρ hw0 H hc0 hHok
  have fr := GenB{w}.seg_frame (rho (off + j)) hρ hw0 H hc0 hHok
  have dat := GenB{w}.seg_data (rho (off + j)) hρ hw0 H hc0 hHok _ (inv0_{w} input H (off + j) hHin)
  have mv := GenB{w}.seg_moves (rho (off + j)) hρ hw0 H hc0 hHok 268 268 (by simp)
  -- the body under the choice `ch`: the same run (no `vsetvli` on its path)
{runch(w)}
  generalize hSb : GenB{w}.segAt25 H = Sb at sr fr dat mv hrunch
  obtain ⟨hrun, hokb, hcutb⟩ := sr
  have fb := cut_fields _ _ _ _ hcutb
  have word : ∀ v, v ∈ GenB{w}.ctl25 → v < 288 → cutVar GenB{w}.ctl25 Sb v = E.reloc (rho (off + j)) (cutVar GenB{w}.ctl25 GenB{w}.sc25 v) :=
    fun v _ hv => cut_word (rho (off + j)) hρ GenB{w}.ctl25 GenB{w}.sc25 Sb hcutb v (Or.inl hv)
  have hb5 : Sb.getGD 5 = BitVec.ofNat 64 {w} := by
    have e1 := word 261 (by decide) (by decide)
    rw [show cutVar GenB{w}.ctl25 GenB{w}.sc25 261 = .const (BitVec.ofNat 64 {w}) by decide +kernel, rho_const] at e1
    rw [← envOf_gdVar Sb 5 (by decide)]; exact cut_const _ Sb 261 (by decide) _ e1
  have hb17 : Sb.getGD 17 = 0#64 := by
    have e1 := word 273 (by decide) (by decide)
    rw [show cutVar GenB{w}.ctl25 GenB{w}.sc25 273 = .const 0#64 by decide +kernel, rho_const] at e1
    rw [← envOf_gdVar Sb 17 (by decide)]; exact cut_const _ Sb 273 (by decide) _ e1
  have hb30 : Sb.getGD 30 = 0x8000000000000000#64 := by
    have e1 := word 286 (by decide) (by decide)
    rw [show cutVar GenB{w}.ctl25 GenB{w}.sc25 286 = .const 0x8000000000000000#64 by decide +kernel, rho_const] at e1
    rw [← envOf_gdVar Sb 30 (by decide)]; exact cut_const _ Sb 286 (by decide) _ e1
  have hb10 : Sb.getGD 10 = gprWord ⟨rOutput, 32 * ((off + (j + {w}) : Nat) : Int)⟩ := by
    have e1 := word 266 (by decide) (by decide)
    rw [show cutVar GenB{w}.ctl25 GenB{w}.sc25 266 = .ptr ⟨rOutput, {32 * w}⟩ by decide +kernel, reloc_ptr_out] at e1
    rw [← envOf_gdVar Sb 10 (by decide), cut_ptr _ Sb 266 (by decide) _ e1]
    exact congrArg (fun z : Int => gprWord ⟨rOutput, z⟩) (by omega)
  have hb11 : Sb.getGD 11 = gprWord ⟨rInput, 64 * ((off + (j + {w}) : Nat) : Int)⟩ := by
    have e1 := word 267 (by decide) (by decide)
    rw [show cutVar GenB{w}.ctl25 GenB{w}.sc25 267 = .ptr ⟨rInput, {64 * w}⟩ by decide +kernel, reloc_ptr_in] at e1
    rw [← envOf_gdVar Sb 11 (by decide), cut_ptr _ Sb 267 (by decide) _ e1]
    exact congrArg (fun z : Int => gprWord ⟨rInput, z⟩) (by omega)
  have hb12 : Sb.getGD 12 = gprWord ⟨0, (c : Int) - j⟩ := by
    rw [Reloc.var_lt _ 268 (by decide)] at mv
    rw [← envOf_gdVar Sb 12 (by decide), mv, hHenv 268 (by decide) (by decide), envOf_gdVar S 12 (by decide), hM.a2]
  have hpcb : Sb.pc = {s} := fb.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  -- back edge: `sub a2, a2, t0; bnez a2, 7`
  have htl := run_tail {V} ch rodata prog {s} prog_{s} prog_{s + 1} Sb ((c : Int) - j) {w} hokb.2.1 hpcb hb12 hb5 (by omega)
    (by rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; omega)
  have hUf := T2_facts Sb ((c : Int) - j) {w}
  have hUg : ∀ n, n ≠ 12 → (T2 Sb ((c : Int) - j) {w}).getGD n = Sb.getGD n := fun n hn => T2_getGD _ _ _ n hn
  have hUpc := T2_pc Sb ((c : Int) - j) {w} {s} hpcb
  generalize hU : T2 Sb ((c : Int) - j) {w} = U at htl hUf hUg hUpc
  obtain ⟨hU12, hUg', hUk, hUz, hUc, hUn, hUv, hUd, hUh, hUe, hUt, hUmem⟩ := hUf
  have hrunall : (RVc ch).run rodata prog {P} S = U := by
    rw [show {P} = 4 + GenB{w}.segLen + 2 by rw [body_len{w}], Isa.run_add, Isa.run_add, hhd, hrunch, htl]
  rw [hrunall]
  obtain ⟨g1, k1, z1, c1, n1, v1, _, _, d1⟩ := fb
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hUe.trans hokb.1, hUh.trans hokb.2.1, hUt.trans hokb.2.2⟩,
    (hUg 10 (by decide)).trans hb10, (hUg 11 (by decide)).trans hb11, ?_, (hUg 17 (by decide)).trans hb17,
    (hUg 30 (by decide)).trans hb30, ?_, ?_, ?_⟩
  · rw [hUg', g1]; decide +kernel
  · rw [hUk, k1]; decide +kernel
  · rw [hUz, z1]; decide +kernel
  · rw [hUc, c1]; decide +kernel
  · rw [hUn, n1]; decide +kernel
  · rw [hUv, v1]; decide +kernel
  · rw [hUpc]
    by_cases hz : c - j - {w} = 0
    · rw [if_pos (by omega), if_pos hz]
    · rw [if_neg (by omega), if_neg hz]
  · rw [hUd, d1]; decide +kernel
  · rw [hU12]; exact congrArg (fun z : Int => gprWord ⟨0, z⟩) (by omega)
  · intro q; rw [hUmem, fr rInput q rfl]; exact hHin q
  · intro q hq
    rw [hUmem, fr rOutput q (by
      rw [rho_wshift_out]
      show (rOutput == 2 && decide (0 ≤ q - 4 * ((off + j : Nat) : Int)) && decide (q - 4 * ((off + j : Nat) : Int) < {4 * w})) = false
      rw [show decide (0 ≤ q - 4 * ((off + j : Nat) : Int)) = false from decide_eq_false (by omega)]; rfl), hfm]
    exact hM.pre q hq
  · obtain ⟨{names}⟩ := dat
{chr(10).join(node_digests).replace('(m + ', '(off + j + ').replace('env_out Sb m ', 'env_out Sb (off + j) ')}
    intro n hn
    by_cases hnj : n < j
    · apply digest_congr input S U (off + n) _ (hM.dig n hnj)
      intro t ht
      rw [hUmem, fr rOutput _ (by
        rw [rho_wshift_out]
        show (rOutput == 2 && decide (0 ≤ (Int.ofNat (4 * (off + n) + t)) - 4 * ((off + j : Nat) : Int)) &&
          decide ((Int.ofNat (4 * (off + n) + t)) - 4 * ((off + j : Nat) : Int) < {4 * w})) = false
        rw [show decide (0 ≤ (Int.ofNat (4 * (off + n) + t)) - 4 * ((off + j : Nat) : Int)) = false from
          decide_eq_false (by simp only [Int.ofNat_eq_coe]; omega)]; rfl), hfm]
    · rcases (show {alts} by omega) with {pats}
{dig_cases.replace('m + ', 'off + j + ')}
'''


def main():
    parts = []
    imports = ''.join(f'import Keccaktree.Kernels.{ns}.GenB{w}.Seg\n' for w in range(1, V + 1))
    parts.append(f'''{imports}import Keccaktree.Kernels.RvvCommon
import Keccaktree.Kernels.RvVl
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_{kernel.rsplit('_v', 1)[0]}` at VLEN = {64 * V} (`VLMAX = {V}`) on any number of nodes

GENERATED by lean/gen_all_rvv.py; do not edit.  The frame is `RvvCommon`; a batch with `vl = w`
(`w = min(r, {V})` for `r` nodes left) runs the body variant `GenB<w>` (proved once, symbolically, at
every relocated position).  `{P}` steps per batch; the loop is an induction over the batches.

**Result** (`all`): for every count `c` and node offset `off` with `64·(off+c) ≤ 2^54`, from an entry
state (`RvvCommon.Entry`: node-aligned buffers), `8 + {P}·⌈c/{V}⌉` steps halt without a model fault
and without a tail call, keep the output words before node `off`, and leave the keccak256 digest of
input node `off+n` in output words `4(off+n) ..`, for every `n < c`.  Assumes `vsetvli` picks
`vl = min(avl, VLMAX)` (see `RvvCommon`).
-/
namespace Keccaktree.Kernels.{ns}.All
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon Keccaktree.Kernels.RvvCommon
open Keccaktree.Asm.Riscv (setR getR brHolds cutVar_const_of)
open Keccaktree.Kernels.{pns} (prog rodata)

abbrev RV : Isa := Riscv.isa {V}

/-- The instruction set with the vector-length choice `ch` at `vsetvli`. -/
abbrev RVc (ch : Nat → Nat) : Isa := Riscv.isaCh {V} ch

theorem prog_1 : prog.getD 1 .nop = .br .eq 12 0 ({s} + 3) := by decide +kernel
theorem prog_2 : prog.getD 2 .nop = .opi 2 2 .addi 0xfffffffffffffe00#64 := by decide +kernel
theorem prog_3 : prog.getD 3 .nop = .li 30 0x1#64 := by decide +kernel
theorem prog_4 : prog.getD 4 .nop = .opi 30 30 .slli 0x3f#64 := by decide +kernel
theorem prog_5 : prog.getD 5 .nop = .op 17 10 11 .or := by decide +kernel
theorem prog_6 : prog.getD 6 .nop = .opi 17 17 .andi 0x7#64 := by decide +kernel
theorem prog_7 : prog.getD 7 .nop = .mv 28 12 := by decide +kernel
theorem prog_8 : prog.getD 8 .nop = .br .eq 17 0 12 := by decide +kernel
theorem prog_12 : prog.getD 12 .nop = .vsetvli 5 28 := by decide +kernel
theorem prog_13 : prog.getD 13 .nop = .br .ne 17 0 16 := by decide +kernel
theorem prog_{s} : prog.getD {s} .nop = .op 12 12 5 .sub := by decide +kernel
theorem prog_{s + 1} : prog.getD ({s} + 1) .nop = .br .ne 12 0 7 := by decide +kernel
theorem prog_{s + 2} : prog.getD ({s} + 2) .nop = .opi 2 2 .addi 0x200#64 := by decide +kernel
theorem prog_{s + 3} : prog.getD ({s} + 3) .nop = .ret := by decide +kernel
''')
    only = os.environ.get('ONLY_W')
    ws = [int(x) for x in only.split(',')] if only else list(range(1, V + 1))
    for w in ws:
        parts.append(batch(w))
    if only:
        parts[0] = ''.join(f'import Keccaktree.Kernels.{ns}.GenB{w}.Seg\n' for w in ws) + parts[0].split('import Keccaktree.Kernels.RvvCommon', 1)[0].split('\n', V)[-1] * 0 + 'import Keccaktree.Kernels.RvvCommon' + parts[0].split('import Keccaktree.Kernels.RvvCommon', 1)[1]
        parts.append(f'\nend Keccaktree.Kernels.{ns}.All\n')
        with open(os.path.join(kdir, 'AllPart.lean'), 'w') as f:
            f.write(''.join(parts).replace(f'namespace Keccaktree.Kernels.{ns}.All', f'namespace Keccaktree.Kernels.{ns}.AllPart').replace(f'end Keccaktree.Kernels.{ns}.All', f'end Keccaktree.Kernels.{ns}.AllPart'))
        return
    cases = '\n'.join(f'  · exact batch{w} ch off c input S0 S j hb hM (by omega) hwc' for w in range(1, V + 1))
    parts.append(f"""
/-! ## The loop -/

/-- A batch of any width `w = ch (c - j)`. -/
theorem batch_any (ch : Nat → Nat) (off c : Nat) (input : Int → BitVec 64) (S0 S : State (BitVec 64)) (j w : Nat)
    (hb : 64 * (off + c) ≤ 2 ^ 54) (hM : Mid off c input S0 S j 7) (hw1 : 1 ≤ w) (hw2 : w ≤ {V}) (hj : j + w ≤ c)
    (hwc : ch (c - j) = w) :
    Mid off c input S0 ((RVc ch).run rodata prog {P} S) (j + w) (if c - j - w = 0 then {s + 2} else 7) := by
  rcases (show {' ∨ '.join(f'w = {w}' for w in range(1, V + 1))} by omega) with {' | '.join('rfl' for _ in range(V))}
{cases}

/-- The number of batches for `r` nodes left under the choice `ch` (fuel `f ≥ r`). -/
def nb (ch : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, r => if r = 0 then 0 else 1 + nb ch f (r - ch r)

theorem nb_zero (ch : Nat → Nat) (f : Nat) : nb ch f 0 = 0 := by cases f <;> rfl

/-- **The loop under any legal choice**: from the loop head after `j < c` nodes, `nb ch f (c - j)` batches
(fuel `f ≥ c - j`) reach the exit with every node done. -/
theorem loop (ch : Nat → Nat) (hch : Riscv.LegalVl {V} ch) (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64))
    (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ f j (S : State (BitVec 64)), Mid off c input S0 S j 7 → j < c → c - j ≤ f →
      Mid off c input S0 ((RVc ch).run rodata prog ({P} * nb ch f (c - j)) S) c {s + 2} := by
  intro f
  induction f with
  | zero => intro j S hM h1 h2; omega
  | succ f ih =>
    intro j S hM h1 h2
    obtain ⟨b1, b2, b3⟩ := hch.bounds (by decide) (c - j) (by omega)
    have hstep := batch_any ch off c input S0 S j (ch (c - j)) hb hM b1 b3 (by omega) rfl
    have hnb : nb ch (f + 1) (c - j) = 1 + nb ch f (c - j - ch (c - j)) := by
      show (if c - j = 0 then 0 else 1 + nb ch f (c - j - ch (c - j))) = _
      rw [if_neg (by omega)]
    rw [hnb, show {P} * (1 + nb ch f (c - j - ch (c - j))) = {P} + {P} * nb ch f (c - j - ch (c - j)) by omega, Isa.run_add]
    by_cases hz : c - j - ch (c - j) = 0
    · rw [if_pos hz, show j + ch (c - j) = c by omega] at hstep
      rw [hz, nb_zero, Nat.mul_zero, show (RVc ch).run rodata prog 0 _ = _ from rfl]
      exact hstep
    · rw [if_neg hz] at hstep
      rw [show c - j - ch (c - j) = c - (j + ch (c - j)) by omega]
      exact ih (j + ch (c - j)) _ hstep (by omega) (by omega)

theorem nb_min : ∀ f r, r ≤ f → nb (fun a => min a {V}) f r = (r + {V - 1}) / {V} := by
  intro f
  induction f with
  | zero => intro r h; rw [show r = 0 by omega]; rfl
  | succ f ih =>
    intro r h
    show (if r = 0 then 0 else 1 + nb (fun a => min a {V}) f (r - min r {V})) = _
    by_cases hr : r = 0
    · rw [if_pos hr, hr]
    · rw [if_neg hr, ih _ (by omega)]
      omega

/-! ## The whole call -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The kernel on any number of nodes, under any legal vector-length choice** (RVV 1.0 §6.3). -/
theorem all_ch (ch : Nat → Nat) (hch : Riscv.LegalVl {V} ch) (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ((RVc ch).run rodata prog (8 + {P} * nb ch c c) S).halted = true ∧
    ((RVc ch).run rodata prog (8 + {P} * nb ch c c) S).err = false ∧
    ((RVc ch).run rodata prog (8 + {P} * nb ch c c) S).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → ((RVc ch).run rodata prog (8 + {P} * nb ch c c) S).mem rOutput q = S.mem rOutput q) ∧
    ∀ n, n < c → Digest input ((RVc ch).run rodata prog (8 + {P} * nb ch c c) S) (off + n) := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have h0 := entry_zero {V} ch rodata prog {s} prog_1 prog_{s + 3} off input S hE
    rw [nb_zero, Nat.mul_zero, show 8 + 0 = 2 + 6 from rfl, Isa.run_add, h0, Isa.run_halted _ _ _ _ _ rfl]
    exact ⟨rfl, hE.ok.1, hE.ok.2.2, fun q _ => rfl, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  · have hM0 := entry_pos {V} ch rodata prog {s} prog_1 prog_2 prog_3 prog_4 prog_5 prog_6 off c input S hE hc hb
    have hl := loop ch hch off c input S hb c 0 _ hM0 hc (by omega)
    rw [Nat.sub_zero] at hl
    generalize hX : (RVc ch).run rodata prog ({P} * nb ch c c) ((RVc ch).run rodata prog 6 S) = X at hl
    have hx := run_exit {V} ch rodata prog {s} prog_{s + 2} prog_{s + 3} X hl.ok.2.1 hl.ctrl.2.2.2.2.2.2.1
    rw [show 8 + {P} * nb ch c c = 6 + {P} * nb ch c c + 2 by omega, Isa.run_add, Isa.run_add, hX, hx]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · simp only [Riscv.next_err, Riscv.setR_err]; exact hl.ok.1
    · simp only [Riscv.next_tail, Riscv.setR_tail]; exact hl.ok.2.2
    · intro q hq; simp only [Riscv.next_mem, Riscv.setR_mem']; exact hl.pre q hq
    · intro n hn
      exact digest_congr input X _ _ (fun t _ => by simp only [Riscv.next_mem, Riscv.setR_mem']) (hl.dig n hn)

/-- **The kernel on any number of nodes** (the deterministic model `Riscv.isa {V}`: `vl = min(avl, {V})`),
`8 + {P}·⌈c/{V}⌉` steps. -/
theorem all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (hE : Entry off c input S)
    (hb : 64 * (off + c) ≤ 2 ^ 54) :
    (RV.run rodata prog (8 + {P} * ((c + {V - 1}) / {V})) S).halted = true ∧
    (RV.run rodata prog (8 + {P} * ((c + {V - 1}) / {V})) S).err = false ∧
    (RV.run rodata prog (8 + {P} * ((c + {V - 1}) / {V})) S).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (RV.run rodata prog (8 + {P} * ((c + {V - 1}) / {V})) S).mem rOutput q = S.mem rOutput q) ∧
    ∀ n, n < c → Digest input (RV.run rodata prog (8 + {P} * ((c + {V - 1}) / {V})) S) (off + n) := by
  have h := all_ch (fun a => min a {V}) (Riscv.legal_min {V}) off c input S hE hb
  rw [nb_min c c (Nat.le_refl c), Riscv.run_min] at h
  exact h

/-! ## In the library -/

/-- What the library needs (`LibRv.NormThmRv`), deterministic model. -/
theorem norm_thm : LibRv.NormThmRv {V} rodata prog 1 (fun _ c => 8 + {P} * ((c + {V - 1}) / {V})) [] := by
  intro off count input S hE hb hpc
  obtain ⟨⟨g, k, z, cf, n, v, _, d⟩, hok, ha2, _, ha1, ha0, hin⟩ := hE
  have hE' : Entry off count input S := ⟨⟨g, k, z, cf, n, v, hpc, d⟩, hok, ha2, ha1, ha0, hin⟩
  obtain ⟨hh, he, ht, hp, hd⟩ := all off count input S hE' hb
  exact ⟨hh, he, hp, Or.inl ⟨ht, hd⟩⟩

/-- What the library needs under any legal choice (`LibRv.NormThmRvCh`). -/
theorem norm_thm_ch (ch : Nat → Nat) (hch : Riscv.LegalVl {V} ch) :
    LibRv.NormThmRvCh {V} ch rodata prog 1 (fun _ c => 8 + {P} * nb ch c c) [] := by
  intro off count input S hE hb hpc
  obtain ⟨⟨g, k, z, cf, n, v, _, d⟩, hok, ha2, _, ha1, ha0, hin⟩ := hE
  have hE' : Entry off count input S := ⟨⟨g, k, z, cf, n, v, hpc, d⟩, hok, ha2, ha1, ha0, hin⟩
  obtain ⟨hh, he, ht, hp, hd⟩ := all_ch ch hch off count input S hE' hb
  exact ⟨hh, he, hp, Or.inl ⟨ht, hd⟩⟩

/-- The kernel as a kernel of the RISC-V library at `vlmax = {V}` (VLEN = {64 * V}; rank 0: it hands
nothing over; any `vl` at entry), deterministic model. -/
def kernel : Library.KernelThm RV LibTable.EntryRv Digest :=
  LibRv.mkKernelRv {V} (LibTable.sym "{base}") 0 [] rodata prog 1 (fun _ c => 8 + {P} * ((c + {V - 1}) / {V}))
    (Riscv.vlAnn RvVl.{base}) RvVl.{base}_ok RvVl.entries.{entsel} norm_thm

/-- The kernel in the RISC-V library under the legal vector-length choice `ch`. -/
def kernel_ch (ch : Nat → Nat) (hch : Riscv.LegalVl {V} ch) : Library.KernelThm (RVc ch) LibTable.EntryRv Digest :=
  LibRv.mkKernelRvCh {V} ch (LibTable.sym "{base}") 0 [] rodata prog 1 (fun _ c => 8 + {P} * nb ch c c)
    (Riscv.vlAnn RvVl.{base}) RvVl.{base}_ok RvVl.entries.{entsel} (norm_thm_ch ch hch)

end Keccaktree.Kernels.{ns}.All
""")
    with open(os.path.join(kdir, 'All.lean'), 'w') as f:
        f.write(''.join(parts))


if __name__ == '__main__':
    main()
