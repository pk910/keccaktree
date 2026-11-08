#!/usr/bin/env python3
"""In place (`out == in`): emit Keccaktree/Kernels/<Ns>/InPlaceAll.lean for an RVV kernel configuration whose
every-count proof is `gen_all_rvv.py`'s All.lean (same arguments):

    gen_inplace_rvv.py <kernel> <Ns> <ProgNs> <V> <s> <L>
      s = instruction index of `sub a2, a2, t0` (380 rvv, 237 rvv_zvkb), L = body length (steps)

The access condition (`Riscv.AccessRun V`, deterministic model `Riscv.isa V`) of every call: per batch of
`w = min(r, V)` nodes from the loop head after `j` nodes, the head (`quietWithin`: no memory cells), the
body `GenB<w>` from its footprint summaries (`gen_inplace.py <Ns> GenB1 .. GenB<V> --prog <ProgNs> --eval
--split`; input loads of the batch at or above `4(off+j)`, the digests below `4(off+j+w)`), the back
edge (no memory); the frame's entry and exit (no memory).  The state facts come from `All` (`batch<w>`,
`batch_any`, `Mid`, `RvvCommon`).  `kernelAl`: `LibRvAl.mkKernelRvAl` with `All.norm_thm` and `access_thm`.
The proof files of the kernel are only read."""
import os, re, sys

kernel, ns, pns, V, s, L = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
root = os.path.dirname(os.path.abspath(__file__))
kdir = os.path.join(root, 'Keccaktree', 'Kernels', ns)
P = L + 6  # steps per batch


def ctl0(w):
    src = open(os.path.join(kdir, f'GenB{w}', 'Slice0.lean')).read()
    return [int(x) for x in re.search(r'^def ctl0 : List Nat := \[(.*?)\]', src, re.M).group(1).split(',')]


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




def batchA(w):
    c0 = ctl0(w)
    return f"""
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **A batch of `{w}` node(s) in place**: input loads of nodes `off + j ..` at or above the bound
`4(off + j)`, which ends at `4(off + j + {w})`. -/
theorem batchA{w} (ch : Nat → Nat) (hch : ch = fun a => min a {V}) (off c : Nat) (input : Int → BitVec 64)
    (S0 S : State (BitVec 64)) (j : Nat) (hb : 64 * (off + c) ≤ 2 ^ 54) (hM : Mid off c input S0 S j 7) (hj : j + {w} ≤ c)
    (hw : ch (c - j) = {w}) :
    AR {P} (4 * ((off + j : Nat) : Int)) (4 * ((off + j : Nat) : Int) + {4 * w}) S := by
  have hM' := batch{w} ch off c input S0 S j hb hM hj hw
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
  have ht : ((c : Int) - j).toNat = c - j := by omega
  have hhd := run_head {V} ch rodata prog prog_7 prog_8 prog_12 prog_13 S ((c : Int) - j) hM.ok.2.1 hM.ctrl.2.2.2.2.2.2.1
    hM.a2 hM.a7 hr0 hr1 (by rw [ht, hw]; omega)
  rw [ht, hw] at hhd
  have hf := H4_facts {w} S ((c : Int) - j)
  have hHenv : ∀ i, i ≠ 261 → i ≠ 284 → envOf (H4 {w} S ((c : Int) - j)) i = envOf S i := fun i a b => H4_env _ _ _ i a b
  generalize hH : H4 {w} S ((c : Int) - j) = H at hhd hf hHenv
  obtain ⟨hf14, hfvl, hf5, hfg, hfk, hfz, hfc, hfn, hfv, hfd, hfh, hfe, hft, hfm⟩ := hf
  have hHok : SliceCert.Ok H := ⟨hfe.trans hM.ok.1, hfh.trans hM.ok.2.1, hft.trans hM.ok.2.2⟩
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
  have hw0 : (rho (off + j)).within GenB{w}.B := rho_within (off + j) (by omega)
  have hrun4 : RV.run rodata prog 4 S = H := by rw [← runCH, ← hch]; exact hhd
  -- the head: no memory cells
  have aH : AR 4 (4 * ((off + j : Nat) : Int)) (4 * ((off + j : Nat) : Int)) S :=
    acc_quietWithin {V} rodata prog 4 [7] S _ (by simp [hM.ctrl.2.2.2.2.2.2.1]) (by decide +kernel)
      (by rw [hrun4]; exact hHok.1)
  -- the body: from its footprint summaries
  have aB : AR GenB{w}.segLen (4 * ((off + j : Nat) : Int)) (4 * ((off + j : Nat) : Int) + {4 * w}) H := by
    rw [← InPlace.GenB{w}.len]
    apply (Riscv.alIsa {V}).chain_access (rho (off + j)) hρ hw0 InPlace.GenB{w}.certs _ _ _ InPlace.GenB{w}.chain
      (by intro C hC; simp only [InPlace.GenB{w}.certs, List.head?_cons, Option.mem_def, Option.some.injEq] at hC; subst hC; exact hc0)
      hHok
    rw [InPlace.GenB{w}.sums, rho_wshift_in, rho_wshift_out]
    simp [SummOk, nextB] <;> omega
  have sr := GenB{w}.seg_run (rho (off + j)) hρ hw0 H hc0 hHok
  generalize hSb : GenB{w}.segAt25 H = Sb at sr
  obtain ⟨hrun, hokb, hcutb⟩ := sr
  have hpcb : Sb.pc = {s} := (cut_fields _ _ _ _ hcutb).2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hrunB : RV.run rodata prog GenB{w}.segLen H = Sb := hrun
  have herr : (RV.run rodata prog 2 Sb).err = false := by
    have := hM'.ok.1
    rw [hch, runCH, show {P} = 4 + GenB{w}.segLen + 2 by rw [body_len{w}], Isa.run_add, Isa.run_add, hrun4, hrunB] at this
    exact this
  -- the back edge: no memory cells
  have aT := acc_quietWithin {V} rodata prog 2 [{s}] Sb (4 * ((off + j : Nat) : Int) + {4 * w}) (by simp [hpcb])
    (by decide +kernel) herr
  rw [show {P} = 4 + GenB{w}.segLen + 2 by rw [body_len{w}]]
  apply Riscv.accessRun_add {V} rodata prog _ _ _ _ _ S
    (Riscv.accessRun_add {V} rodata prog _ _ _ _ _ S aH (by rw [hrun4]; exact aB))
  rw [Isa.run_add, hrun4, hrunB]; exact aT
"""


def main():
    allsrc = open(os.path.join(kdir, 'All.lean')).read()
    m = re.search(r'def kernel : Library\.KernelThm RV LibTable\.EntryRv Digest :=\n  LibRv\.mkKernelRv (.*?)norm_thm\n', allsrc, re.S)
    assert m, 'All.lean: no kernel definition'
    kargs = m.group(1)
    steps = re.search(r'theorem norm_thm : LibRv\.NormThmRv \d+ rodata prog 1 \((fun _ c => .*?)\) \[\] :=', allsrc).group(1)
    for w in range(1, V + 1):
        if not os.path.exists(os.path.join(kdir, 'InPlace', f'GenB{w}.lean')):
            print(f'note: no summaries yet for GenB{w} (gen_inplace.py {ns} GenB1 .. GenB{V} --prog {pns} --eval --split)')
    parts = []
    imports = ''.join(f'import Keccaktree.Kernels.{ns}.InPlace.GenB{w}\n' for w in range(1, V + 1))
    parts.append(f"""import Keccaktree.Kernels.{ns}.All
import Keccaktree.Kernels.RiscvAccSt
{imports}set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_{kernel.rsplit('_v', 1)[0]}` at VLEN = {64 * V} in place (`out == in`)

GENERATED by lean/gen_inplace_rvv.py; do not edit.  The access condition along every call of
`All.norm_thm` (`access_thm`) and the kernel of the in-place RISC-V library (`kernelAl`). -/
namespace Keccaktree.Kernels.{ns}.InPlaceAll
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon Keccaktree.Kernels.RvvCommon
  Keccaktree.Kernels.RiscvAccSt Keccaktree.Kernels.{ns}.All
open Keccaktree.Asm.Riscv (setR getR brHolds cutVar_const_of)
open Keccaktree.Kernels.{pns} (prog rodata)

/-- The access condition in the deterministic model (`vl = min(avl, {V})`). -/
abbrev AR := Riscv.AccessRun {V} rodata prog

theorem runCH (n : Nat) (S : State (BitVec 64)) :
    (RVc (fun a => min a {V})).run rodata prog n S = RV.run rodata prog n S :=
  Riscv.run_min {V} rodata prog n S
""")
    for w in range(1, V + 1):
        parts.append(batchA(w))
    cases = '\n'.join(f'  · exact batchA{w} ch hch off c input S0 S j hb hM (by omega) hwc' for w in range(1, V + 1))
    parts.append(f"""
/-- A batch of any width `w = min (c - j) {V}`. -/
theorem batchA_any (ch : Nat → Nat) (hch : ch = fun a => min a {V}) (off c : Nat) (input : Int → BitVec 64)
    (S0 S : State (BitVec 64)) (j w : Nat) (hb : 64 * (off + c) ≤ 2 ^ 54) (hM : Mid off c input S0 S j 7)
    (hw1 : 1 ≤ w) (hw2 : w ≤ {V}) (hj : j + w ≤ c) (hwc : ch (c - j) = w) :
    AR {P} (4 * ((off + j : Nat) : Int)) (4 * ((off + j : Nat) : Int) + 4 * w) S := by
  rcases (show {' ∨ '.join(f'w = {w}' for w in range(1, V + 1))} by omega) with {' | '.join('rfl' for _ in range(V))}
{cases}

/-- **The loop in place**: from the loop head after `j < c` nodes, the remaining batches, from the bound
`4(off + j)` to `4(off + c)`. -/
theorem loopA (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ f j (S : State (BitVec 64)), Mid off c input S0 S j 7 → j < c → c - j ≤ f →
      AR ({P} * nb (fun a => min a {V}) f (c - j)) (4 * ((off + j : Nat) : Int)) (4 * ((off + c : Nat) : Int)) S := by
  intro f
  induction f with
  | zero => intro j S hM h1 h2; omega
  | succ f ih =>
    intro j S hM h1 h2
    obtain ⟨b1, b2, b3⟩ := (Riscv.legal_min {V}).bounds (by decide) (c - j) (by omega)
    have hstep := batch_any (fun a => min a {V}) off c input S0 S j _ hb hM b1 b3 (by omega) rfl
    have hacc := batchA_any (fun a => min a {V}) rfl off c input S0 S j _ hb hM b1 b3 (by omega) rfl
    have hnb : nb (fun a => min a {V}) (f + 1) (c - j) = 1 + nb (fun a => min a {V}) f (c - j - min (c - j) {V}) := by
      show (if c - j = 0 then 0 else 1 + nb (fun a => min a {V}) f (c - j - min (c - j) {V})) = _
      rw [if_neg (by omega)]
    rw [hnb, show {P} * (1 + nb (fun a => min a {V}) f (c - j - min (c - j) {V})) =
      {P} + {P} * nb (fun a => min a {V}) f (c - j - min (c - j) {V}) by omega]
    apply Riscv.accessRun_add {V} rodata prog _ _ _ _ _ S hacc
    rw [← runCH]
    by_cases hz : c - j - min (c - j) {V} = 0
    · rw [hz, nb_zero, Nat.mul_zero]
      show (4 * ((off + j : Nat) : Int) + 4 * min (c - j) {V}) ≤ 4 * ((off + c : Nat) : Int)
      omega
    · rw [if_neg hz] at hstep
      have := ih (j + min (c - j) {V}) _ hstep (by omega) (by omega)
      rw [show c - (j + min (c - j) {V}) = c - j - min (c - j) {V} by omega,
        show 4 * ((off + (j + min (c - j) {V}) : Nat) : Int) = 4 * ((off + j : Nat) : Int) + 4 * min (c - j) {V} by omega] at this
      exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The access condition of a whole call** (`c` nodes at node offset `off`): the bound starts at `4·off`
and ends at `4·(off + c)`. -/
theorem access_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (hE : Entry off c input S)
    (hb : 64 * (off + c) ≤ 2 ^ 54) :
    AR (8 + {P} * nb (fun a => min a {V}) c c) (4 * (off : Int)) (4 * ((off + c : Nat) : Int)) S := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have h0 := entry_zero {V} (fun a => min a {V}) rodata prog {s} prog_1 prog_{s + 3} off input S hE
    rw [runCH] at h0
    rw [nb_zero, Nat.mul_zero, show 8 + 0 = 2 + 6 from rfl]
    apply Riscv.accessRun_add {V} rodata prog 2 6 _ _ _ S
    · exact acc_quietWithin {V} rodata prog 2 [1] S _ (by simp [hE.ctrl.2.2.2.2.2.2.1]) (by decide +kernel)
        (by rw [h0]; exact hE.ok.1)
    · rw [h0]
      exact accessRun_bf {V} rodata prog 6 _ _ _ _ (accessRun_of_halted' {V} rodata prog 6 _ _ rfl) (by omega)
  · have hM0 := entry_pos {V} (fun a => min a {V}) rodata prog {s} prog_1 prog_2 prog_3 prog_4 prog_5 prog_6 off c input S hE hc hb
    rw [runCH] at hM0
    have a6 := acc_quietWithin {V} rodata prog 6 [1] S (4 * (off : Int)) (by simp [hE.ctrl.2.2.2.2.2.2.1]) (by decide +kernel)
      hM0.ok.1
    have al := loopA off c input S hb c 0 _ hM0 hc (by omega)
    rw [Nat.sub_zero, show ((off + 0 : Nat) : Int) = (off : Int) by simp] at al
    have hl := loop (fun a => min a {V}) (Riscv.legal_min {V}) off c input S hb c 0 _ hM0 hc (by omega)
    rw [Nat.sub_zero] at hl
    generalize hX : (RVc (fun a => min a {V})).run rodata prog ({P} * nb (fun a => min a {V}) c c) (RV.run rodata prog 6 S) = X at hl
    have hX' : RV.run rodata prog ({P} * nb (fun a => min a {V}) c c) (RV.run rodata prog 6 S) = X := by rw [← runCH]; exact hX
    have hx := run_exit {V} (fun a => min a {V}) rodata prog {s} prog_{s + 2} prog_{s + 3} X hl.ok.2.1 hl.ctrl.2.2.2.2.2.2.1
    rw [runCH] at hx
    have ax := acc_quietWithin {V} rodata prog 2 [{s + 2}] X (4 * ((off + c : Nat) : Int)) (by simp [hl.ctrl.2.2.2.2.2.2.1])
      (by decide +kernel) (by rw [hx]; simp only [Riscv.next_err, Riscv.setR_err]; exact hl.ok.1)
    rw [show 8 + {P} * nb (fun a => min a {V}) c c = 6 + {P} * nb (fun a => min a {V}) c c + 2 by omega]
    apply Riscv.accessRun_add {V} rodata prog _ 2 _ _ _ S (Riscv.accessRun_add {V} rodata prog 6 _ _ _ _ S a6 al)
    rw [Isa.run_add, hX']; exact ax

/-! ## In the in-place library -/

/-- The access theorem (`LibRvAl.AccessThmRv`). -/
theorem access_thm : LibRvAl.AccessThmRv {V} rodata prog 1 ({steps}) := by
  intro off count input S hE hb hpc
  have hnorm := norm_thm off count input S hE hb hpc
  obtain ⟨⟨g, k, z, cf, n, v, _, d⟩, hok, ha2, _, ha1, ha0, hin⟩ := hE
  have hE' : Entry off count input S := ⟨⟨g, k, z, cf, n, v, hpc, d⟩, hok, ha2, ha1, ha0, hin⟩
  have h := access_all off count input S hE' hb
  rw [nb_min count count (Nat.le_refl count)] at h
  refine ⟨4 * ((off + count : Nat) : Int), h, ?_⟩
  intro next done _ ht _
  obtain ⟨-, -, -, hout⟩ := hnorm
  rcases hout with ⟨ht', -⟩ | ⟨nx, dn, -, hmem, -⟩
  · exact absurd (ht'.symm.trans ht) (by simp)
  · simp at hmem

/-- The kernel of the in-place RISC-V library (any `vl` at entry). -/
def kernelAl : Library.KernelThm (Riscv.alIsa {V}).isaAl LibRvAl.EntryRvAl Digest :=
  LibRvAl.mkKernelRvAl {kargs}norm_thm access_thm

end Keccaktree.Kernels.{ns}.InPlaceAll
""")
    out = '\n'.join(parts)
    open(os.path.join(kdir, 'InPlaceAll.lean'), 'w').write(out)
    print('written', ns, len(out.splitlines()), 'lines')


if __name__ == '__main__':
    main()
