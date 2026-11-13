import Keccaktree.Kernels.ZbbX1.All
import Keccaktree.Kernels.RiscvAccSt
import Keccaktree.Kernels.ZbbX1.InPlace.GenSE
import Keccaktree.Kernels.ZbbX1.InPlace.GenSI
import Keccaktree.Kernels.ZbbX1.InPlace.GenSC
import Keccaktree.Kernels.ZbbX1.InPlace.GenSX
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_zbb_x1` (RISC-V) in place (`out == in`), for every count

In place the two buffers are one, so the aligned case (`mi = mo = 0`, `All.zbb_x1_all`).  The access
condition along the separate-region run (`access_all`, at `vlmax = 2`; every vector length by
`Riscv.accessRun_vlmax`), mirroring `AllU`: per node `j` the head and the 8 loads (`GenSI`: input words
`8j ..`, at or above the bound `4j`), the rounds (`GenSC`, stack only), the four digest stores into
output words `4j .. 4j+3` (the bound becomes `4j + 4`), the back edge; the concrete steps as `StA`
(`RiscvAccSt`), the segments from their footprint summaries (`InPlace.Gen*`).

`kernelAl vlmax` (`LibRvAl.mkKernelRvAl`) and **`lib_inplace_zbb_x1`**: the in-place library on
`[zbb_x1]`, any `vl` at entry, every vector length.
-/
namespace Keccaktree.Kernels.ZbbX1.InPlaceAll
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon Keccaktree.Kernels.RiscvBytes
  Keccaktree.Kernels.RiscvAccSt Keccaktree.Kernels.ZbbX1.AllU
open Keccaktree.Asm.Riscv (setR getR brHolds run_one exec_br_num exec_j_eq exec_ret_eq getR_zero getR_pos)
open Keccaktree.Kernels.ZbbX1 (prog rodata)

/-- The access condition at `vlmax = 2` (the vector length of `RV`). -/
abbrev AR := Riscv.AccessRun 2 rodata prog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The input part** (aligned): the head (stack only) and the 8 loads of node `j`. -/
theorem in_acc (mi j : Nat) (hm0 : mi = 0) (hb : 64 * j + 64 ≤ 2 ^ 54)
    (S : State (BitVec 64)) (hc : Ctl0 S) (hpc : S.pc = 20) (hsp : S.getGD 2 = gprWord ⟨rStack, SP⟩)
    (hin : S.mem rStack 131053 = gprWord ⟨rInput, mi + 64 * j⟩) (B : Int) (hB : B ≤ 8 * (j : Int)) :
    AR 13 B B S := by
  have hb' : 64 * j + 64 ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hmi : mi < 8 := by omega
  have hR2 : (fun r => S.getGD r) 2 = gprWord ⟨rStack, SP⟩ := hsp
  have s0 : StA 2 rodata prog S 0 20 (fun r => S.getGD r) S.mem B B := StA.start ⟨hc, hpc, fun _ _ => rfl, rfl⟩ B
  have hwfa : (⟨rInput, (mi : Int) + 64 * j⟩ : Addr).wf := ⟨show 0 ≤ (mi : Int) + 64 * j by omega,
    show (mi : Int) + 64 * j < 2 ^ 55 by omega⟩
  have s1 := StA.ld s0 5 2 72 ⟨rStack, SP⟩ 131053 _ prog_20 (by decide) (by decide) (by decide) hR2 sp_wf (by decide)
    (by decide) (by decide) hin (by decide)
  have s2 := StA.addi s1 6 5 0x40#64 ⟨rInput, (mi : Int) + 64 * j⟩ ((mi : Int) + 64 * j + 64) prog_21 (by decide)
    (by decide) (by decide) (by decide) (by simp [upd]) (by rw [show (0x40#64).toInt = 64 by decide])
  have s3 := StA.sd s2 6 2 72 ⟨rStack, SP⟩ 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) prog_22 (by decide)
    (by decide) (by decide) (by simp [upd]; exact hsp) sp_wf (by decide) (by decide) (by decide) (by simp [upd])
    (by decide) (by decide)
  have s4 := StA.andi7 s3 6 5 ⟨rInput, (mi : Int) + 64 * j⟩ prog_23 (by decide) (by decide) (by decide) (by decide)
    (by simp [upd])
  have hm8 : ((⟨rInput, (mi : Int) + 64 * j⟩ : Addr).off % 8) = mi := by show ((mi : Int) + 64 * j) % 8 = mi; omega
  have hm8' : ((mi : Int) + 64 * (j : Int)) % 8 = mi := by omega
  have s5 := StA.brz s4 .eq 6 34 mi prog_24 (by decide) (by decide) (by simp [upd, hm8, hm8'])
    ⟨show (0 : Int) ≤ mi by omega, show (mi : Int) < 2 ^ 55 by omega⟩
  subst hm0
  have hbr : brHolds .eq ((0 : Nat) : Int) 0 = true := rfl
  rw [hbr, if_pos rfl] at s5
  have r5_2 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) S).getGD 2 = gprWord ⟨rStack, SP⟩ :=
    (s5.st.regs 2 (by decide)).trans (by simp [upd]; exact hsp)
  have r5_5 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) S).getGD 5 = gprWord ⟨rInput, ((0 : Nat) : Int) + 64 * j⟩ :=
    (s5.st.regs 5 (by decide)).trans (by simp [upd])
  have hok : SliceCert.Ok (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) S) := s5.st.ctl.ok
  have hpc5 := s5.st.pc
  have hctl5 := s5.st.ctl
  have hacc5 := s5.acc
  generalize hH : RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) S = H at r5_2 r5_5 hok hpc5 hctl5
  have hρ := rho_ok j
  have hw : (rho j).within (2 ^ 54) := rho_within j (by omega)
  have hc0 : relocState (rho j) (cutOf GenSI.ctl0 GenSI.sc0) = cutOf GenSI.ctl0 H := by
    apply relocState_cutOf (rho j) GenSI.ctl0 GenSI.sc0 H
    · intro i hi
      simp only [GenSI.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl
      · rw [cutVar_ptr_of GenSI.ctl0 H 258 ⟨rStack, SP⟩ (by decide) ((envOf_gdVar H 2 (by decide)).trans r5_2) sp_wf
            (by decide), show cutVar GenSI.ctl0 GenSI.sc0 258 = .ptr ⟨rStack, SP⟩ by decide +kernel, reloc_ptr_stack]
      · rw [cutVar_ptr_of GenSI.ctl0 H 261 ⟨rInput, 0 + 64 * (j : Int)⟩ (by decide)
            ((envOf_gdVar H 5 (by decide)).trans r5_5) hwfa (by show rInput ≠ 0; decide),
          show cutVar GenSI.ctl0 GenSI.sc0 261 = .ptr ⟨rInput, 0⟩ by decide +kernel, reloc_ptr_in]
    · intro i hi h; simp only [GenSI.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
    · exact ctrl_eq _ _ hctl5 (by decide +kernel) (hpc5.trans (by decide +kernel))
  have aI : AR GenSI.segLen B B H := by
    have hwI : (rho j).within GenSI.B := rho_within j (by omega)
    rw [← InPlace.GenSI.len]
    apply (Riscv.alIsa 2).chain_access (rho j) hρ hwI InPlace.GenSI.certs _ _ _ InPlace.GenSI.chain
      (by intro C hC; simp only [InPlace.GenSI.certs, List.head?_cons, Option.mem_def, Option.some.injEq] at hC; subst hC; exact hc0) hok
    rw [InPlace.GenSI.sums, rho_wshift_in, rho_wshift_out]
    simp [SummOk, nextB] <;> omega
  have hlen : GenSI.segLen = 8 := by decide +kernel
  rw [hlen] at aI
  rw [show 13 = (0 + 1 + 1 + 1 + 1 + 1) + 8 from rfl]
  apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ S hacc5
  rw [hH]; exact aI

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The rounds** touch only the stack. -/
theorem core_acc (mi j : Nat) (input : Int → BitVec 64) (hb : 64 * j + 64 ≤ 2 ^ 54) (S P : State (BitVec 64))
    (hP : CoreStart mi j input S P) (B : Int) : AR 3415 B B P := by
  have hρ := rho_ok j
  have hw : (rho j).within GenSC.B := rho_within j (by omega)
  rw [← core_len, ← InPlace.GenSC.len]
  apply (Riscv.alIsa 2).chain_access (rho j) hρ hw InPlace.GenSC.certs _ _ _ InPlace.GenSC.chain
    (by intro C hC; simp only [InPlace.GenSC.certs, List.head?_cons, Option.mem_def, Option.some.injEq] at hC; subst hC; exact hP.cut)
    hP.ok
  rw [InPlace.GenSC.sums]
  simp [SummOk, nextB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The output part** (aligned): the head (stack only) and the 4 digest stores into output words
`4j .. 4j+3`: the bound passes them. -/
theorem out_acc (mi mo j : Nat) (hm0 : mo = 0) (input : Int → BitVec 64) (hb : 64 * j + 64 ≤ 2 ^ 54)
    (S C : State (BitVec 64)) (hC : CoreEnd mi j input S C) (hout : S.mem rStack 131052 = gprWord ⟨rOutput, mo + 32 * j⟩)
    (B : Int) (hB : B ≤ 4 * (j : Int)) : AR 10 B (4 * (j : Int) + 4) C := by
  have hmo : mo < 8 := by omega
  have hb' : 64 * j + 64 ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hR2 : (fun r => C.getGD r) 2 = gprWord ⟨rStack, SP⟩ := hC.sp
  have s0 : StA 2 rodata prog C 0 3457 (fun r => C.getGD r) C.mem B B := StA.start ⟨hC.ctl, hC.pc, fun _ _ => rfl, rfl⟩ B
  have hwfb : (⟨rOutput, (mo : Int) + 32 * j⟩ : Addr).wf := ⟨show 0 ≤ (mo : Int) + 32 * j by omega,
    show (mo : Int) + 32 * j < 2 ^ 55 by omega⟩
  have s1 := StA.ld s0 5 2 64 ⟨rStack, SP⟩ 131052 _ prog_5388 (by decide) (by decide) (by decide) hR2 sp_wf (by decide)
    (by decide) (by decide) (hC.out.trans hout) (by decide)
  have s2 := StA.addi s1 6 5 0x20#64 ⟨rOutput, (mo : Int) + 32 * j⟩ ((mo : Int) + 32 * j + 32) prog_5389 (by decide)
    (by decide) (by decide) (by decide) (by simp [upd]) (by rw [show (0x20#64).toInt = 32 by decide])
  have s3 := StA.sd s2 6 2 64 ⟨rStack, SP⟩ 131052 (gprWord ⟨rOutput, (mo : Int) + 32 * j + 32⟩) prog_5390 (by decide)
    (by decide) (by decide) (by simp [upd]; exact hC.sp) sp_wf (by decide) (by decide) (by decide) (by simp [upd])
    (by decide) (by decide)
  have s4 := StA.andi7 s3 6 5 ⟨rOutput, (mo : Int) + 32 * j⟩ prog_5391 (by decide) (by decide) (by decide) (by decide)
    (by simp [upd])
  have hm8 : ((⟨rOutput, (mo : Int) + 32 * j⟩ : Addr).off % 8) = mo := by show ((mo : Int) + 32 * j) % 8 = mo; omega
  have hm8' : ((mo : Int) + 32 * (j : Int)) % 8 = mo := by omega
  have s5 := StA.brz s4 .ne 6 3467 mo prog_5392 (by decide) (by decide) (by simp [upd, hm8, hm8'])
    ⟨show (0 : Int) ≤ mo by omega, show (mo : Int) < 2 ^ 55 by omega⟩
  subst hm0
  have hbr : brHolds .ne ((0 : Nat) : Int) 0 = false := rfl
  rw [hbr, if_neg (by decide)] at s5
  have s6 := StA.sd_out s5 10 5 0 ⟨rOutput, ((0 : Nat) : Int) + 32 * j⟩ (4 * (j : Int)) _ prog_5393 (by decide)
    (by decide) (by decide) (by simp [upd]) hwfb (by show (((0 : Nat) : Int) + 32 * (j : Int) + 0) % 8 = 0; omega)
    rfl (by show (((0 : Nat) : Int) + 32 * (j : Int) + 0) / 8 = 4 * (j : Int); omega) rfl
  have s7 := StA.sd_out s6 11 5 8 ⟨rOutput, ((0 : Nat) : Int) + 32 * j⟩ (4 * (j : Int) + 1) _ prog_5394 (by decide)
    (by decide) (by decide) (by simp [upd]) hwfb (by show (((0 : Nat) : Int) + 32 * (j : Int) + 8) % 8 = 0; omega)
    rfl (by show (((0 : Nat) : Int) + 32 * (j : Int) + 8) / 8 = 4 * (j : Int) + 1; omega) rfl
  have s8 := StA.sd_out s7 12 5 16 ⟨rOutput, ((0 : Nat) : Int) + 32 * j⟩ (4 * (j : Int) + 2) _ prog_5395 (by decide)
    (by decide) (by decide) (by simp [upd]) hwfb (by show (((0 : Nat) : Int) + 32 * (j : Int) + 16) % 8 = 0; omega)
    rfl (by show (((0 : Nat) : Int) + 32 * (j : Int) + 16) / 8 = 4 * (j : Int) + 2; omega) rfl
  have s9 := StA.sd_out s8 13 5 24 ⟨rOutput, ((0 : Nat) : Int) + 32 * j⟩ (4 * (j : Int) + 3) _ prog_5396 (by decide)
    (by decide) (by decide) (by simp [upd]) hwfb (by show (((0 : Nat) : Int) + 32 * (j : Int) + 24) % 8 = 0; omega)
    rfl (by show (((0 : Nat) : Int) + 32 * (j : Int) + 24) / 8 = 4 * (j : Int) + 3; omega) rfl
  have s10 := StA.j s9 3479 prog_5397
  exact accessRun_bf 2 rodata prog _ _ _ _ _ s10.acc (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The back edge `ld; addi; sd; beq` (and `j` when the loop goes on): stack only. -/
theorem back_acc (mi mo off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (k : Nat) (S U : State (BitVec 64))
    (hk : k < c) (hb : 64 * (off + c) ≤ 2 ^ 54) (hH : Head mi mo off c input S0 k S) (hU : OutEnd mi mo (off + k) input S U)
    (B : Int) : AR 4 B B U ∧ (k + 1 < c → AR 5 B B U) := by
  have hR2 : (fun r => U.getGD r) 2 = gprWord ⟨rStack, SP⟩ := hU.sp
  have s0 : StA 2 rodata prog U 0 3479 (fun r => U.getGD r) U.mem B B := StA.start ⟨hU.ctl, hU.pc, fun _ _ => rfl, rfl⟩ B
  have s1 := StA.ld s0 5 2 80 ⟨rStack, SP⟩ 131054 _ prog_5410 (by decide) (by decide) (by decide) hR2 sp_wf (by decide)
    (by decide) (by decide) (hU.cnt.trans hH.cnt) (by decide)
  have hm1 : (0xffffffffffffffff#64).toInt = -1 := by decide
  have s2 := StA.addi s1 5 5 0xffffffffffffffff#64 ⟨0, (c : Int) - k⟩ ((c : Int) - k - 1) prog_5411 (by decide) (by decide)
    (by decide) (by decide) (by simp [upd])
    (by show (c : Int) - k + (0xffffffffffffffff#64).toInt = (c : Int) - k - 1; omega)
  have s3 := StA.sd s2 5 2 80 ⟨rStack, SP⟩ 131054 (gprWord ⟨0, (c : Int) - k - 1⟩) prog_5412 (by decide) (by decide)
    (by decide) (by simp [upd]; exact hU.sp) sp_wf (by decide) (by decide) (by decide) (by simp [upd]) (by decide) (by decide)
  have s4 := StA.brz s3 .eq 5 3484 ((c : Int) - k - 1) prog_5413 (by decide) (by decide) (by simp [upd])
    ⟨show (0 : Int) ≤ (c : Int) - k - 1 by omega, show (c : Int) - k - 1 < 2 ^ 55 by
      rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; omega⟩
  refine ⟨s4.acc, fun hk1 => ?_⟩
  have hbr : brHolds .eq ((c : Int) - k - 1) 0 = false := by simp only [brHolds, beq_eq_false_iff_ne, ne_eq]; omega
  rw [hbr, if_neg (by decide)] at s4
  exact (StA.j s4 20 prog_5414).acc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One iteration in place**: node `j = off + k`, from the bound `4j` to `4j + 4`. -/
theorem iter_acc (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64))
    (hb : 64 * (off + c) ≤ 2 ^ 54) (k : Nat) (S : State (BitVec 64)) (hk : k < c) (hH : Head 0 0 off c input S0 k S) :
    AR 3442 (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S ∧
    (k + 1 < c → AR 3443 (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S) := by
  have hj : 64 * (off + k) + 64 ≤ 2 ^ 54 := by
    have : 64 * (off + k) + 64 ≤ 64 * (off + c) := by omega
    omega
  have hin : S.mem rStack 131053 = gprWord ⟨rInput, ((0 : Nat) : Int) + 64 * ((off + k : Nat) : Int)⟩ :=
    hH.inp.trans (congrArg (fun o => gprWord ⟨rInput, o⟩) (by omega))
  have hout : S.mem rStack 131052 = gprWord ⟨rOutput, ((0 : Nat) : Int) + 32 * ((off + k : Nat) : Int)⟩ :=
    hH.out.trans (congrArg (fun o => gprWord ⟨rOutput, o⟩) (by omega))
  have aI := in_acc 0 (off + k) rfl hj S hH.ctl hH.pc hH.sp hin (4 * ((off + k : Nat) : Int)) (by omega)
  have hP := in_part 0 (off + k) input (by decide) hj S hH.ctl hH.pc hH.sp hin hH.msg
  generalize hPe : RV.run rodata prog (inSteps 0) S = P at hP
  have aC := core_acc 0 (off + k) input hj S P hP (4 * ((off + k : Nat) : Int))
  have hC := core_part 0 (off + k) input hj S P hP
  generalize hCe : RV.run rodata prog 3415 P = C at hC
  have aO := out_acc 0 0 (off + k) rfl input hj S C hC hout (4 * ((off + k : Nat) : Int)) (by omega)
  have hU := out_part 0 0 (off + k) input (by decide) hj S C hC hout
  generalize hUe : RV.run rodata prog (outSteps 0) C = U at hU
  have aB := back_acc 0 0 off c input S0 k S U hk hb hH hU (4 * ((off + k : Nat) : Int) + 4)
  have hP' : RV.run rodata prog 13 S = P := hPe
  have hU' : RV.run rodata prog 10 C = U := hUe
  have pre : AR (13 + 3415 + 10) (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S := by
    apply Riscv.accessRun_add 2 rodata prog (13 + 3415) 10 _ (4 * ((off + k : Nat) : Int)) _ S
    · apply Riscv.accessRun_add 2 rodata prog 13 3415 _ _ _ S aI
      rw [hP']; exact aC
    · rw [Isa.run_add, hP', hCe]; exact aO
  refine ⟨?_, fun hk1 => ?_⟩
  · rw [show (3442 : Nat) = 13 + 3415 + 10 + 4 from rfl]
    apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ S pre
    rw [Isa.run_add, Isa.run_add, hP', hCe, hU']; exact aB.1
  · rw [show (3443 : Nat) = 13 + 3415 + 10 + 5 from rfl]
    apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ S pre
    rw [Isa.run_add, Isa.run_add, hP', hCe, hU']; exact aB.2 hk1

/-- **The loop in place**: from the head before iteration `k`, the remaining `d + 1` iterations, from the
bound `4(off + k)` to `4(off + c)`. -/
theorem loop_acc (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ d k (S : State (BitVec 64)), k + d + 1 = c → Head 0 0 off c input S0 k S →
      AR (3443 * d + 3442) (4 * ((off + k : Nat) : Int)) (4 * ((off + c : Nat) : Int)) S := by
  intro d
  induction d with
  | zero =>
    intro k S hk hH
    have := (iter_acc off c input S0 hb k S (by omega) hH).1
    rw [show ((off + c : Nat) : Int) = (off + k : Nat) + 1 by omega, show 3443 * 0 + 3442 = 3442 from rfl,
      show 4 * (((off + k : Nat) : Int) + 1) = 4 * ((off + k : Nat) : Int) + 4 by omega]
    exact this
  | succ d ih =>
    intro k S hk hH
    have h1 := (iter 0 0 off c input S0 (by decide) (by decide) hb k S (by omega) hH).1 (by omega)
    rw [show 3443 * (d + 1) + 3442 = 3443 + (3443 * d + 3442) by rw [Nat.mul_add, Nat.mul_one]; omega]
    apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ S ((iter_acc off c input S0 hb k S (by omega) hH).2 (by omega))
    have := ih (k + 1) _ (by omega) h1
    rw [show ((off + (k + 1) : Nat) : Int) = (off + k : Nat) + 1 by omega] at this
    rw [show 4 * ((off + k : Nat) : Int) + 4 = 4 * (((off + k : Nat) : Int) + 1) by omega]
    exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The epilogue (restores, `ret`) touches neither input nor output. -/
theorem exit_acc (off c : Nat) (input : Int → BitVec 64) (S0 U : State (BitVec 64))
    (hX : ExitAt 0 0 off c input S0 U) (b : Int) : AR 15 b b U := by
  have hρ := rho_ok 0
  have hw : (rho 0).within GenSX.B := rho_within 0 (by decide)
  have hc0 : relocState (rho 0) (cutOf GenSX.ctl0 GenSX.sc0) = cutOf GenSX.ctl0 U := by
    apply relocState_cutOf (rho 0) GenSX.ctl0 GenSX.sc0 U
    · intro i hi
      simp only [GenSX.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi
      rw [cutVar_ptr_of GenSX.ctl0 U 258 ⟨rStack, SP⟩ (by decide) ((envOf_gdVar U 2 (by decide)).trans hX.sp) sp_wf
          (by decide), show cutVar GenSX.ctl0 GenSX.sc0 258 = .ptr ⟨rStack, SP⟩ by decide +kernel, reloc_ptr_stack]
    · intro i hi h; simp only [GenSX.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
    · exact ctrl_eq _ _ hX.ctl (by decide +kernel) (hX.pc.trans (by decide +kernel))
  have hseg : AR GenSX.segLen b b U := by
    rw [← InPlace.GenSX.len]
    apply (Riscv.alIsa 2).chain_access (rho 0) hρ hw InPlace.GenSX.certs _ _ _ InPlace.GenSX.chain
      (by intro C hC; simp only [InPlace.GenSX.certs, List.head?_cons, Option.mem_def, Option.some.injEq] at hC; subst hC; exact hc0)
      hX.ctl.ok
    rw [InPlace.GenSX.sums]
    simp [SummOk, nextB]
  have sr := GenSX.seg_run (rho 0) hρ hw U hc0 hX.ctl.ok
  generalize hSx : GenSX.segAt1 U = Sx at sr
  obtain ⟨hrun, hokx, hcutx⟩ := sr
  have hpc : Sx.pc = 3498 := (cut_fields _ _ _ _ hcutx).2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hrunU : RV.run rodata prog GenSX.segLen U = Sx := hrun
  rw [show 15 = GenSX.segLen + 1 by rw [exit_len]]
  apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ U hseg
  rw [hrunU]
  apply Riscv.accessRun_step 2 rodata prog 0 _ _ Sx hokx.2.1
  · rw [hpc, prog_5429, exec_ret_eq 2 rodata Sx hokx.2.1]; exact hokx.1
  · intro cl hc; rw [hpc, prog_5429] at hc; simp [Riscv.reads] at hc
  · intro cl hc; rw [hpc, prog_5429] at hc; simp [Riscv.writes] at hc
  · exact Int.le_refl _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The access condition of a whole call** (`c` nodes at node offset `off`, `vlmax = 2`): the bound
starts at `4·off` and ends at `4·(off + c)`. -/
theorem access_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : All.Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    AR (32 + 3443 * c) (4 * (off : Int)) (4 * ((off + c : Nat) : Int)) S := by
  have hE : EntryU 0 0 off c input S :=
    ⟨hE.ctrl, hE.ok, hE.a2, hE.sp, hE.a1.trans (congrArg (fun o => gprWord ⟨rInput, o⟩) (by push_cast; omega)),
      hE.a0.trans (congrArg (fun o => gprWord ⟨rOutput, o⟩) (by push_cast; omega)), hE.inp⟩
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hh : S.halted = false := hE.ok.2.1
  have hpc0 : S.pc = 1 := hE.ctrl.2.2.2.2.2.2.2.1
  have hcwf : (⟨0, (c : Int)⟩ : Addr).wf := by
    show 0 ≤ (c : Int) ∧ (c : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hbr : Riscv.exec 2 rodata (.br .ne 12 0 3) S = { S with pc := if brHolds .ne (c : Int) 0 then 3 else S.pc + 1 } :=
    exec_br_num 2 rodata S .ne 12 0 3 c 0 hh ((getR_pos S 12 (by decide)).trans hE.a2) (getR_zero S) hcwf (by decide)
  -- the entry `bnez a2`: no memory
  have a1 : ∀ (m : Nat) (bf : Int), AR m (4 * (off : Int)) bf { S with pc := if brHolds .ne (c : Int) 0 then 3 else S.pc + 1 } →
      AR (m + 1) (4 * (off : Int)) bf S := by
    intro m bf hrest
    apply Riscv.accessRun_step 2 rodata prog _ _ _ S hh
    · rw [hpc0, prog_1, hbr]; exact hE.ok.1
    · intro cl hc; rw [hpc0, prog_1] at hc; simp [Riscv.reads] at hc
    · intro cl hc; rw [hpc0, prog_1] at hc; simp [Riscv.writes] at hc
    · rw [hpc0, prog_1, hbr]; exact hrest
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- no node: `j` to the `ret`
    subst hc
    generalize hT1 : ({ S with pc := if brHolds .ne ((0 : Nat) : Int) 0 then 3 else S.pc + 1 } : State (BitVec 64)) = T1 at a1
    have hT1pc : T1.pc = 2 := by rw [← hT1]; simp [brHolds, hpc0]
    have hT1h : T1.halted = false := by rw [← hT1]; exact hh
    have hT1e : T1.err = false := by rw [← hT1]; exact hE.ok.1
    rw [show 32 + 3443 * 0 = 31 + 1 from rfl]
    apply a1
    rw [show (31 : Nat) = 30 + 1 from rfl]
    apply Riscv.accessRun_step 2 rodata prog _ _ _ T1 hT1h
    · rw [hT1pc, prog_2, exec_j_eq 2 rodata T1 3498 hT1h]; exact hT1e
    · intro cl hc; rw [hT1pc, prog_2] at hc; simp [Riscv.reads] at hc
    · intro cl hc; rw [hT1pc, prog_2] at hc; simp [Riscv.writes] at hc
    rw [hT1pc, prog_2, exec_j_eq 2 rodata T1 3498 hT1h, show (30 : Nat) = 29 + 1 from rfl]
    apply Riscv.accessRun_step 2 rodata prog _ _ _ { T1 with pc := 3498 } hT1h
    · rw [show ({ T1 with pc := 3498 } : State (BitVec 64)).pc = 3498 from rfl, prog_5429,
        exec_ret_eq 2 rodata { T1 with pc := 3498 } hT1h]; exact hT1e
    · intro cl hc; rw [show ({ T1 with pc := 3498 } : State (BitVec 64)).pc = 3498 from rfl, prog_5429] at hc
      simp [Riscv.reads] at hc
    · intro cl hc; rw [show ({ T1 with pc := 3498 } : State (BitVec 64)).pc = 3498 from rfl, prog_5429] at hc
      simp [Riscv.writes] at hc
    rw [show ({ T1 with pc := 3498 } : State (BitVec 64)).pc = 3498 from rfl, prog_5429,
      exec_ret_eq 2 rodata { T1 with pc := 3498 } hT1h]
    show (Riscv.alIsa 2).AccessRun rodata prog (28 + 1) _ _ _
    simp [AlIsa.AccessRun]
  · have hbrc : brHolds .ne (c : Int) 0 = true := by simp [brHolds]; omega
    rw [hbrc] at a1
    generalize hT1 : ({ S with pc := if true = true then 3 else S.pc + 1 } : State (BitVec 64)) = T1 at a1
    have hT1pc : T1.pc = 3 := by rw [← hT1]; rfl
    have hT1ok : SliceCert.Ok T1 := by rw [← hT1]; exact hE.ok
    have hT1env : ∀ i, envOf T1 i = envOf S i := by intro i; rw [← hT1]; rfl
    have hT1mem : T1.mem = S.mem := by rw [← hT1]
    have hρ := rho_ok 0
    have hw0 : (rho 0).within GenSE.B := rho_within 0 (by decide)
    have hc0 : relocState (rho 0) (cutOf GenSE.ctl0 GenSE.sc0) = cutOf GenSE.ctl0 T1 := by
      apply relocState_cutOf (rho 0) GenSE.ctl0 GenSE.sc0 T1
      · intro i hi
        simp only [GenSE.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
        subst hi
        rw [cutVar_ptr_of GenSE.ctl0 T1 258 ⟨rStack, 1048576⟩ (by decide)
            ((hT1env 258).trans ((envOf_gdVar S 2 (by decide)).trans hE.sp)) (by decide) (by decide),
          show cutVar GenSE.ctl0 GenSE.sc0 258 = .ptr ⟨rStack, 1048576⟩ by decide +kernel, reloc_ptr_stack]
      · intro i hi h; simp only [GenSE.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
      · obtain ⟨g, k, z, cf, n, v, l, p, d⟩ := hE.ctrl
        have e : T1.g = S.g ∧ T1.k = S.k ∧ T1.zf = S.zf ∧ T1.cf = S.cf ∧ T1.nf = S.nf ∧ T1.vf = S.vf ∧ T1.vl = S.vl ∧
            T1.depth = S.depth := by rw [← hT1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := e
        rw [e1, e2, e3, e4, e5, e6, e7, e8, hT1pc, g, k, z, cf, n, v, l, d]
        decide +kernel
    -- E: frame stores and spills (stack only)
    have aE : AR GenSE.segLen (4 * (off : Int)) (4 * (off : Int)) T1 := by
      rw [← InPlace.GenSE.len]
      apply (Riscv.alIsa 2).chain_access (rho 0) hρ hw0 InPlace.GenSE.certs _ _ _ InPlace.GenSE.chain
        (by intro C hC; simp only [InPlace.GenSE.certs, List.head?_cons, Option.mem_def, Option.some.injEq] at hC; subst hC; exact hc0)
        hT1ok
      rw [InPlace.GenSE.sums]
      simp [SummOk, nextB]
    have s1 := GenSE.seg_run (rho 0) hρ hw0 T1 hc0 hT1ok
    have f1 := GenSE.seg_frame (rho 0) hρ hw0 T1 hc0 hT1ok
    have mv := GenSE.seg_moves (rho 0) hρ hw0 T1 hc0 hT1ok
    generalize hT2 : GenSE.segAt1 T1 = T2 at s1 f1 mv
    obtain ⟨hrun1, hok1, hcut1⟩ := s1
    obtain ⟨hC2, hp2⟩ := ctl0_of_cut _ _ _ _ hcut1 hok1 (by decide +kernel)
    have hmove : ∀ (d s : Nat) (q : Int), (d, s) ∈ ([(2097155, 268), (2097139, 267), (2097123, 266)] : List (Nat × Nat)) →
        d = memVar rStack q → s < 288 → T2.mem rStack q = envOf S s := by
      intro d s q hm hd hs
      have := mv d s hm
      rw [rho_var_stack 0 d (by rw [hd]; exact memVar_ge _ _) (by rw [hd]; exact memVarRegion_memVar _ _),
        Reloc.var_lt _ _ hs, hd, envOf_mem, hT1env] at this
      exact this
    have hH : Head 0 0 off c input S 0 T2 := by
      refine ⟨hC2, hp2.trans (by decide +kernel), sp_of_cut (rho 0) hρ GenSE.ctl1 GenSE.sc1 T2 hcut1 (by decide)
        (by decide +kernel), ?_, ?_, ?_, fun q => ?_, fun b _ => ?_, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      · rw [hmove 2097139 267 131053 (by simp) (by decide +kernel) (by decide)]
        exact ((envOf_gdVar S 11 (by decide)).trans hE.a1).trans (congrArg (fun o => gprWord ⟨rInput, o⟩) (by push_cast; omega))
      · rw [hmove 2097123 266 131052 (by simp) (by decide +kernel) (by decide)]
        exact ((envOf_gdVar S 10 (by decide)).trans hE.a0).trans (congrArg (fun o => gprWord ⟨rOutput, o⟩) (by push_cast; omega))
      · rw [hmove 2097155 268 131054 (by simp) (by decide +kernel) (by decide)]
        exact ((envOf_gdVar S 12 (by decide)).trans hE.a2).trans (congrArg (fun o => gprWord ⟨0, o⟩) (by push_cast; omega))
      · rw [f1 rInput q rfl, hT1mem]; exact hE.inp q
      · have : T2.mem rOutput = S.mem rOutput := funext fun q => by rw [f1 rOutput q rfl, hT1mem]
        rw [this]
    have hl := loop 0 0 off c input S (by decide) (by decide) hb (c - 1) 0 T2 (by omega) hH
    have al := loop_acc off c input S hb (c - 1) 0 T2 (by omega) hH
    rw [show ((off + 0 : Nat) : Int) = (off : Int) by simp] at al
    have ae := exit_acc off c input S _ hl (4 * ((off + c : Nat) : Int))
    have hrun1' : RV.run rodata prog GenSE.segLen T1 = T2 := hrun1
    rw [show 32 + 3443 * c = (GenSE.segLen + ((3443 * (c - 1) + 3442) + 15)) + 1 by rw [entry_len]; omega]
    apply a1
    apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ T1 aE
    rw [hrun1']
    rw [show 3443 * (c - 1) + 3442 = iterSteps 0 0 * (c - 1) + (iterSteps 0 0 - 1) from rfl] at al ⊢
    exact Riscv.accessRun_add 2 rodata prog _ _ _ _ _ T2 al ae

/-! ## The in-place library on `[zbb_x1]` -/

/-- The access theorem of `zbb_x1` at every vector length (`LibRvAl.AccessThmRv`). -/
theorem access_thm (vlmax : Nat) : LibRvAl.AccessThmRv vlmax rodata prog 1 (fun _ c => 32 + 3443 * c) := by
  intro off c input S hE hb hpc
  obtain ⟨⟨g, k, z, cf, n, v, l, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩ := hE
  have hE' : All.Entry off c input S := ⟨⟨g, k, z, cf, n, v, l, hpc, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩
  refine ⟨4 * ((off + c : Nat) : Int),
    Riscv.accessRun_vlmax 2 vlmax rodata prog All.scalar _ _ _ _ (access_all off c input S hE' hb), ?_⟩
  intro next done _ ht _
  obtain ⟨-, -, -, hout⟩ := All.norm_thm vlmax off c input S ⟨⟨g, k, z, cf, n, v, l, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩ hb hpc
  rcases hout with ⟨ht', -⟩ | ⟨nx, dn, -, hmem, -⟩
  · exact absurd (ht'.symm.trans ht) (by simp)
  · simp at hmem

/-- `keccaktree_keccak256_zbb_x1` as a kernel of the in-place RISC-V library (any `vl` at entry). -/
def kernelAl (vlmax : Nat) : Library.KernelThm (Riscv.alIsa vlmax).isaAl LibRvAl.EntryRvAl Digest :=
  LibRvAl.mkKernelRvAl vlmax (LibTable.sym "zbb_x1") 0 [] rodata prog 1 (fun _ c => 32 + 3443 * c)
    (Riscv.vlAnn RvVl.zbb_x1) RvVl.zbb_x1_ok RvVl.entries.2.1 (All.norm_thm vlmax) (access_thm vlmax)

theorem ranks_al (vlmax : Nat) : Library.RanksOk [kernelAl vlmax] := by
  intro K hK t ht
  simp only [List.mem_singleton] at hK
  subst hK
  simp [kernelAl, LibRvAl.mkKernelRvAl, LibAliasGen.mkKernelAlG, LibRv.mkKernelRv] at ht

/-- **The in-place library theorem on the table `[zbb_x1]`** (RISC-V, VLEN = 64·`vlmax`, one buffer,
any `vl` at entry): the library run halts without a model fault with every node's digest in the
buffer. -/
theorem lib_inplace_zbb_x1 (vlmax : Nat) (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64))
    (hT : LibRvAl.EntryRvAl (LibTable.sym "zbb_x1") off count input T) :
    Library.LibOk [kernelAl vlmax] (kernelAl vlmax) off count input T :=
  Library.lib_correct [kernelAl vlmax] 0 (by simp [kernelAl, LibRvAl.mkKernelRvAl, LibAliasGen.mkKernelAlG, LibRv.mkKernelRv])
    (ranks_al vlmax) LibX86.digest_local _ (kernelAl vlmax) (by simp) off count input T (Nat.le_refl _) hT

end Keccaktree.Kernels.ZbbX1.InPlaceAll
