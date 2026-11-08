import Keccaktree.Kernels.Rv64X1.AllUIn
import Keccaktree.Kernels.Rv64X1.GenSC.Seg
import Keccaktree.Kernels.Rv64X1.GenSX.Seg
import Keccaktree.Asm.RiscvChoice
import Keccaktree.Kernels.RvVl
import Keccaktree.Kernels.LibRvU
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_rv64_x1` at any buffer alignment: the rounds, the digest stores, the loop

Continues `AllUIn` (the calling convention `EntryU`, the loop head `Head`, the input part `in_part`).
-/
namespace Keccaktree.Kernels.Rv64X1.AllU
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon Keccaktree.Kernels.RiscvBytes
open Keccaktree.Asm.Riscv (setR getR brHolds run_one exec_br_num exec_j_eq exec_ret_eq getR_zero getR_pos)
open Keccaktree.Kernels.Rv64X1 (prog rodata)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The rounds' output invariant: registers `x10..x13` hold the first 4 lanes of the permuted state. -/
theorem core_out (input : Int → BitVec 64) (mi j : Nat) (env : Nat → BitVec 64)
    (h : GenSC.Inv24 env (GenSC.AAt (AN input mi j) 24)) (w : Nat) (hw : w < 4) :
    env (gdVar (10 + w)) = L (Spec.keccakF (absorbNode (nodeWordsB input mi j))) w := by
  rw [show GenSC.AAt (AN input mi j) 24 = fun _ => Spec.rounds 24 (absorbNode (nodeWordsB input mi j)) from
    funext fun n => by
      obtain ⟨n, hn⟩ := n
      have : n = 0 := by omega
      subst this
      exact GenSC.aat_0 _] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at h0 h1 h2 h3
  rcases w with _ | _ | _ | _ | w
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · omega

/-! ## The rounds -/

/-- The state after the rounds (`pc = 5388`) of node `j`, from a loop-head state `S`. -/
structure CoreEnd (mi j : Nat) (input : Int → BitVec 64) (S C : State (BitVec 64)) : Prop where
  ctl : Ctl0 C
  pc : C.pc = 5388
  sp : C.getGD 2 = gprWord ⟨rStack, SP⟩
  dig : ∀ w, w < 4 → C.getGD (10 + w) = L (Spec.keccakF (absorbNode (nodeWordsB input mi j))) w
  out : C.mem rStack 131052 = S.mem rStack 131052
  inp : C.mem rStack 131053 = gprWord ⟨rInput, mi + 64 * j + 64⟩
  cnt : C.mem rStack 131054 = S.mem rStack 131054
  msg : ∀ q, C.mem rInput q = S.mem rInput q
  outm : ∀ q, C.mem rOutput q = S.mem rOutput q

theorem core_len : GenSC.segLen = 5346 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The rounds**, at the relocation of node `j`. -/
theorem core_part (mi j : Nat) (input : Int → BitVec 64) (hb : 64 * j + 64 ≤ 2 ^ 54) (S P : State (BitVec 64))
    (hP : CoreStart mi j input S P) : CoreEnd mi j input S (RV.run rodata prog 5346 P) := by
  have hρ := rho_ok j
  have hw : (rho j).within (2 ^ 54) := rho_within j (by omega)
  have sr := GenSC.seg_run (rho j) hρ hw P hP.cut hP.ok
  have fr := GenSC.seg_frame (rho j) hρ hw P hP.cut hP.ok
  have dat := GenSC.seg_data (rho j) hρ hw P hP.cut hP.ok (AN input mi j) hP.inv
  generalize hC : GenSC.segAt24 P = C at sr fr dat
  obtain ⟨hrun, hok, hcut⟩ := sr
  rw [← core_len, hrun]
  obtain ⟨hc, hp⟩ := ctl0_of_cut _ _ _ _ hcut hok (by decide +kernel)
  have hmem : ∀ r q, (r ≠ rStack ∨ q < 131055) → C.mem r q = P.mem r q := by
    intro r q h
    apply fr r q
    rcases h with h | h
    · have : (r == 3) = false := by simp only [beq_eq_false_iff_ne]; exact h
      simp only [this, Bool.false_and]
    · by_cases hr : r = rStack
      · subst hr; rw [rho_wshift_stack]; simp only [Int.sub_zero]
        have : decide ((131055 : Int) ≤ q) = false := decide_eq_false (by omega)
        simp only [this, Bool.and_false, Bool.false_and]
      · have : (r == 3) = false := by simp only [beq_eq_false_iff_ne]; exact hr
        simp only [this, Bool.false_and]
  refine ⟨hc, hp.trans (by decide +kernel), sp_of_cut (rho j) hρ GenSC.ctl24 GenSC.sc24 C hcut (by decide) (by decide +kernel),
    fun w hw' => ?_, (hmem _ _ (Or.inr (by decide))).trans hP.out, (hmem _ _ (Or.inr (by decide))).trans hP.inp,
    (hmem _ _ (Or.inr (by decide))).trans hP.cnt, fun q => (hmem _ _ (Or.inl (by decide))).trans (hP.msg q),
    fun q => (hmem _ _ (Or.inl (by decide))).trans (hP.outm q)⟩
  have := core_out input mi j _ dat w hw'
  simp only [Reloc.var_lt (rho j) (gdVar (10 + w)) (show gdVar (10 + w) < 288 by simp only [gdVar]; omega)] at this
  rw [← envOf_gdVar C (10 + w) (by omega)]
  exact this

/-! ## The digest stores -/

theorem store4_eq (M : Region → Int → BitVec 64) (r : Region) (q0 : Int) (D : Nat → BitVec 64) (w : Nat) (hw : w < 4) :
    memStore (memStore (memStore (memStore M r q0 (D 0)) r (q0 + 1) (D 1)) r (q0 + 2) (D 2)) r (q0 + 3) (D 3) r
      (q0 + w) = D w := by
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl
  · rw [memStore_other _ _ _ _ _ _ (Or.inr (show q0 + ((0 : Nat) : Int) ≠ q0 + 3 by omega)),
      memStore_other _ _ _ _ _ _ (Or.inr (show q0 + ((0 : Nat) : Int) ≠ q0 + 2 by omega)),
      memStore_other _ _ _ _ _ _ (Or.inr (show q0 + ((0 : Nat) : Int) ≠ q0 + 1 by omega)),
      show q0 + ((0 : Nat) : Int) = q0 by omega, memStore_same]
  · rw [memStore_other _ _ _ _ _ _ (Or.inr (show q0 + ((1 : Nat) : Int) ≠ q0 + 3 by omega)),
      memStore_other _ _ _ _ _ _ (Or.inr (show q0 + ((1 : Nat) : Int) ≠ q0 + 2 by omega)),
      show q0 + ((1 : Nat) : Int) = q0 + 1 by omega, memStore_same]
  · rw [memStore_other _ _ _ _ _ _ (Or.inr (show q0 + ((2 : Nat) : Int) ≠ q0 + 3 by omega)),
      show q0 + ((2 : Nat) : Int) = q0 + 2 by omega, memStore_same]
  · rw [show q0 + ((3 : Nat) : Int) = q0 + 3 by omega, memStore_same]

theorem store4_other (M : Region → Int → BitVec 64) (r : Region) (q0 : Int) (D : Nat → BitVec 64) (r' : Region) (q : Int)
    (h : r' ≠ r ∨ q < q0 ∨ q0 + 4 ≤ q) :
    memStore (memStore (memStore (memStore M r q0 (D 0)) r (q0 + 1) (D 1)) r (q0 + 2) (D 2)) r (q0 + 3) (D 3) r' q =
      M r' q := by
  have e : ∀ x : Int, q0 ≤ x → x < q0 + 4 → (r' ≠ r ∨ q ≠ x) := by
    intro x h1 h2; rcases h with h | h | h
    · exact Or.inl h
    · right; omega
    · right; omega
  rw [memStore_other _ _ _ _ _ _ (e _ (by omega) (by omega)), memStore_other _ _ _ _ _ _ (e _ (by omega) (by omega)),
    memStore_other _ _ _ _ _ _ (e _ (by omega) (by omega)), memStore_other _ _ _ _ _ _ (e _ (by omega) (by omega))]

/-- The digest bytes of 4 stored words. -/
theorem store4_byte (W : Int → BitVec 64) (q0 : Int) (D : Nat → BitVec 64) (hW : ∀ w : Nat, w < 4 → W (q0 + w) = D w)
    (t : Nat) (ht : t < 32) : byteAt W (8 * q0 + t) = (D (t / 8)).extractLsb' (8 * (t % 8)) 8 := by
  rw [show 8 * q0 + (t : Int) = 8 * (q0 + ((t / 8 : Nat) : Int)) + ((t % 8 : Nat) : Int) by push_cast; omega,
    byteAt_word _ _ _ (Nat.mod_lt _ (by decide)), hW _ (by omega)]

/-- The state after the digest stores (`pc = 5410`, the back edge). -/
structure OutEnd (mi mo j : Nat) (input : Int → BitVec 64) (S U : State (BitVec 64)) : Prop where
  ctl : Ctl0 U
  pc : U.pc = 5410
  sp : U.getGD 2 = gprWord ⟨rStack, SP⟩
  out : U.mem rStack 131052 = gprWord ⟨rOutput, mo + 32 * j + 32⟩
  inp : U.mem rStack 131053 = gprWord ⟨rInput, mi + 64 * j + 64⟩
  cnt : U.mem rStack 131054 = S.mem rStack 131054
  msg : ∀ q, U.mem rInput q = S.mem rInput q
  keep : ∀ b : Int, (b < mo + 32 * j ∨ mo + 32 * j + 32 ≤ b) → byteAt (U.mem rOutput) b = byteAt (S.mem rOutput) b
  dig : DigestB mi mo input U j

/-- The steps of the output part: the head test, the stores (through the bounce buffer if misaligned). -/
def outSteps (mo : Nat) : Nat := if mo = 0 then 10 else 203

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The output part**: the output pointer's test and the digest stores, directly or through the
bounce buffer and `COPY_BYTES`. -/
theorem out_part (mi mo j : Nat) (input : Int → BitVec 64) (hmo : mo < 8) (hb : 64 * j + 64 ≤ 2 ^ 54)
    (S C : State (BitVec 64)) (hC : CoreEnd mi j input S C) (hout : S.mem rStack 131052 = gprWord ⟨rOutput, mo + 32 * j⟩) :
    OutEnd mi mo j input S (RV.run rodata prog (outSteps mo) C) := by
  have hb' : 64 * j + 64 ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hR2 : (fun r => C.getGD r) 2 = gprWord ⟨rStack, SP⟩ := hC.sp
  have s0 : St (RV.run rodata prog 0 C) 5388 (fun r => C.getGD r) C.mem := ⟨hC.ctl, hC.pc, fun _ _ => rfl, rfl⟩
  have hwfb : (⟨rOutput, (mo : Int) + 32 * j⟩ : Addr).wf := ⟨show 0 ≤ (mo : Int) + 32 * j by omega,
    show (mo : Int) + 32 * j < 2 ^ 55 by omega⟩
  -- ld t0, 64(sp); addi t1, t0, 32; sd t1, 64(sp); andi t1, t0, 7; bnez t1, 4f
  have s1 := St.ld s0 5 2 64 ⟨rStack, SP⟩ 131052 _ prog_5388 (by decide) (by decide) (by decide) hR2 sp_wf (by decide)
    (by decide) (by decide) (hC.out.trans hout)
  have s2 := St.addi s1 6 5 0x20#64 ⟨rOutput, (mo : Int) + 32 * j⟩ ((mo : Int) + 32 * j + 32) prog_5389 (by decide)
    (by decide) (by decide) (by decide) (by simp [upd]) (by rw [show (0x20#64).toInt = 32 by decide])
  have s3 := St.sd s2 6 2 64 ⟨rStack, SP⟩ 131052 (gprWord ⟨rOutput, (mo : Int) + 32 * j + 32⟩) prog_5390 (by decide)
    (by decide) (by decide) (by simp [upd]; exact hC.sp) sp_wf (by decide) (by decide) (by decide) (by simp [upd])
  have s4 := St.andi7 s3 6 5 ⟨rOutput, (mo : Int) + 32 * j⟩ prog_5391 (by decide) (by decide) (by decide) (by decide)
    (by simp [upd])
  have hm8 : ((⟨rOutput, (mo : Int) + 32 * j⟩ : Addr).off % 8) = mo := by show ((mo : Int) + 32 * j) % 8 = mo; omega
  have hm8' : ((mo : Int) + 32 * (j : Int)) % 8 = mo := by omega
  have s5 := St.brz s4 .ne 6 5398 mo prog_5392 (by decide) (by decide) (by simp [upd, hm8, hm8'])
    ⟨show (0 : Int) ≤ mo by omega, show (mo : Int) < 2 ^ 55 by omega⟩
  have r5_2 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) C).getGD 2 = gprWord ⟨rStack, SP⟩ :=
    (s5.regs 2 (by decide)).trans (by simp [upd]; exact hC.sp)
  have r5_5 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) C).getGD 5 = gprWord ⟨rOutput, (mo : Int) + 32 * j⟩ :=
    (s5.regs 5 (by decide)).trans (by simp [upd])
  have hD : ∀ w, w < 4 → C.getGD (10 + w) = L (Spec.keccakF (absorbNode (nodeWordsB input mi j))) w := hC.dig
  generalize hDd : (fun w => C.getGD (10 + w)) = D at hD
  have hDw : ∀ w, C.getGD (10 + w) = D w := fun w => by rw [← hDd]
  have hM5 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) C).mem =
      memStore C.mem rStack 131052 (gprWord ⟨rOutput, (mo : Int) + 32 * j + 32⟩) := s5.mem
  have hdig : ∀ U : State (BitVec 64), (∀ t : Nat, t < 32 →
      byteAt (U.mem rOutput) ((mo : Int) + 32 * j + t) = (D (t / 8)).extractLsb' (8 * (t % 8)) 8) →
      DigestB mi mo input U j := by
    intro U h t ht
    rw [h t ht]
    exact digest_byte input mi j D (fun w hw => (hDw w).symm.trans (hD w hw)) t ht
  by_cases hm0 : mo = 0
  · -- aligned: the 4 words into the output
    subst hm0
    have hbr : brHolds .ne ((0 : Nat) : Int) 0 = false := rfl
    rw [hbr, if_neg (by decide)] at s5
    have hq0 : (((0 : Nat) : Int) + 32 * (j : Int)) / 8 = 4 * (j : Int) := by omega
    have s6 := St.sd s5 10 5 0 ⟨rOutput, ((0 : Nat) : Int) + 32 * j⟩ (4 * (j : Int)) (D 0) prog_5393 (by decide)
      (by decide) (by decide) (by simp [upd]) hwfb (by show (((0 : Nat) : Int) + 32 * (j : Int) + 0) % 8 = 0; omega)
      (by show rOutput ≠ rRodata; decide) (by show (((0 : Nat) : Int) + 32 * (j : Int) + 0) / 8 = 4 * (j : Int); omega) (by simp [upd]; exact hDw 0)
    have s7 := St.sd s6 11 5 8 ⟨rOutput, ((0 : Nat) : Int) + 32 * j⟩ (4 * (j : Int) + 1) (D 1) prog_5394 (by decide)
      (by decide) (by decide) (by simp [upd]) hwfb (by show (((0 : Nat) : Int) + 32 * (j : Int) + 8) % 8 = 0; omega)
      (by show rOutput ≠ rRodata; decide) (by show (((0 : Nat) : Int) + 32 * (j : Int) + 8) / 8 = 4 * (j : Int) + 1; omega)
      (by simp [upd]; exact hDw 1)
    have s8 := St.sd s7 12 5 16 ⟨rOutput, ((0 : Nat) : Int) + 32 * j⟩ (4 * (j : Int) + 2) (D 2) prog_5395 (by decide)
      (by decide) (by decide) (by simp [upd]) hwfb (by show (((0 : Nat) : Int) + 32 * (j : Int) + 16) % 8 = 0; omega)
      (by show rOutput ≠ rRodata; decide) (by show (((0 : Nat) : Int) + 32 * (j : Int) + 16) / 8 = 4 * (j : Int) + 2; omega)
      (by simp [upd]; exact hDw 2)
    have s9 := St.sd s8 13 5 24 ⟨rOutput, ((0 : Nat) : Int) + 32 * j⟩ (4 * (j : Int) + 3) (D 3) prog_5396 (by decide)
      (by decide) (by decide) (by simp [upd]) hwfb (by show (((0 : Nat) : Int) + 32 * (j : Int) + 24) % 8 = 0; omega)
      (by show rOutput ≠ rRodata; decide) (by show (((0 : Nat) : Int) + 32 * (j : Int) + 24) / 8 = 4 * (j : Int) + 3; omega)
      (by simp [upd]; exact hDw 3)
    have s10 := St.j s9 5410 prog_5397
    generalize hU : RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) C = U at s10
    have hrunU : RV.run rodata prog (outSteps 0) C = U := by rw [← hU]; rfl
    rw [hrunU]
    have hMU : U.mem = memStore (memStore (memStore (memStore (memStore C.mem rStack 131052
        (gprWord ⟨rOutput, ((0 : Nat) : Int) + 32 * j + 32⟩)) rOutput (4 * (j : Int)) (D 0)) rOutput (4 * (j : Int) + 1) (D 1))
        rOutput (4 * (j : Int) + 2) (D 2)) rOutput (4 * (j : Int) + 3) (D 3) := s10.mem
    have hstk : ∀ q, U.mem rStack q = memStore C.mem rStack 131052 (gprWord ⟨rOutput, ((0 : Nat) : Int) + 32 * j + 32⟩)
        rStack q := fun q => by rw [hMU, store4_other _ _ _ D _ _ (Or.inl (show rStack ≠ rOutput by decide))]
    have hU2 : U.getGD 2 = gprWord ⟨rStack, SP⟩ := (s10.regs 2 (by decide)).trans (by simp [upd]; exact hC.sp)
    refine ⟨s10.ctl, s10.pc, hU2, by rw [hstk, memStore_same], ?_, ?_, fun q => ?_, fun b hb => ?_, hdig U fun t ht => ?_⟩
    · rw [hstk, memStore_other _ _ _ _ _ _ (Or.inr (show (131053 : Int) ≠ 131052 by decide))]; exact hC.inp
    · rw [hstk, memStore_other _ _ _ _ _ _ (Or.inr (show (131054 : Int) ≠ 131052 by decide))]; exact hC.cnt
    · rw [hMU, store4_other _ _ _ D _ _ (Or.inl (show rInput ≠ rOutput by decide)),
        memStore_other _ _ _ _ _ _ (Or.inl (show rInput ≠ rStack by decide))]
      exact hC.msg q
    · have e : ∀ x, (x < 4 * (j : Int) ∨ 4 * (j : Int) + 4 ≤ x) → U.mem rOutput x = S.mem rOutput x := by
        intro x hx
        rw [hMU, store4_other _ _ _ D _ _ (Or.inr hx), memStore_other _ _ _ _ _ _ (Or.inl (show rOutput ≠ rStack by decide))]
        exact hC.outm x
      unfold byteAt
      rw [e (b / 8) (by omega)]
    · rw [show ((0 : Nat) : Int) + 32 * (j : Int) + (t : Int) = 8 * (4 * (j : Int)) + (t : Int) by omega]
      exact store4_byte _ _ D (fun w hw => by rw [hMU]; exact store4_eq _ _ _ D w hw) t ht
  · -- misaligned: the 4 words into the bounce buffer, then the 32 bytes
    have hbr : brHolds .ne (mo : Int) 0 = true := by simp only [brHolds, bne_iff_ne, ne_eq]; omega
    rw [hbr, if_pos rfl] at s5
    have s6 := St.sd s5 10 2 0 ⟨rStack, SP⟩ 131044 (D 0) prog_5398 (by decide) (by decide) (by decide)
      (by simp [upd]; exact hC.sp) sp_wf (by decide) (by decide) (by decide) (by simp [upd]; exact hDw 0)
    have s7 := St.sd s6 11 2 8 ⟨rStack, SP⟩ (131044 + 1) (D 1) prog_5399 (by decide) (by decide) (by decide)
      (by simp [upd]; exact hC.sp) sp_wf (by decide) (by decide) (by decide) (by simp [upd]; exact hDw 1)
    have s8 := St.sd s7 12 2 16 ⟨rStack, SP⟩ (131044 + 2) (D 2) prog_5400 (by decide) (by decide) (by decide)
      (by simp [upd]; exact hC.sp) sp_wf (by decide) (by decide) (by decide) (by simp [upd]; exact hDw 2)
    have s9 := St.sd s8 13 2 24 ⟨rStack, SP⟩ (131044 + 3) (D 3) prog_5401 (by decide) (by decide) (by decide)
      (by simp [upd]; exact hC.sp) sp_wf (by decide) (by decide) (by decide) (by simp [upd]; exact hDw 3)
    have s10 := St.mv s9 6 2 prog_5402 (by decide) (by decide) (by decide) (by decide)
    have s11 := St.li s10 17 0x20#64 prog_5403 (by decide) (by decide)
    have r11_5 : (RV.run rodata prog 11 C).getGD 5 = gprWord ⟨rOutput, (mo : Int) + 32 * j⟩ := by
      rw [s11.regs 5 (by decide)]; simp [upd]
    have r11_6 : (RV.run rodata prog 11 C).getGD 6 = gprWord ⟨rStack, 8 * 131044⟩ := by
      rw [s11.regs 6 (by decide)]; simp only [upd]; simp; exact hC.sp
    have r11_17 : (RV.run rodata prog 11 C).getGD 17 = gprWord ⟨0, ((32 : Nat) : Int)⟩ := by
      rw [s11.regs 17 (by decide)]; simp only [upd]; simp; decide
    have r11_2 : (RV.run rodata prog 11 C).getGD 2 = gprWord ⟨rStack, SP⟩ := by
      rw [s11.regs 2 (by decide)]; simp only [upd]; simp; exact hC.sp
    have hM11 : (RV.run rodata prog 11 C).mem = memStore (memStore (memStore (memStore (memStore C.mem rStack 131052
        (gprWord ⟨rOutput, (mo : Int) + 32 * j + 32⟩)) rStack 131044 (D 0)) rStack (131044 + 1) (D 1))
        rStack (131044 + 2) (D 2)) rStack (131044 + 3) (D 3) := s11.mem
    have hcp := copy_loop 2 rodata prog 5404 6 5 7 17 code_out regs_out rStack rOutput (8 * 131044) ((mo : Int) + 32 * j)
      (by decide) (by decide) (by decide) (by decide) (by decide) 32 (by decide) (by decide) (by omega) (by decide)
      (by omega) (by decide) _ s11.ctl s11.pc r11_6 r11_5 r11_17
    obtain ⟨hT1, hp1⟩ := hcp
    generalize hT0 : RV.run rodata prog 11 C = T0 at hT1 hp1 hM11 r11_2
    generalize hT1e : RV.run rodata prog (6 * 32) T0 = U at hT1 hp1
    have hrunU : RV.run rodata prog (outSteps mo) C = U := by
      rw [show outSteps mo = 11 + 6 * 32 by simp [outSteps, hm0], Isa.run_add, hT0, hT1e]
    rw [hrunU]
    have hstk : ∀ q, U.mem rStack q = T0.mem rStack q := fun q => hT1.word_other rStack q (Or.inl (by decide))
    have hT0s : ∀ q, (q < 131044 ∨ 131044 + 4 ≤ q) → T0.mem rStack q =
        memStore C.mem rStack 131052 (gprWord ⟨rOutput, (mo : Int) + 32 * j + 32⟩) rStack q := by
      intro q hq; rw [hM11, store4_other _ _ _ D _ _ (Or.inr hq)]
    have hU2 : U.getGD 2 = gprWord ⟨rStack, SP⟩ := by
      rw [hT1.regs 2 (by decide) (by decide) (by decide) (by decide)]; exact r11_2
    refine ⟨hT1.ctl, hp1, hU2, by rw [hstk, hT0s 131052 (Or.inr (by decide)), memStore_same], ?_, ?_, fun q => ?_,
      fun b hb => ?_, hdig U fun t ht => ?_⟩
    · rw [hstk, hT0s 131053 (Or.inr (by decide)), memStore_other _ _ _ _ _ _ (Or.inr (show (131053 : Int) ≠ 131052 by decide))]
      exact hC.inp
    · rw [hstk, hT0s 131054 (Or.inr (by decide)), memStore_other _ _ _ _ _ _ (Or.inr (show (131054 : Int) ≠ 131052 by decide))]
      exact hC.cnt
    · rw [hT1.word_other rInput q (Or.inl (by decide)), hM11, store4_other _ _ _ D _ _ (Or.inl (show rInput ≠ rStack by decide)),
        memStore_other _ _ _ _ _ _ (Or.inl (show rInput ≠ rStack by decide))]
      exact hC.msg q
    · rw [hT1.bytes, if_neg]
      · unfold byteAt
        rw [hM11, store4_other _ _ _ D _ _ (Or.inl (show rOutput ≠ rStack by decide)),
          memStore_other _ _ _ _ _ _ (Or.inl (show rOutput ≠ rStack by decide)), hC.outm]
      · rintro ⟨-, h1, h2⟩; push_cast at h2; omega
    · rw [hT1.bytes, if_pos]
      · rw [show (8 * 131044 : Int) + ((mo : Int) + 32 * (j : Int) + (t : Int) - ((mo : Int) + 32 * (j : Int))) =
          8 * 131044 + (t : Int) by omega]
        exact store4_byte _ _ D (fun w hw => by rw [hM11]; exact store4_eq _ _ _ D w hw) t ht
      · exact ⟨rfl, by omega, by push_cast; omega⟩

/-! ## One iteration and the loop -/

/-- The steps of one iteration: input part, rounds, output part, back edge (with the `j`). -/
def iterSteps (mi mo : Nat) : Nat := inSteps mi + 5346 + outSteps mo + 5

theorem iterSteps_00 : iterSteps 0 0 = 5374 := rfl

/-- The state at the epilogue (`pc = 5415`). -/
structure ExitAt (mi mo off c : Nat) (input : Int → BitVec 64) (S0 U : State (BitVec 64)) : Prop where
  ctl : Ctl0 U
  pc : U.pc = 5415
  sp : U.getGD 2 = gprWord ⟨rStack, SP⟩
  pre : ∀ b : Int, b < mo + 32 * off → byteAt (U.mem rOutput) b = byteAt (S0.mem rOutput) b
  dig : ∀ n, n < c → DigestB mi mo input U (off + n)

theorem digestB_congr (mi mo : Nat) (input : Int → BitVec 64) (U V : State (BitVec 64)) (j : Nat)
    (h : ∀ t : Nat, t < 32 → byteAt (V.mem rOutput) (mo + 32 * j + t) = byteAt (U.mem rOutput) (mo + 32 * j + t))
    (hd : DigestB mi mo input U j) : DigestB mi mo input V j := by
  intro t ht; rw [h t ht]; exact hd t ht

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One iteration of the loop.** -/
theorem iter (mi mo off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hmi : mi < 8) (hmo : mo < 8)
    (hb : 64 * (off + c) ≤ 2 ^ 54) (k : Nat) (S : State (BitVec 64)) (hk : k < c) (hH : Head mi mo off c input S0 k S) :
    (k + 1 < c → Head mi mo off c input S0 (k + 1) (RV.run rodata prog (iterSteps mi mo) S)) ∧
    (k + 1 = c → ExitAt mi mo off c input S0 (RV.run rodata prog (iterSteps mi mo - 1) S)) := by
  have hj : 64 * (off + k) + 64 ≤ 2 ^ 54 := by
    have : 64 * (off + k) + 64 ≤ 64 * (off + c) := by omega
    omega
  have hin : S.mem rStack 131053 = gprWord ⟨rInput, mi + 64 * ((off + k : Nat) : Int)⟩ :=
    hH.inp.trans (congrArg (fun o => gprWord ⟨rInput, o⟩) (by omega))
  have hout : S.mem rStack 131052 = gprWord ⟨rOutput, mo + 32 * ((off + k : Nat) : Int)⟩ :=
    hH.out.trans (congrArg (fun o => gprWord ⟨rOutput, o⟩) (by omega))
  have hP := in_part mi (off + k) input hmi hj S hH.ctl hH.pc hH.sp hin hH.msg
  generalize hPe : RV.run rodata prog (inSteps mi) S = P at hP
  have hC := core_part mi (off + k) input hj S P hP
  generalize hCe : RV.run rodata prog 5346 P = C at hC
  have hU := out_part mi mo (off + k) input hmo hj S C hC hout
  generalize hUe : RV.run rodata prog (outSteps mo) C = U at hU
  -- the back edge: ld t0, 80(sp); addi t0, t0, -1; sd t0, 80(sp); beq t0, zero, exit
  have hR2 : (fun r => U.getGD r) 2 = gprWord ⟨rStack, SP⟩ := hU.sp
  have s0 : St (RV.run rodata prog 0 U) 5410 (fun r => U.getGD r) U.mem := ⟨hU.ctl, hU.pc, fun _ _ => rfl, rfl⟩
  have s1 := St.ld s0 5 2 80 ⟨rStack, SP⟩ 131054 _ prog_5410 (by decide) (by decide) (by decide) hR2 sp_wf (by decide)
    (by decide) (by decide) (hU.cnt.trans hH.cnt)
  have hm1 : (0xffffffffffffffff#64).toInt = -1 := by decide
  have s2 := St.addi s1 5 5 0xffffffffffffffff#64 ⟨0, (c : Int) - k⟩ ((c : Int) - k - 1) prog_5411 (by decide) (by decide)
    (by decide) (by decide) (by simp [upd])
    (by show (c : Int) - k + (0xffffffffffffffff#64).toInt = (c : Int) - k - 1; omega)
  have s3 := St.sd s2 5 2 80 ⟨rStack, SP⟩ 131054 (gprWord ⟨0, (c : Int) - k - 1⟩) prog_5412 (by decide) (by decide)
    (by decide) (by simp [upd]; exact hU.sp) sp_wf (by decide) (by decide) (by decide) (by simp [upd])
  have s4 := St.brz s3 .eq 5 5415 ((c : Int) - k - 1) prog_5413 (by decide) (by decide) (by simp [upd])
    ⟨show (0 : Int) ≤ (c : Int) - k - 1 by omega, show (c : Int) - k - 1 < 2 ^ 55 by omega⟩
  have hM4 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1) U).mem = memStore U.mem rStack 131054 (gprWord ⟨0, (c : Int) - k - 1⟩) :=
    s4.mem
  have hM4o : (RV.run rodata prog (0 + 1 + 1 + 1 + 1) U).mem rOutput = U.mem rOutput := by
    rw [hM4]; funext q; exact memStore_other _ _ _ _ _ _ (Or.inl (by decide))
  have r4_2 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1) U).getGD 2 = gprWord ⟨rStack, SP⟩ :=
    (s4.regs 2 (by decide)).trans (by simp [upd]; exact hU.sp)
  have hrun0 : ∀ m, RV.run rodata prog (inSteps mi + 5346 + outSteps mo + m) S = RV.run rodata prog m U := by
    intro m
    rw [Isa.run_add _ _ _ (inSteps mi + 5346 + outSteps mo) m, Isa.run_add _ _ _ (inSteps mi + 5346) (outSteps mo),
      Isa.run_add _ _ _ (inSteps mi) 5346, hPe, hCe, hUe]
  -- the output bytes of the iteration's state
  have hdig' : ∀ n, n < k + 1 → ∀ V : State (BitVec 64), V.mem rOutput = U.mem rOutput → DigestB mi mo input V (off + n) := by
    intro n hn V hV
    by_cases hnk : n < k
    · apply digestB_congr mi mo input S V (off + n) _ (hH.dig n hnk)
      intro t ht; rw [hV]; apply hU.keep; left; push_cast; omega
    · have : n = k := by omega
      subst this
      exact digestB_congr mi mo input U V (off + n) (fun t _ => by rw [hV]) hU.dig
  have hpre' : ∀ V : State (BitVec 64), V.mem rOutput = U.mem rOutput →
      ∀ b : Int, b < mo + 32 * off → byteAt (V.mem rOutput) b = byteAt (S0.mem rOutput) b := by
    intro V hV b hb'
    rw [hV, hU.keep b (Or.inl (by push_cast; omega))]
    exact hH.pre b hb'
  refine ⟨fun hk1 => ?_, fun hk1 => ?_⟩
  · have hbr : brHolds .eq ((c : Int) - k - 1) 0 = false := by simp only [brHolds, beq_eq_false_iff_ne, ne_eq]; omega
    rw [hbr, if_neg (by decide)] at s4
    have s5 := St.j s4 20 prog_5414
    have hrun : RV.run rodata prog (iterSteps mi mo) S = RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) U := by
      rw [← hrun0]; rfl
    rw [hrun]
    have hM5 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) U).mem = memStore U.mem rStack 131054 (gprWord ⟨0, (c : Int) - k - 1⟩) :=
      s5.mem
    have hM5o : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) U).mem rOutput = U.mem rOutput := by
      rw [hM5]; funext q; exact memStore_other _ _ _ _ _ _ (Or.inl (by decide))
    refine ⟨s5.ctl, s5.pc, (s5.regs 2 (by decide)).trans (by simp [upd]; exact hU.sp), ?_, ?_, ?_, fun q => ?_,
      hpre' _ hM5o, fun n hn => hdig' n hn _ hM5o⟩
    · rw [hM5, memStore_other _ _ _ _ _ _ (Or.inr (show (131053 : Int) ≠ 131054 by decide)), hU.inp]
      exact congrArg (fun o => gprWord ⟨rInput, o⟩) (by push_cast; omega)
    · rw [hM5, memStore_other _ _ _ _ _ _ (Or.inr (show (131052 : Int) ≠ 131054 by decide)), hU.out]
      exact congrArg (fun o => gprWord ⟨rOutput, o⟩) (by push_cast; omega)
    · rw [hM5, memStore_same]
      exact congrArg (fun o => gprWord ⟨0, o⟩) (by push_cast; omega)
    · rw [hM5, memStore_other _ _ _ _ _ _ (Or.inl (show rInput ≠ rStack by decide)), hU.msg, hH.msg]
  · have hbr : brHolds .eq ((c : Int) - k - 1) 0 = true := by simp only [brHolds, beq_iff_eq]; omega
    rw [hbr, if_pos rfl] at s4
    have hrun : RV.run rodata prog (iterSteps mi mo - 1) S = RV.run rodata prog (0 + 1 + 1 + 1 + 1) U := by
      rw [show iterSteps mi mo - 1 = inSteps mi + 5346 + outSteps mo + 4 by unfold iterSteps; omega, hrun0]
    rw [hrun]
    refine ⟨s4.ctl, s4.pc, r4_2, hpre' _ hM4o, fun n hn => hdig' n (by omega) _ hM4o⟩

/-- **The loop**: from the head before iteration `k`, the remaining `d + 1 = c - k` iterations reach the
epilogue with every digest written. -/
theorem loop (mi mo off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hmi : mi < 8) (hmo : mo < 8)
    (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ d k (S : State (BitVec 64)), k + d + 1 = c → Head mi mo off c input S0 k S →
      ExitAt mi mo off c input S0 (RV.run rodata prog (iterSteps mi mo * d + (iterSteps mi mo - 1)) S) := by
  intro d
  induction d with
  | zero =>
    intro k S hk hH
    rw [show iterSteps mi mo * 0 + (iterSteps mi mo - 1) = iterSteps mi mo - 1 by omega]
    exact (iter mi mo off c input S0 hmi hmo hb k S (by omega) hH).2 (by omega)
  | succ d ih =>
    intro k S hk hH
    have h1 := (iter mi mo off c input S0 hmi hmo hb k S (by omega) hH).1 (by omega)
    rw [show iterSteps mi mo * (d + 1) + (iterSteps mi mo - 1) = iterSteps mi mo + (iterSteps mi mo * d + (iterSteps mi mo - 1))
      by rw [Nat.mul_add, Nat.mul_one]; omega, Isa.run_add]
    exact ih (k + 1) _ (by omega) h1

theorem exit_len : GenSX.segLen = 14 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The epilogue**: the restores and `ret` halt with the memory unchanged. -/
theorem epilogue (mi mo off c : Nat) (input : Int → BitVec 64) (S0 U : State (BitVec 64))
    (hX : ExitAt mi mo off c input S0 U) :
    (RV.run rodata prog 15 U).halted = true ∧ (RV.run rodata prog 15 U).err = false ∧
    (RV.run rodata prog 15 U).tail = none ∧
    (∀ b : Int, b < mo + 32 * off → byteAt ((RV.run rodata prog 15 U).mem rOutput) b = byteAt (S0.mem rOutput) b) ∧
    ∀ n, n < c → DigestB mi mo input (RV.run rodata prog 15 U) (off + n) := by
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
  have sr := GenSX.seg_run (rho 0) hρ hw U hc0 hX.ctl.ok
  have fr := GenSX.seg_frame (rho 0) hρ hw U hc0 hX.ctl.ok
  generalize hSx : GenSX.segAt1 U = Sx at sr fr
  obtain ⟨hrun, hokx, hcutx⟩ := sr
  have hpc : Sx.pc = 5429 := (cut_fields _ _ _ _ hcutx).2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hr : RV.run rodata prog 15 U = { Sx with halted := true } := by
    rw [show 15 = GenSX.segLen + 1 by rw [exit_len], Isa.run_add, hrun, run_one 2 rodata prog Sx hokx.2.1,
      show prog.getD Sx.pc .nop = .ret by rw [hpc]; exact prog_5429, exec_ret_eq 2 rodata Sx hokx.2.1]
  have hmem : ∀ r q, Sx.mem r q = U.mem r q := fun r q => fr r q rfl
  have hmo : Sx.mem rOutput = U.mem rOutput := funext fun q => hmem _ _
  rw [hr]
  refine ⟨rfl, hokx.1, hokx.2.2, fun b hb => ?_, fun n hn => ?_⟩
  · show byteAt (Sx.mem rOutput) b = _
    rw [hmo]; exact hX.pre b hb
  · exact digestB_congr mi mo input U _ (off + n) (fun t _ => by show byteAt (Sx.mem rOutput) _ = _; rw [hmo]) (hX.dig n hn)

/-! ## The whole call -/

theorem entry_len : GenSE.segLen = 17 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`keccaktree_keccak256_rv64_x1` on any number of nodes at any buffer alignment.**  For every
count `c`, node offset `off` with `64·(off + c) ≤ 2^54` and byte offsets `mi, mo < 8` of the input and
output buffers, from an entry state, `32 + c·iterSteps mi mo` steps halt without a model fault and
without a tail call, keep the output bytes before the output buffer, and leave the keccak256 digest
of input node `off + n` (the 64 bytes at `mi + 64(off+n)`) in the 32 output bytes at
`mo + 32(off+n)`, for every `n < c`. -/
theorem rv64_x1_allU (mi mo off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (hmi : mi < 8) (hmo : mo < 8)
    (hE : EntryU mi mo off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    (RV.run rodata prog (32 + c * iterSteps mi mo) S).halted = true ∧
    (RV.run rodata prog (32 + c * iterSteps mi mo) S).err = false ∧
    (RV.run rodata prog (32 + c * iterSteps mi mo) S).tail = none ∧
    (∀ b : Int, b < mo + 32 * off →
      byteAt ((RV.run rodata prog (32 + c * iterSteps mi mo) S).mem rOutput) b = byteAt (S.mem rOutput) b) ∧
    ∀ n, n < c → DigestB mi mo input (RV.run rodata prog (32 + c * iterSteps mi mo) S) (off + n) := by
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hh : S.halted = false := hE.ok.2.1
  have hpc0 : S.pc = 1 := hE.ctrl.2.2.2.2.2.2.2.1
  have hcwf : (⟨0, (c : Int)⟩ : Addr).wf := by
    show 0 ≤ (c : Int) ∧ (c : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  -- bnez a2
  have hbr : RV.run rodata prog 1 S = { S with pc := if brHolds .ne (c : Int) 0 then 3 else S.pc + 1 } := by
    rw [run_one 2 rodata prog S hh, show prog.getD S.pc .nop = .br .ne 12 0 3 by rw [hpc0]; exact prog_1,
      exec_br_num 2 rodata S .ne 12 0 3 c 0 hh ((getR_pos S 12 (by decide)).trans hE.a2) (getR_zero S) hcwf (by decide)]
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- no node: `j` to the `ret`
    subst hc
    generalize hT1 : ({ S with pc := if brHolds .ne ((0 : Nat) : Int) 0 then 3 else S.pc + 1 } : State (BitVec 64)) = T1 at hbr
    have hT1pc : T1.pc = 2 := by rw [← hT1]; simp [brHolds, hpc0]
    have hT1h : T1.halted = false := by rw [← hT1]; exact hh
    have h2 : RV.run rodata prog 1 T1 = { T1 with pc := 5429 } := by
      rw [run_one 2 rodata prog T1 hT1h, hT1pc, prog_2, exec_j_eq 2 rodata T1 5429 hT1h]
    have h3 : RV.run rodata prog 1 { T1 with pc := 5429 } = { T1 with pc := 5429, halted := true } := by
      rw [run_one 2 rodata prog { T1 with pc := 5429 } hT1h]
      exact exec_ret_eq 2 rodata { T1 with pc := 5429 } hT1h
    have hrun : RV.run rodata prog 3 S = { T1 with pc := 5429, halted := true } := by
      rw [show 3 = 1 + 1 + 1 from rfl, Isa.run_add, Isa.run_add, hbr, h2, h3]
    rw [show 32 + 0 * iterSteps mi mo = 3 + 29 by omega, Isa.run_add, hrun, Isa.run_halted _ _ _ _ _ rfl]
    have hmem : T1.mem = S.mem := by rw [← hT1]
    refine ⟨rfl, ?_, ?_, fun b _ => by show byteAt (T1.mem rOutput) b = _; rw [hmem], fun n hn => absurd hn (Nat.not_lt_zero _)⟩
    · show T1.err = false; rw [← hT1]; exact hE.ok.1
    · show T1.tail = none; rw [← hT1]; exact hE.ok.2.2
  · have hbrc : brHolds .ne (c : Int) 0 = true := by simp [brHolds]; omega
    rw [hbrc] at hbr
    generalize hT1 : ({ S with pc := if true = true then 3 else S.pc + 1 } : State (BitVec 64)) = T1 at hbr
    have hT1pc : T1.pc = 3 := by rw [← hT1]; rfl
    have hT1ok : SliceCert.Ok T1 := by rw [← hT1]; exact hE.ok
    have hT1env : ∀ i, envOf T1 i = envOf S i := by intro i; rw [← hT1]; rfl
    have hT1mem : T1.mem = S.mem := by rw [← hT1]
    have hρ := rho_ok 0
    have hw0 : (rho 0).within GenSE.B := rho_within 0 (by decide)
    -- the entry cut
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
    have hH : Head mi mo off c input S 0 T2 := by
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
    have hl := loop mi mo off c input S hmi hmo hb (c - 1) 0 T2 (by omega) hH
    have he := epilogue mi mo off c input S _ hl
    have hrun1' : RV.run rodata prog 17 T1 = T2 := by rw [← entry_len]; exact hrun1
    have hI : 1 ≤ iterSteps mi mo := by unfold iterSteps; omega
    have hsteps : ∀ I c : Nat, 1 ≤ I → 1 ≤ c → 32 + c * I = 1 + 17 + (I * (c - 1) + (I - 1)) + 15 := by
      intro I c hI hc
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [Nat.succ_mul, show c' + 1 - 1 = c' by omega, Nat.mul_comm I c']
      omega
    rw [hsteps _ _ hI hc,
      Isa.run_add _ _ _ (1 + 17 + (iterSteps mi mo * (c - 1) + (iterSteps mi mo - 1))) 15,
      Isa.run_add _ _ _ (1 + 17) (iterSteps mi mo * (c - 1) + (iterSteps mi mo - 1)), Isa.run_add _ _ _ 1 17, hbr, hrun1']
    exact he

/-! ## In the misaligned library -/

set_option maxRecDepth 100000 in
/-- The kernel has no `vsetvli` and no byte-vector instruction: its runs are the same for every vector length. -/
theorem scalarU : prog.toList.all (fun i => !i.usesVlmax) = true := by decide +kernel

/-- What the misaligned library needs (`LibRvU.NormThmRvU`), for every `vlmax` and byte offsets `mi, mo < 8`. -/
theorem norm_thmU (vlmax mi mo : Nat) (hmi : mi < 8) (hmo : mo < 8) :
    LibRvU.NormThmRvU vlmax mi mo rodata prog 1 (fun _ c => 32 + c * iterSteps mi mo) := by
  intro off count input S hE hb hpc
  obtain ⟨⟨g, k, z, cf, n, v, l, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩ := hE
  have hE' : EntryU mi mo off count input S := ⟨⟨g, k, z, cf, n, v, l, hpc, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩
  obtain ⟨hh, he, ht, hp, hd⟩ := rv64_x1_allU mi mo off count input S hmi hmo hE' hb
  show Library.Outcome _ _ _ off count input S ((Riscv.isa vlmax).run rodata prog (32 + count * iterSteps mi mo) S)
  rw [Riscv.run_vlmax vlmax 2 rodata prog scalarU]
  exact ⟨hh, he, LibRvU.words_of_bytes mo off S _ hp, Or.inl ⟨ht, hd⟩⟩

/-- `keccaktree_keccak256_rv64_x1` as a kernel of the misaligned RISC-V library (input buffer at byte
offset `mi`, output buffer at `mo`, modulo 8), at any `vlmax`. -/
def kernelU (vlmax mi mo : Nat) (hmi : mi < 8) (hmo : mo < 8) :
    Library.KernelThm (Riscv.isa vlmax) (LibRvU.EntryRvU mi mo) (DigestB mi mo) :=
  LibRvU.mkKernelRvU vlmax mi mo (LibTable.sym "rv64_x1") 0 rodata prog 1 (fun _ c => 32 + c * iterSteps mi mo)
    (Riscv.vlAnn RvVl.rv64_x1) RvVl.rv64_x1_ok RvVl.entries.1 (norm_thmU vlmax mi mo hmi hmo)

/-- Under any vector-length choice (`Riscv.isaCh`): the same run. -/
theorem norm_thmU_ch (vlmax mi mo : Nat) (ch : Nat → Nat) (hmi : mi < 8) (hmo : mo < 8) :
    LibRvU.NormThmRvUCh vlmax mi mo ch rodata prog 1 (fun _ c => 32 + c * iterSteps mi mo) := by
  intro off count input S hE hb hpc
  have h := norm_thmU vlmax mi mo hmi hmo off count input S hE hb hpc
  show Library.Outcome _ _ _ off count input S ((Riscv.isaCh vlmax ch).run rodata prog (32 + count * iterSteps mi mo) S)
  rw [Riscv.run_ch_scalar vlmax ch rodata prog scalarU]
  exact h

def kernelU_ch (vlmax mi mo : Nat) (ch : Nat → Nat) (hmi : mi < 8) (hmo : mo < 8) :
    Library.KernelThm (Riscv.isaCh vlmax ch) (LibRvU.EntryRvU mi mo) (DigestB mi mo) :=
  LibRvU.mkKernelRvUCh vlmax mi mo ch (LibTable.sym "rv64_x1") 0 rodata prog 1 (fun _ c => 32 + c * iterSteps mi mo)
    (Riscv.vlAnn RvVl.rv64_x1) RvVl.rv64_x1_ok RvVl.entries.1 (norm_thmU_ch vlmax mi mo ch hmi hmo)

end Keccaktree.Kernels.Rv64X1.AllU
