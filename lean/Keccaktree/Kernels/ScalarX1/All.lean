import Keccaktree.Kernels.ScalarX1.GenSE1.Seg
import Keccaktree.Kernels.ScalarX1.GenSB.Seg
import Keccaktree.Kernels.ScalarX1.GenSX.Seg
import Keccaktree.Asm.KernelGlue
import Keccaktree.Asm.ArmSteps
import Keccaktree.Asm.ArmFlags
import Keccaktree.Asm.Nodes
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_scalar_x1` (AArch64) on any number of nodes

The kernel is a frame (`stp` of the callee-saved registers, `cbz x2`), a loop whose body hashes
one node (it spills `x0, x1` and the count `x2` to the stack, hashes, reloads them and advances
both pointers), a `subs x2, x2, #1; b.ne` back edge and the epilogue (`ldp` restores, `ret`).
Three generated segments (`GenSE1` entry, `GenSB` body, `GenSX` epilogue) are each proved once,
symbolically, at every relocated position; none of them reads or writes the flags, so each runs
from any flags (`seg_flags`; the loop head is reached with the entry flags and with the flags of
`subs`).  The count steps are the concrete lemmas of `ArmSteps`; the loop is an induction over
the iterations, iteration `k` running the body relocated by `k` nodes.

**Result** (`scalar_x1_all`): for every count `c` and node offset `off` with `64·(off+c) ≤ 2^54`,
from an entry state (`Entry`: any flags), `14 + 2437·c` steps halt without a model fault and
without a tail call, keep the output words before node `off`, and leave in output words
`4(off+n)+w` the keccak256 digest of input node `off+n`, for every `n < c`.
-/
namespace Keccaktree.Kernels.ScalarX1.All
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.Nodes Keccaktree.Proof Keccak
open Keccaktree.Kernels.ScalarX1 (prog rodata)

/-- The state with the flags of the closed control state `sc` (the flags a segment was recorded with). -/
@[reducible] def norm (S sc : State (BitVec 64)) : State (BitVec 64) := S.withFlags sc.zf sc.cf sc.nf sc.vf

/-- The entry state of a call `keccaktree_keccak256_scalar_x1(out, in, count)` at node offset `off`
(AAPCS64): `x0`/`x1` at node `off` of the output/input regions, `x2 = count`, `sp` at the top of
the stack region, the input region holding the message, the control part of a fresh call except
the flags (any).  The vector registers, the other general registers and every other memory word
are arbitrary. -/
structure Entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.vl = 0 ∧ S.pc = 0 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  x2 : S.getGD 2 = gprWord ⟨0, count⟩
  sp : S.getGD 31 = gprWord ⟨rStack, 1048576⟩
  x1 : S.getGD 1 = gprWord ⟨rInput, 64 * off⟩
  x0 : S.getGD 0 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The body's input invariant at node `m`, from the message. -/
theorem body_inv0 (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat) (hin : ∀ q, S.mem rInput q = input q) :
    GenSB.Inv0 (fun i => envOf S ((rho m).var i)) (fun _ => absorbNode (nodeWords input m)) := by
  have key : ∀ q : Int, envOf S ((rho m).var (memVar rInput q)) = input (q + 8 * (m : Int)) := by
    intro q; rw [rho_var_in, envOf_mem, hin]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, absorbNode_lane8 _, absorbNode_lane9 _, absorbNode_lane10 _,
    absorbNode_lane11 _, absorbNode_lane12 _, absorbNode_lane13 _, absorbNode_lane14 _, absorbNode_lane15 _,
    absorbNode_lane16 _, absorbNode_lane17 _, absorbNode_lane18 _, absorbNode_lane19 _, absorbNode_lane20 _,
    absorbNode_lane21 _, absorbNode_lane22 _, absorbNode_lane23 _, absorbNode_lane24 _⟩
  all_goals
    show envOf S ((rho m).var (memVar rInput _)) = _
    rw [key]
    simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, absorbNode_lane0, absorbNode_lane1, absorbNode_lane2,
      absorbNode_lane3, absorbNode_lane4, absorbNode_lane5, absorbNode_lane6, absorbNode_lane7, nodeWords, rotl0]
    congr 1
    simp only [Int.ofNat_eq_coe]
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The body's output invariant at node `m` is the digest of node `m`. -/
theorem body_digest (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat)
    (h : GenSB.Inv25 (fun i => envOf S ((rho m).var i)) (GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25)) :
    Digest input S m := by
  have key : ∀ w : Nat, envOf S ((rho m).var (memVar rOutput (Int.ofNat (4 * 0 + w)))) = S.mem rOutput (Int.ofNat (4 * m + w)) := by
    intro w; rw [rho_var_out, envOf_mem]; congr 1; simp only [Int.ofNat_eq_coe]; omega
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hw : ∀ w : Nat, w < 4 → S.mem rOutput (Int.ofNat (4 * m + w)) =
      L (GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25 ⟨0, by decide⟩) w := by
    intro w hw
    rw [← key w]
    rcases w with _ | _ | _ | _ | w
    · have := h0; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h1; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h2; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h3; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · omega
  intro w i hw' hi
  have hr : GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25 ⟨0, by decide⟩ =
      Spec.rounds 24 (absorbNode (nodeWords input m)) := GenSB.aat_0 _
  rw [hw w hw', hr, absorbNode_keccak, squeezeByte_eq]
  have e1 : (8 * w + i) / 8 = w := by omega
  have e2 : (8 * w + i) % 8 = i := by omega
  rw [e1, e2]
  simp only [Spec.keccakF, Fin.val_mk]

/-! ## The loop -/

/-- The state at the loop head before iteration `k` (of a call on `c` nodes at offset `off` from
`S0`): with the recorded flags, the body's start cut relocated by `off + k`; the count `c - k` in
`x2`, the message, the earlier output words, and the digests of the nodes done. -/
@[reducible] def Head (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (k : Nat) (S : State (BitVec 64)) : Prop :=
  relocState (rho (off + k)) (cutOf GenSB.ctl0 GenSB.sc0) = cutOf GenSB.ctl0 (norm S GenSB.sc0) ∧ SliceCert.Ok S ∧
  S.getGD 2 = gprWord ⟨0, (c : Int) - k⟩ ∧ (∀ q, S.mem rInput q = input q) ∧
  (∀ q : Int, q < 4 * (off : Int) → S.mem rOutput q = S0.mem rOutput q) ∧
  (∀ n, n < k → Digest input S (off + n))

/-- The state at the epilogue: its start cut (with the recorded flags, relocated by `m` nodes),
the earlier output words, and every digest. -/
@[reducible] def ExitAt (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (S : State (BitVec 64)) : Prop :=
  relocState (rho m) (cutOf GenSX.ctl0 GenSX.sc0) = cutOf GenSX.ctl0 (norm S GenSX.sc0) ∧ SliceCert.Ok S ∧
  (∀ q : Int, q < 4 * (off : Int) → S.mem rOutput q = S0.mem rOutput q) ∧
  (∀ n, n < c → Digest input S (off + n))

theorem body_len : GenSB.segLen = 2435 := by decide +kernel
theorem prog_2442 : prog.getD 2442 .nop = .subs 2 2 1 := by decide +kernel
theorem prog_2443 : prog.getD 2443 .nop = .bcond .ne 7 := by decide +kernel

/-- The body's write condition is false outside the node's own output words and the stack. -/
theorem wok_out (q : Int) (h : q < 0 ∨ 4 ≤ q) :
    ((rOutput == 3) || (rOutput == 2 && decide (0 ≤ q) && decide (q < 4))) = false := by
  rcases h with h | h
  · rw [show decide (0 ≤ q) = false from decide_eq_false (by omega)]; rfl
  · rw [show decide (q < 4) = false from decide_eq_false (by omega)]
    cases decide (0 ≤ q) <;> rfl

theorem wf_num (c : Int) (h0 : 0 ≤ c) (h1 : c ≤ 18014398509481984) : (⟨0, c⟩ : Addr).wf := by
  show 0 ≤ c ∧ c < 2 ^ 55
  rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One iteration of the loop.** From the loop head before iteration `k < c`, `2437` steps
(body, `subs`, `b.ne`) reach the loop head before iteration `k + 1`, or the epilogue after the last. -/
theorem iter (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (k : Nat) (S : State (BitVec 64)) (hk : k < c) (hH : Head off c input S0 k S) :
    (k + 1 < c → Head off c input S0 (k + 1) (Arm.isa.run rodata prog 2437 S)) ∧
    (k + 1 = c → ExitAt off c input S0 (off + k) (Arm.isa.run rodata prog 2437 S)) := by
  obtain ⟨hcut, hok, hcnt, hin, hpre, hdig⟩ := hH
  have hρ := rho_ok (off + k)
  have hw : (rho (off + k)).within GenSB.B := rho_within (off + k) (by omega)
  have hok' : SliceCert.Ok (norm S GenSB.sc0) := hok
  have sr := GenSB.seg_run (rho (off + k)) hρ hw _ hcut hok'
  have fr := GenSB.seg_frame (rho (off + k)) hρ hw _ hcut hok'
  have dat := GenSB.seg_data (rho (off + k)) hρ hw _ hcut hok' _ (body_inv0 input (norm S GenSB.sc0) (off + k) hin)
  have mv := GenSB.seg_moves (rho (off + k)) hρ hw _ hcut hok' 258 258 (by simp)
  have fl : Arm.isa.run rodata prog GenSB.segLen S =
      (GenSB.segAt25 (norm S GenSB.sc0)).withFlags S.zf S.cf S.nf S.vf :=
    GenSB.seg_flags (rho (off + k)) hρ hw _ hcut hok' S.zf S.cf S.nf S.vf
  rw [Reloc.var_lt _ 258 (by decide)] at mv
  generalize hSb' : GenSB.segAt25 (norm S GenSB.sc0) = Sb' at sr fr dat mv fl
  obtain ⟨_, hokb, hcutb⟩ := sr
  have fb := cut_fields _ _ _ _ hcutb
  generalize hSb : Sb'.withFlags S.zf S.cf S.nf S.vf = Sb at fl
  have hSbmem : Sb.mem = Sb'.mem := by rw [← hSb]; rfl
  have hSbenv : ∀ i, envOf Sb i = envOf Sb' i := by intro i; rw [← hSb]; rfl
  have hhb : Sb.halted = false := by rw [← hSb]; exact hokb.2.1
  have hpcb : Sb.pc = 2442 := by rw [← hSb]; exact fb.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  -- the count survives the body (x2 -> [sp+112] -> x2)
  have hcntb : Sb.getGD 2 = gprWord ⟨0, (c : Int) - k⟩ := by
    have e1 : envOf Sb 258 = Sb.getGD 2 := envOf_gdVar Sb 2 (by decide)
    have e2 : envOf (norm S GenSB.sc0) 258 = (norm S GenSB.sc0).getGD 2 := envOf_gdVar _ 2 (by decide)
    rw [← e1, hSbenv, mv, e2]; exact hcnt
  have hb' : 64 * (off + c) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  -- subs x2, x2, #1
  have hsubs := Arm.exec_subs_num rodata Sb 2 2 1 ((c : Int) - k) hhb hcntb (wf_num _ (by omega) (by omega))
  generalize hV : Arm.next (Arm.setFlags (Sb.setGD 2 (gprWord ⟨0, (c : Int) - k - 1⟩)) ((c : Int) - k) 1) = V at hsubs
  have hrunV : Arm.isa.run rodata prog 1 Sb = V := by
    rw [Arm.run_one rodata prog Sb hhb, show prog.getD Sb.pc .nop = .subs 2 2 1 by rw [hpcb]; exact prog_2442, hsubs]
  have hpcV : V.pc = 2443 := by rw [← hV]; show Sb.pc + 1 = 2443; rw [hpcb]
  have hhV : V.halted = false := by rw [← hV]; exact hhb
  have hVzf : V.zf = decide ((c : Int) - k = 1) := by rw [← hV]; rfl
  -- b.ne loop
  have hrunU : Arm.isa.run rodata prog 1 V = { V with pc := if Arm.condHolds V .ne then 7 else V.pc + 1 } := by
    rw [Arm.run_one rodata prog V hhV, show prog.getD V.pc .nop = .bcond .ne 7 by rw [hpcV]; exact prog_2443]
    exact Arm.exec_bcond_eq rodata V .ne 7 hhV
  generalize hU : { V with pc := if Arm.condHolds V .ne then 7 else V.pc + 1 } = U at hrunU
  have hrun2437 : Arm.isa.run rodata prog 2437 S = U := by
    rw [show 2437 = GenSB.segLen + 1 + 1 by rw [body_len], Isa.run_add, Isa.run_add, fl, hrunV, hrunU]
  rw [hrun2437]
  -- the fields of U
  have hUmem : U.mem = Sb'.mem := by rw [← hU, ← hV]; exact hSbmem
  have hUpc : U.pc = if decide ((c : Int) - k = 1) then 2444 else 7 := by
    rw [← hU]; show (if Arm.condHolds V .ne then 7 else V.pc + 1) = _
    rw [hpcV, show Arm.condHolds V .ne = !V.zf from rfl, hVzf]
    cases decide ((c : Int) - k = 1) <;> rfl
  have hUenv : ∀ i, i ≠ 258 → envOf U i = envOf Sb' i := by
    intro i hi
    rw [← hSbenv i, ← Arm.envOf_setGD_other Sb 2 i (gprWord ⟨0, (c : Int) - k - 1⟩) (by omega), ← hU, ← hV]; rfl
  have hUcnt : U.getGD 2 = gprWord ⟨0, (c : Int) - k - 1⟩ := by
    rw [← hU, ← hV]; exact Arm.getGD_setGD_same Sb 2 _ (by decide)
  have hUg : U.g = Sb'.g.setIfInBounds 2 ⟨0, 0⟩ := by rw [← hU, ← hV, ← hSb]; rfl
  have hUc : U.k = Sb'.k ∧ U.vl = Sb'.vl ∧ U.depth = Sb'.depth := by
    rw [← hU, ← hV, ← hSb]; exact ⟨rfl, rfl, rfl⟩
  have hUok : SliceCert.Ok U := by rw [← hU, ← hV, ← hSb]; exact hokb
  have hUo : ∀ q, U.mem rOutput q = Sb'.mem rOutput q := by intro q; rw [hUmem]
  -- frames of the body
  have hbi : ∀ q, Sb'.mem rInput q = S.mem rInput q := fun q => fr rInput q rfl
  have hbo : ∀ q : Int, q - 4 * ((off + k : Nat) : Int) < 0 → Sb'.mem rOutput q = S.mem rOutput q := by
    intro q hq
    apply fr rOutput q
    rw [rho_wshift_out]
    exact wok_out _ (Or.inl hq)
  have hpre' : ∀ q : Int, q < 4 * (off : Int) → U.mem rOutput q = S0.mem rOutput q := by
    intro q hq; rw [hUo, hbo q (by omega)]; exact hpre q hq
  have hdig' : ∀ n, n < k + 1 → Digest input U (off + n) := by
    intro n hn
    by_cases hnk : n < k
    · apply digest_congr input S U (off + n) _ (hdig n hnk)
      intro w hw; rw [hUo]; exact hbo _ (by simp only [Int.ofNat_eq_coe]; omega)
    · have hnk' : n = k := by omega
      rw [hnk']
      apply digest_congr input Sb' U (off + k) (fun w _ => hUo _)
      exact body_digest input Sb' (off + k) dat
  have hL : ∀ L' : List Nat, (L'.all fun i => decide (i ≠ 258)) = true →
      ∀ i ∈ L', envOf (norm U GenSB.sc0) i = envOf Sb' i := by
    intro L' hL' i hi
    have hne : i ≠ 258 := by have := List.all_eq_true.mp hL' i hi; simpa using this
    exact hUenv i hne
  have hLx : ∀ L' : List Nat, (L'.all fun i => decide (i ≠ 258)) = true →
      ∀ i ∈ L', envOf (norm U GenSX.sc0) i = envOf Sb' i := by
    intro L' hL' i hi
    have hne : i ≠ 258 := by have := List.all_eq_true.mp hL' i hi; simpa using this
    exact hUenv i hne
  refine ⟨fun hk1 => ?_, fun hk1 => ?_⟩
  · -- back to the loop head, one node further
    have hz : decide ((c : Int) - k = 1) = false := decide_eq_false (by omega)
    refine ⟨?_, hUok, ?_, fun q => by rw [hUmem, hbi]; exact hin q, hpre', hdig'⟩
    · rw [show off + (k + 1) = (off + k) + 1 by omega, ← rho_add]
      apply cut_transfer (rho (off + k)) _ hρ (Reloc.add_ok _ _ hρ (rho_ok 1)) GenSB.ctl25 GenSB.ctl0 GenSB.sc25 GenSB.sc0 Sb' _ hcutb
        (hL_dec _ _ (by decide +kernel)) (hL _ (by decide +kernel))
        (hval_succ _ _ hρ (rho_ok 1) _ _ _ _ (by decide +kernel))
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show U.g = _; rw [hUg, fb.1]; decide +kernel
      · show U.k = _; rw [hUc.1, fb.2.1]; decide +kernel
      · show U.vl = _; rw [hUc.2.1, fb.2.2.2.2.2.2.1]; decide +kernel
      · show U.pc = _; rw [hUpc, hz]; decide +kernel
      · show U.depth = _; rw [hUc.2.2, fb.2.2.2.2.2.2.2.2]; decide +kernel
    · rw [hUcnt]
      exact congrArg (fun z : Int => gprWord ⟨0, z⟩) (by omega)
  · -- the last iteration: on to the epilogue
    have hz : decide ((c : Int) - k = 1) = true := decide_eq_true (by omega)
    refine ⟨?_, hUok, hpre', ?_⟩
    · apply cut_transfer (rho (off + k)) _ hρ hρ GenSB.ctl25 GenSX.ctl0 GenSB.sc25 GenSX.sc0 Sb' _ hcutb
        (hL_dec _ _ (by decide +kernel)) (hLx _ (by decide +kernel))
        (hval_same _ _ _ _ _ (by decide +kernel))
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show U.g = _; rw [hUg, fb.1]; decide +kernel
      · show U.k = _; rw [hUc.1, fb.2.1]; decide +kernel
      · show U.vl = _; rw [hUc.2.1, fb.2.2.2.2.2.2.1]; decide +kernel
      · show U.pc = _; rw [hUpc, hz]; decide +kernel
      · show U.depth = _; rw [hUc.2.2, fb.2.2.2.2.2.2.2.2]; decide +kernel
    · intro n hn; exact hdig' n (by omega)

/-- **The loop**: from the loop head before iteration `k`, the remaining `d + 1 = c - k` iterations
reach the epilogue with every digest written. -/
theorem loop (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ d k (S : State (BitVec 64)), k + d + 1 = c → Head off c input S0 k S →
      ExitAt off c input S0 (off + c - 1) (Arm.isa.run rodata prog (2437 * (d + 1)) S) := by
  intro d
  induction d with
  | zero =>
    intro k S hk hH
    have := (iter off c input S0 hb k S (by omega) hH).2 (by omega)
    rw [show off + c - 1 = off + k by omega, show 2437 * (0 + 1) = 2437 from rfl]
    exact this
  | succ d ih =>
    intro k S hk hH
    have h1 := (iter off c input S0 hb k S (by omega) hH).1 (by omega)
    rw [show 2437 * (d + 1 + 1) = 2437 + 2437 * (d + 1) by omega, Isa.run_add]
    exact ih (k + 1) _ (by omega) h1

theorem exit_len : GenSX.segLen = 6 := by decide +kernel
theorem prog_2450 : prog.getD 2450 .nop = .ret := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The epilogue**: `ldp ×6; ret` halts with the memory unchanged. -/
theorem epilogue (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (hm : 64 * m ≤ 2 ^ 54)
    (U : State (BitVec 64)) (hX : ExitAt off c input S0 m U) :
    (Arm.isa.run rodata prog 7 U).halted = true ∧ (Arm.isa.run rodata prog 7 U).err = false ∧
    (Arm.isa.run rodata prog 7 U).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (Arm.isa.run rodata prog 7 U).mem rOutput q = S0.mem rOutput q) ∧
    ∀ n, n < c → Digest input (Arm.isa.run rodata prog 7 U) (off + n) := by
  obtain ⟨hcut, hok, hpre, hdig⟩ := hX
  have hρ := rho_ok m
  have hw : (rho m).within GenSX.B := rho_within m hm
  have hok' : SliceCert.Ok (norm U GenSX.sc0) := hok
  have sr := GenSX.seg_run (rho m) hρ hw _ hcut hok'
  have fr := GenSX.seg_frame (rho m) hρ hw _ hcut hok'
  have fl : Arm.isa.run rodata prog GenSX.segLen U = (GenSX.segAt1 (norm U GenSX.sc0)).withFlags U.zf U.cf U.nf U.vf :=
    GenSX.seg_flags (rho m) hρ hw _ hcut hok' U.zf U.cf U.nf U.vf
  generalize hSx' : GenSX.segAt1 (norm U GenSX.sc0) = Sx' at sr fr fl
  obtain ⟨_, hokx, hcutx⟩ := sr
  have fx := cut_fields _ _ _ _ hcutx
  generalize hSx : Sx'.withFlags U.zf U.cf U.nf U.vf = Sx at fl
  have hpc : Sx.pc = 2450 := by rw [← hSx]; exact fx.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hhx : Sx.halted = false := by rw [← hSx]; exact hokx.2.1
  have hr : Arm.isa.run rodata prog 7 U = { Sx with halted := true } := by
    rw [show 7 = GenSX.segLen + 1 by rw [exit_len], Isa.run_add, fl, Arm.run_one rodata prog Sx hhx,
      show prog.getD Sx.pc .nop = .ret by rw [hpc]; exact prog_2450, Arm.exec_ret_eq rodata Sx hhx]
  have hmem : ∀ r q, Sx.mem r q = U.mem r q := by intro r q; rw [← hSx]; exact fr r q rfl
  rw [hr]
  refine ⟨rfl, ?_, ?_, fun q hq => (hmem _ _).trans (hpre q hq), fun n hn => ?_⟩
  · rw [← hSx]; exact hokx.1
  · rw [← hSx]; exact hokx.2.2
  exact digest_congr input U _ _ (fun w _ => hmem _ _) (hdig n hn)

/-! ## The whole call -/

theorem e1_len : GenSE1.segLen = 6 := by decide +kernel
theorem prog_6 : prog.getD 6 .nop = .cbz 2 2444 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`keccaktree_keccak256_scalar_x1` on any number of nodes.**  For every count `c` and node
offset `off` with `64·(off + c) ≤ 2^54`, from an entry state (any flags), `14 + 2437·c` steps of
the fetch-execute loop halt without a model fault and without a tail call, keep the output words
before node `off`, and leave the keccak256 digest of input node `off + n` in output words
`4(off+n) .. 4(off+n)+3`, for every `n < c`. -/
theorem scalar_x1_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    (Arm.isa.run rodata prog (14 + 2437 * c) S).halted = true ∧
    (Arm.isa.run rodata prog (14 + 2437 * c) S).err = false ∧
    (Arm.isa.run rodata prog (14 + 2437 * c) S).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (Arm.isa.run rodata prog (14 + 2437 * c) S).mem rOutput q = S.mem rOutput q) ∧
    ∀ n, n < c → Digest input (Arm.isa.run rodata prog (14 + 2437 * c) S) (off + n) := by
  have hρ := rho_ok off
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hwf_in : (⟨rInput, 64 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 64 * (off : Int) ∧ 64 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hwf_out : (⟨rOutput, 32 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 32 * (off : Int) ∧ 32 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  -- the entry cut (with the recorded flags), at node offset `off`
  have hc0 : relocState (rho off) (cutOf GenSE1.ctl0 GenSE1.sc0) = cutOf GenSE1.ctl0 (norm S GenSE1.sc0) := by
    apply relocState_cutOf (rho off) GenSE1.ctl0 GenSE1.sc0 (norm S GenSE1.sc0)
    · intro i hi
      simp only [GenSE1.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · rw [cutVar_ptr_of GenSE1.ctl0 (norm S GenSE1.sc0) 256 ⟨rOutput, 32 * (off : Int)⟩ (by decide) ((envOf_gdVar (norm S GenSE1.sc0) 0 (by decide)).trans hE.x0) hwf_out (by show rOutput ≠ 0; decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 256 = .ptr ⟨rOutput, 0⟩ by decide +kernel, reloc_ptr_out, Int.zero_add]
      · rw [cutVar_ptr_of GenSE1.ctl0 (norm S GenSE1.sc0) 257 ⟨rInput, 64 * (off : Int)⟩ (by decide) ((envOf_gdVar (norm S GenSE1.sc0) 1 (by decide)).trans hE.x1) hwf_in (by show rInput ≠ 0; decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 257 = .ptr ⟨rInput, 0⟩ by decide +kernel, reloc_ptr_in, Int.zero_add]
      · rw [cutVar_ptr_of GenSE1.ctl0 (norm S GenSE1.sc0) 287 ⟨rStack, 1048576⟩ (by decide) ((envOf_gdVar (norm S GenSE1.sc0) 31 (by decide)).trans hE.sp) (by decide) (by decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 287 = .ptr ⟨rStack, 1048576⟩ by decide +kernel, reloc_ptr_stack]
    · intro i hi h; simp only [GenSE1.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
    · obtain ⟨g, k, l, p, d⟩ := hE.ctrl
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show S.g = _; rw [g]; decide +kernel
      · show S.k = _; rw [k]; decide +kernel
      · show S.vl = _; rw [l]; decide +kernel
      · show S.pc = _; rw [p]; decide +kernel
      · show S.depth = _; rw [d]; decide +kernel
  -- E1: the frame
  have hw0 : (rho off).within (2 ^ 54) := rho_within off (by omega)
  have hok0 : SliceCert.Ok (norm S GenSE1.sc0) := hE.ok
  have s1 := GenSE1.seg_run (rho off) hρ hw0 _ hc0 hok0
  have f1 := GenSE1.seg_frame (rho off) hρ hw0 _ hc0 hok0
  have m1 := GenSE1.seg_moves (rho off) hρ hw0 _ hc0 hok0 258 258 (by simp)
  have fl1 : Arm.isa.run rodata prog GenSE1.segLen S = (GenSE1.segAt1 (norm S GenSE1.sc0)).withFlags S.zf S.cf S.nf S.vf :=
    GenSE1.seg_flags (rho off) hρ hw0 _ hc0 hok0 S.zf S.cf S.nf S.vf
  rw [Reloc.var_lt _ 258 (by decide)] at m1
  generalize hT1' : GenSE1.segAt1 (norm S GenSE1.sc0) = T1' at s1 f1 m1 fl1
  obtain ⟨_, hok1, hcut1⟩ := s1
  have ft1 := cut_fields _ _ _ _ hcut1
  generalize hT1 : T1'.withFlags S.zf S.cf S.nf S.vf = T1 at fl1
  have hx2' : T1'.getGD 2 = gprWord ⟨0, c⟩ := by
    have e1 : envOf T1' 258 = T1'.getGD 2 := envOf_gdVar T1' 2 (by decide)
    have e2 : envOf (norm S GenSE1.sc0) 258 = (norm S GenSE1.sc0).getGD 2 := envOf_gdVar _ 2 (by decide)
    rw [← e1, m1, e2]; exact hE.x2
  have hx2 : T1.getGD 2 = gprWord ⟨0, c⟩ := by rw [← hT1]; exact hx2'
  have hpc1 : T1.pc = 6 := by rw [← hT1]; exact ft1.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hh1 : T1.halted = false := by rw [← hT1]; exact hok1.2.1
  -- cbz x2
  have hcbz := Arm.exec_cbz_num rodata T1 2 2444 c hh1 hx2 (wf_num _ (by omega) (by omega))
  have hrunT2 : Arm.isa.run rodata prog 1 T1 = { T1 with pc := if (c : Int) = 0 then 2444 else T1.pc + 1 } := by
    rw [Arm.run_one rodata prog T1 hh1, show prog.getD T1.pc .nop = .cbz 2 2444 by rw [hpc1]; exact prog_6, hcbz]
  generalize hT2 : { T1 with pc := if (c : Int) = 0 then 2444 else T1.pc + 1 } = T2 at hrunT2
  have hT2pc : T2.pc = if (c : Int) = 0 then 2444 else 7 := by rw [← hT2]; show (if (c : Int) = 0 then 2444 else T1.pc + 1) = _; rw [hpc1]
  have hT2env : ∀ i, envOf T2 i = envOf T1' i := by intro i; rw [← hT2, ← hT1]; rfl
  have hT2mem : T2.mem = T1'.mem := by rw [← hT2, ← hT1]; rfl
  have hT2c : T2.g = T1'.g ∧ T2.k = T1'.k ∧ T2.vl = T1'.vl ∧ T2.depth = T1'.depth := by
    rw [← hT2, ← hT1]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hT2ok : SliceCert.Ok T2 := by rw [← hT2, ← hT1]; exact hok1
  have hT2x2 : T2.getGD 2 = gprWord ⟨0, c⟩ := by rw [← hT2]; exact hx2
  have h7 : Arm.isa.run rodata prog 7 S = T2 := by
    rw [show 7 = GenSE1.segLen + 1 by rw [e1_len], Isa.run_add, fl1, hrunT2]
  have hpre2 : ∀ q : Int, T2.mem rOutput q = S.mem rOutput q := by
    intro q; rw [hT2mem]; exact f1 rOutput q rfl
  have hin2 : ∀ q : Int, T2.mem rInput q = input q := by
    intro q; rw [hT2mem, f1 rInput q rfl]; exact hE.inp q
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- no node: straight to the epilogue
    subst hc
    have hX : ExitAt off 0 input S off T2 := by
      refine ⟨?_, hT2ok, fun q _ => hpre2 q, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      apply cut_transfer (rho off) (rho off) hρ hρ GenSE1.ctl1 GenSX.ctl0 GenSE1.sc1 GenSX.sc0 T1' (norm T2 GenSX.sc0) hcut1
        (hL_dec _ _ (by decide +kernel)) (fun i _ => hT2env i) (hval_same _ _ _ _ _ (by decide +kernel))
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show T2.g = _; rw [hT2c.1, ft1.1]; decide +kernel
      · show T2.k = _; rw [hT2c.2.1, ft1.2.1]; decide +kernel
      · show T2.vl = _; rw [hT2c.2.2.1, ft1.2.2.2.2.2.2.1]; decide +kernel
      · show T2.pc = _; rw [hT2pc]; decide +kernel
      · show T2.depth = _; rw [hT2c.2.2.2, ft1.2.2.2.2.2.2.2.2]; decide +kernel
    have he := epilogue off 0 input S off (by omega) T2 hX
    rw [show 14 + 2437 * 0 = 7 + 7 by rfl, Isa.run_add, h7]
    exact he
  · -- the loop and the epilogue
    have hz : ((c : Int) = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
    have hH : Head off c input S 0 T2 := by
      refine ⟨?_, hT2ok, ?_, hin2, fun q _ => hpre2 q, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      · apply cut_transfer (rho off) (rho (off + 0)) hρ hρ GenSE1.ctl1 GenSB.ctl0 GenSE1.sc1 GenSB.sc0 T1' (norm T2 GenSB.sc0) hcut1
          (hL_dec _ _ (by decide +kernel)) (fun i _ => hT2env i) (hval_same _ _ _ _ _ (by decide +kernel))
        refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
        · show T2.g = _; rw [hT2c.1, ft1.1]; decide +kernel
        · show T2.k = _; rw [hT2c.2.1, ft1.2.1]; decide +kernel
        · show T2.vl = _; rw [hT2c.2.2.1, ft1.2.2.2.2.2.2.1]; decide +kernel
        · show T2.pc = _; rw [hT2pc, if_neg (by omega)]; decide +kernel
        · show T2.depth = _; rw [hT2c.2.2.2, ft1.2.2.2.2.2.2.2.2]; decide +kernel
      · rw [hT2x2]; simp
    have hl := loop off c input S hb (c - 1) 0 T2 (by omega) hH
    rw [show c - 1 + 1 = c by omega] at hl
    have he := epilogue off c input S (off + c - 1) (by omega) _ hl
    rw [show 14 + 2437 * c = 7 + 2437 * c + 7 by omega, Isa.run_add, Isa.run_add, h7]
    exact he

/-! ## In the library -/

/-- The AArch64 calling convention of the library at node offset `off` (within the address bound). -/
def EntryArm (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  Entry off count input { S with pc := 0 } ∧ 64 * (off + count) ≤ 2 ^ 54

/-- `keccaktree_keccak256_scalar_x1` as a kernel of the library (rank 0: it hands nothing over). -/
def kernel : Library.KernelThm Arm.isa EntryArm Digest where
  name := "keccaktree_keccak256_scalar_x1"
  rank := 0
  rodata := rodata
  prog := prog
  entry := 0
  steps := fun _ c => 14 + 2437 * c
  thm := fun off count input S h => by
    obtain ⟨hh, he, ht, hp, hd⟩ := scalar_x1_all off count input _ h.1 h.2
    exact ⟨hh, he, hp, Or.inl ⟨ht, hd⟩⟩

theorem ranks_ok : Library.RanksOk [kernel] := by
  intro K hK off count input S hS next done htail _
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
  subst hK
  have ht : (Arm.isa.run rodata prog (14 + 2437 * count) { S with pc := 0 }).tail = none :=
    (scalar_x1_all off count input _ hS.1 hS.2).2.2.1
  have h := ht.symm.trans htail
  cases h

/-- **The library theorem on the table `[scalar_x1]`**. -/
theorem lib_scalar_x1 (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hS : EntryArm "keccaktree_keccak256_scalar_x1" off count input S) : Library.LibOk [kernel] kernel off count input S :=
  Library.lib_correct [kernel] 0 (by simp [kernel]) ranks_ok digest_local _ kernel (by simp) off count input S
    (Nat.le_refl _) hS

end Keccaktree.Kernels.ScalarX1.All
