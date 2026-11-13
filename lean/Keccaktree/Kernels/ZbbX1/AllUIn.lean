import Keccaktree.Kernels.ZbbX1.GenSE.Seg
import Keccaktree.Kernels.ZbbX1.GenSI.Seg
import Keccaktree.Kernels.ZbbX1.GenSJ.Seg
import Keccaktree.Kernels.ZbbX1.GenSC.Slice0
import Keccaktree.Kernels.RiscvBytes
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_zbb_x1` on any number of nodes, at any buffer alignment

The input buffer starts at byte `mi` and the output buffer at byte `mo` of their regions (any
`mi, mo < 8`; the machine address of a buffer is `≡ mi` resp. `mo (mod 8)`), node offset `off`.
Per node the kernel loads the input pointer and tests its low 3 bits: if they are zero it loads the
node's 8 words directly (`GenSI`), else it copies the 64 bytes into a bounce buffer on the stack
(`COPY_BYTES`, `lbu`/`sb`; `RiscvBytes.copy_loop`) and loads from there (`GenSJ`).  The constant lanes
and the 24 rounds (`GenSC`) are the same code for both.  The digest goes directly into the output
(`sd` × 4) if the output pointer is aligned, else through the bounce buffer and `COPY_BYTES`.  The
loop head, the copies, the digest stores and the back edge are concrete steps (`RiscvBytes.St`); the
segments are proved once, symbolically, at every relocated position.

**Result** (`zbb_x1_allU`): from an entry state (`EntryU`), `32 + c·(3443 + 387·[mi ≠ 0] + 193·[mo ≠ 0])`
steps halt without a model fault and without a tail call, keep the output bytes before byte
`mo + 32·off`, and leave in output bytes `mo + 32(off+n) …` the keccak256 digest of the input node at
byte `mi + 64(off+n)`, for every `n < c` (`DigestB`).  With `mi = mo = 0` this is `zbb_x1_all`.
-/
namespace Keccaktree.Kernels.ZbbX1.AllU
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon Keccaktree.Kernels.RiscvBytes
open Keccaktree.Asm.Riscv (setR getR brHolds run_one exec_br_num exec_j_eq exec_ret_eq getR_zero getR_pos)
open Keccaktree.Kernels.ZbbX1 (prog rodata)

abbrev RV : Isa := Riscv.isa 2

/-- The stack pointer inside the frame, and the frame's words: the bounce buffer (8 words), the spilled
output pointer, input pointer and count. -/
def SP : Int := 1048352

theorem sp_wf : (⟨rStack, SP⟩ : Addr).wf := by decide

/-! ## The calling convention -/

/-- The entry state of a call `keccaktree_keccak256_zbb_x1(out, in, count)` with the input buffer at
byte `mi + 64·off` of the input region and the output buffer at byte `mo + 32·off` of the output
region (`a1`, `a0`); otherwise as `ZbbX1.All.Entry`. -/
structure EntryU (mi mo off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.vl = 0 ∧ S.pc = 1 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  a2 : S.getGD 12 = gprWord ⟨0, count⟩
  sp : S.getGD 2 = gprWord ⟨rStack, 1048576⟩
  a1 : S.getGD 11 = gprWord ⟨rInput, mi + 64 * off⟩
  a0 : S.getGD 10 = gprWord ⟨rOutput, mo + 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

/-! ## The program -/

theorem prog_1 : prog.getD 1 .nop = .br .ne 12 0 3 := by decide +kernel
theorem prog_2 : prog.getD 2 .nop = .j 3498 := by decide +kernel
theorem prog_20 : prog.getD 20 .nop = .ld 5 2 72 := by decide +kernel
theorem prog_21 : prog.getD 21 .nop = .opi 6 5 .addi 0x40#64 := by decide +kernel
theorem prog_22 : prog.getD 22 .nop = .sd 6 2 72 := by decide +kernel
theorem prog_23 : prog.getD 23 .nop = .opi 6 5 .andi 7#64 := by decide +kernel
theorem prog_24 : prog.getD 24 .nop = .br .eq 6 0 34 := by decide +kernel
theorem prog_25 : prog.getD 25 .nop = .mv 6 2 := by decide +kernel
theorem prog_26 : prog.getD 26 .nop = .li 17 0x40#64 := by decide +kernel
theorem prog_33 : prog.getD 33 .nop = .mv 5 2 := by decide +kernel
theorem code_in : CopyCode prog 27 5 6 7 17 := by unfold CopyCode; decide +kernel
theorem prog_5388 : prog.getD 3457 .nop = .ld 5 2 64 := by decide +kernel
theorem prog_5389 : prog.getD 3458 .nop = .opi 6 5 .addi 0x20#64 := by decide +kernel
theorem prog_5390 : prog.getD 3459 .nop = .sd 6 2 64 := by decide +kernel
theorem prog_5391 : prog.getD 3460 .nop = .opi 6 5 .andi 7#64 := by decide +kernel
theorem prog_5392 : prog.getD 3461 .nop = .br .ne 6 0 3467 := by decide +kernel
theorem prog_5393 : prog.getD 3462 .nop = .sd 10 5 0 := by decide +kernel
theorem prog_5394 : prog.getD 3463 .nop = .sd 11 5 8 := by decide +kernel
theorem prog_5395 : prog.getD 3464 .nop = .sd 12 5 16 := by decide +kernel
theorem prog_5396 : prog.getD 3465 .nop = .sd 13 5 24 := by decide +kernel
theorem prog_5397 : prog.getD 3466 .nop = .j 3479 := by decide +kernel
theorem prog_5398 : prog.getD 3467 .nop = .sd 10 2 0 := by decide +kernel
theorem prog_5399 : prog.getD 3468 .nop = .sd 11 2 8 := by decide +kernel
theorem prog_5400 : prog.getD 3469 .nop = .sd 12 2 16 := by decide +kernel
theorem prog_5401 : prog.getD 3470 .nop = .sd 13 2 24 := by decide +kernel
theorem prog_5402 : prog.getD 3471 .nop = .mv 6 2 := by decide +kernel
theorem prog_5403 : prog.getD 3472 .nop = .li 17 0x20#64 := by decide +kernel
theorem code_out : CopyCode prog 3473 6 5 7 17 := by unfold CopyCode; decide +kernel
theorem prog_5410 : prog.getD 3479 .nop = .ld 5 2 80 := by decide +kernel
theorem prog_5411 : prog.getD 3480 .nop = .opi 5 5 .addi 0xffffffffffffffff#64 := by decide +kernel
theorem prog_5412 : prog.getD 3481 .nop = .sd 5 2 80 := by decide +kernel
theorem prog_5413 : prog.getD 3482 .nop = .br .eq 5 0 3484 := by decide +kernel
theorem prog_5414 : prog.getD 3483 .nop = .j 20 := by decide +kernel
theorem prog_5429 : prog.getD 3498 .nop = .ret := by decide +kernel

theorem regs_in : CopyRegs 5 6 7 17 := by unfold CopyRegs; decide
theorem regs_out : CopyRegs 6 5 7 17 := by unfold CopyRegs; decide

/-! ## Control parts of cuts -/

/-- The control fields of a state with the kernels' control part, against a cut's control state. -/
theorem ctrl_eq (sc H : State (BitVec 64)) (hC : Ctl0 H)
    (hsc : sc.g = Vector.replicate 32 ⟨0, 0⟩ ∧ sc.k = Vector.replicate 8 0 ∧ sc.zf = false ∧ sc.cf = false ∧
      sc.nf = false ∧ sc.vf = false ∧ sc.vl = 0 ∧ sc.depth = 0) (hp : H.pc = sc.pc) :
    H.g = sc.g ∧ H.k = sc.k ∧ H.zf = sc.zf ∧ H.cf = sc.cf ∧ H.nf = sc.nf ∧ H.vf = sc.vf ∧ H.vl = sc.vl ∧
      H.pc = sc.pc ∧ H.depth = sc.depth := by
  obtain ⟨g, k, z, c, n, v, l, d, -⟩ := hC
  obtain ⟨g', k', z', c', n', v', l', d'⟩ := hsc
  exact ⟨g.trans g'.symm, k.trans k'.symm, z.trans z'.symm, c.trans c'.symm, n.trans n'.symm, v.trans v'.symm,
    l.trans l'.symm, hp, d.trans d'.symm⟩

/-- The kernels' control part at the end of a segment. -/
theorem ctl0_of_cut (ρ : Reloc) (ctl : List Nat) (sc C : State (BitVec 64)) (h : relocState ρ (cutOf ctl sc) = cutOf ctl C)
    (hok : SliceCert.Ok C)
    (hsc : sc.g = Vector.replicate 32 ⟨0, 0⟩ ∧ sc.k = Vector.replicate 8 0 ∧ sc.zf = false ∧ sc.cf = false ∧
      sc.nf = false ∧ sc.vf = false ∧ sc.vl = 0 ∧ sc.depth = 0) : Ctl0 C ∧ C.pc = sc.pc := by
  obtain ⟨g, k, z, c, n, v, l, p, d⟩ := cut_fields _ _ _ _ h
  obtain ⟨g', k', z', c', n', v', l', d'⟩ := hsc
  exact ⟨⟨g.trans g', k.trans k', z.trans z', c.trans c', n.trans n', v.trans v', l.trans l', d.trans d', hok.1, hok.2.1,
    hok.2.2⟩, p⟩

/-- The stack pointer at the end of a segment whose end cut holds it. -/
theorem sp_of_cut (ρ : Reloc) (hρ : ρ.ok) (ctl : List Nat) (sc C : State (BitVec 64))
    (h : relocState ρ (cutOf ctl sc) = cutOf ctl C) (hm : 258 ∈ ctl) (hv : cutVar ctl sc 258 = .ptr ⟨rStack, SP⟩) :
    C.getGD 2 = gprWord ⟨rStack, SP⟩ := by
  have e1 := cut_word ρ hρ ctl sc C h 258 (Or.inl (by decide))
  rw [hv] at e1
  rw [show E.reloc ρ (.ptr ⟨rStack, SP⟩) = .ptr ⟨rStack, SP⟩ from congrArg E.ptr (Reloc.addr_stack ρ hρ _ rfl)] at e1
  rw [← envOf_gdVar C 2 (by decide)]
  exact cut_ptr ctl C 258 hm _ e1

/-! ## The node words and the digest -/

/-- The absorbed state of node `j` of the message at byte offset `mi`. -/
abbrev AN (input : Int → BitVec 64) (mi j : Nat) : Fin 1 → Spec.State := fun _ => absorbNode (nodeWordsB input mi j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The rounds' input invariant from the 8 node words in registers `x10..x17`.  -/
theorem core_inv0 (input : Int → BitVec 64) (mi j : Nat) (env : Nat → BitVec 64)
    (h : ∀ w : Nat, w < 8 → env (gdVar (10 + w)) = nodeWordsB input mi j w) :
    GenSC.Inv0 env (AN input mi j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, absorbNode_lane8 _, absorbNode_lane9 _, absorbNode_lane10 _,
    absorbNode_lane11 _, absorbNode_lane12 _, absorbNode_lane13 _, absorbNode_lane14 _, absorbNode_lane15 _,
    absorbNode_lane16 _, absorbNode_lane17 _, absorbNode_lane18 _, absorbNode_lane19 _, absorbNode_lane20 _,
    absorbNode_lane21 _, absorbNode_lane22 _, absorbNode_lane23 _, absorbNode_lane24 _⟩
  all_goals
    simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, absorbNode_lane0, absorbNode_lane1, absorbNode_lane2,
      absorbNode_lane3, absorbNode_lane4, absorbNode_lane5, absorbNode_lane6, absorbNode_lane7, rotl0]
  · exact h 0 (by decide)
  · exact h 1 (by decide)
  · exact h 2 (by decide)
  · exact h 3 (by decide)
  · exact h 4 (by decide)
  · exact h 5 (by decide)
  · exact h 6 (by decide)
  · exact h 7 (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The aligned load's input invariant: the input words of node `j`. -/
theorem in_inv0 (input : Int → BitVec 64) (j : Nat) (env : Nat → BitVec 64)
    (h : ∀ w : Nat, w < 8 → env (memVar rInput (Int.ofNat (8 * 0 + w))) = nodeWordsB input 0 j w) :
    GenSI.Inv0 env (AN input 0 j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, absorbNode_lane8 _, absorbNode_lane9 _, absorbNode_lane10 _,
    absorbNode_lane11 _, absorbNode_lane12 _, absorbNode_lane13 _, absorbNode_lane14 _, absorbNode_lane15 _,
    absorbNode_lane16 _, absorbNode_lane17 _, absorbNode_lane18 _, absorbNode_lane19 _, absorbNode_lane20 _,
    absorbNode_lane21 _, absorbNode_lane22 _, absorbNode_lane23 _, absorbNode_lane24 _⟩
  all_goals
    simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, absorbNode_lane0, absorbNode_lane1, absorbNode_lane2,
      absorbNode_lane3, absorbNode_lane4, absorbNode_lane5, absorbNode_lane6, absorbNode_lane7, rotl0]
  · exact h 0 (by decide)
  · exact h 1 (by decide)
  · exact h 2 (by decide)
  · exact h 3 (by decide)
  · exact h 4 (by decide)
  · exact h 5 (by decide)
  · exact h 6 (by decide)
  · exact h 7 (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The bounce-buffer load's input invariant: the buffer words are the node words. -/
theorem buf_inv0 (input : Int → BitVec 64) (mi j : Nat) (env : Nat → BitVec 64)
    (h : ∀ w : Nat, w < 8 → env (memVar 3 (131044 + (w : Int))) = nodeWordsB input mi j w) :
    GenSJ.Inv0 env (AN input mi j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, absorbNode_lane8 _, absorbNode_lane9 _, absorbNode_lane10 _,
    absorbNode_lane11 _, absorbNode_lane12 _, absorbNode_lane13 _, absorbNode_lane14 _, absorbNode_lane15 _,
    absorbNode_lane16 _, absorbNode_lane17 _, absorbNode_lane18 _, absorbNode_lane19 _, absorbNode_lane20 _,
    absorbNode_lane21 _, absorbNode_lane22 _, absorbNode_lane23 _, absorbNode_lane24 _⟩
  all_goals
    simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, absorbNode_lane0, absorbNode_lane1, absorbNode_lane2,
      absorbNode_lane3, absorbNode_lane4, absorbNode_lane5, absorbNode_lane6, absorbNode_lane7, rotl0]
  · exact h 0 (by decide)
  · exact h 1 (by decide)
  · exact h 2 (by decide)
  · exact h 3 (by decide)
  · exact h 4 (by decide)
  · exact h 5 (by decide)
  · exact h 6 (by decide)
  · exact h 7 (by decide)

theorem an_aat_si (A : Fin 1 → Spec.State) : GenSI.AAt A 1 = A := by
  funext n; obtain ⟨n, hn⟩ := n
  have : n = 0 := by omega
  subst this
  exact GenSI.aat_0 A

theorem an_aat_sj (A : Fin 1 → Spec.State) : GenSJ.AAt A 1 = A := by
  funext n; obtain ⟨n, hn⟩ := n
  have : n = 0 := by omega
  subst this
  exact GenSJ.aat_0 A

/-- The digest bytes: byte `t` of the 4 digest words `D`. -/
theorem digest_byte (input : Int → BitVec 64) (mi j : Nat) (D : Nat → BitVec 64)
    (hD : ∀ w, w < 4 → D w = L (Spec.keccakF (absorbNode (nodeWordsB input mi j))) w) (t : Nat) (ht : t < 32) :
    (D (t / 8)).extractLsb' (8 * (t % 8)) 8 = Spec.keccak256 64 (nodeBytes (nodeWordsB input mi j)) t := by
  rw [hD _ (by omega), absorbNode_keccak, squeezeByte_eq]

/-! ## One iteration -/

/-- The loop head before iteration `k` of a call on `c` nodes at node offset `off`: the kernels'
control part at the head, the stack pointer, the spilled pointers (input byte `mi + 64(off+k)`,
output byte `mo + 32(off+k)`) and count, the message, the output bytes before the call's buffer, and
the digests of the nodes done. -/
structure Head (mi mo off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (k : Nat) (S : State (BitVec 64)) :
    Prop where
  ctl : Ctl0 S
  pc : S.pc = 20
  sp : S.getGD 2 = gprWord ⟨rStack, SP⟩
  inp : S.mem rStack 131053 = gprWord ⟨rInput, mi + 64 * (off + k)⟩
  out : S.mem rStack 131052 = gprWord ⟨rOutput, mo + 32 * (off + k)⟩
  cnt : S.mem rStack 131054 = gprWord ⟨0, (c : Int) - k⟩
  msg : ∀ q, S.mem rInput q = input q
  pre : ∀ b : Int, b < mo + 32 * off → byteAt (S.mem rOutput) b = byteAt (S0.mem rOutput) b
  dig : ∀ n, n < k → DigestB mi mo input S (off + n)

/-- The state at the rounds' start (`pc = 42`) of node `j`, from a loop-head state `S`. -/
structure CoreStart (mi j : Nat) (input : Int → BitVec 64) (S P : State (BitVec 64)) : Prop where
  cut : relocState (rho j) (cutOf GenSC.ctl0 GenSC.sc0) = cutOf GenSC.ctl0 P
  ok : SliceCert.Ok P
  inv : GenSC.Inv0 (fun i => envOf P ((rho j).var i)) (AN input mi j)
  out : P.mem rStack 131052 = S.mem rStack 131052
  inp : P.mem rStack 131053 = gprWord ⟨rInput, mi + 64 * j + 64⟩
  cnt : P.mem rStack 131054 = S.mem rStack 131054
  msg : ∀ q, P.mem rInput q = S.mem rInput q
  outm : ∀ q, P.mem rOutput q = S.mem rOutput q

/-- The steps of the input part: the head, the copy if misaligned, the 8 loads. -/
def inSteps (mi : Nat) : Nat := if mi = 0 then 13 else 400

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The input part**: from the loop head of node `j` (input pointer at byte `mi + 64 j`), the head
test, the copy into the bounce buffer if the input is misaligned, and the 8 loads reach the rounds'
start with the node's words in registers. -/
theorem in_part (mi j : Nat) (input : Int → BitVec 64) (hmi : mi < 8) (hb : 64 * j + 64 ≤ 2 ^ 54)
    (S : State (BitVec 64)) (hc : Ctl0 S) (hpc : S.pc = 20) (hsp : S.getGD 2 = gprWord ⟨rStack, SP⟩)
    (hin : S.mem rStack 131053 = gprWord ⟨rInput, mi + 64 * j⟩) (hmsg : ∀ q, S.mem rInput q = input q) :
    CoreStart mi j input S (RV.run rodata prog (inSteps mi) S) := by
  have hb' : 64 * j + 64 ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hR2 : (fun r => S.getGD r) 2 = gprWord ⟨rStack, SP⟩ := hsp
  have s0 : St (RV.run rodata prog 0 S) 20 (fun r => S.getGD r) S.mem := ⟨hc, hpc, fun _ _ => rfl, rfl⟩
  -- ld t0, 72(sp); addi t1, t0, 64; sd t1, 72(sp); andi t1, t0, 7; beq t1, zero, 2f
  have hwfa : (⟨rInput, (mi : Int) + 64 * j⟩ : Addr).wf := ⟨show 0 ≤ (mi : Int) + 64 * j by omega,
    show (mi : Int) + 64 * j < 2 ^ 55 by omega⟩
  have s1 := St.ld s0 5 2 72 ⟨rStack, SP⟩ 131053 _ prog_20 (by decide) (by decide) (by decide) hR2 sp_wf (by decide)
    (by decide) (by decide) hin
  have s2 := St.addi s1 6 5 0x40#64 ⟨rInput, (mi : Int) + 64 * j⟩ ((mi : Int) + 64 * j + 64) prog_21 (by decide)
    (by decide) (by decide) (by decide) (by simp [upd]) (by rw [show (0x40#64).toInt = 64 by decide])
  have s3 := St.sd s2 6 2 72 ⟨rStack, SP⟩ 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) prog_22 (by decide)
    (by decide) (by decide) (by simp [upd]; exact hsp) sp_wf (by decide) (by decide) (by decide) (by simp [upd])
  have s4 := St.andi7 s3 6 5 ⟨rInput, (mi : Int) + 64 * j⟩ prog_23 (by decide) (by decide) (by decide) (by decide)
    (by simp [upd])
  have hm8 : ((⟨rInput, (mi : Int) + 64 * j⟩ : Addr).off % 8) = mi := by show ((mi : Int) + 64 * j) % 8 = mi; omega
  have hm8' : ((mi : Int) + 64 * (j : Int)) % 8 = mi := by omega
  have s5 := St.brz s4 .eq 6 34 mi prog_24 (by decide) (by decide) (by simp [upd, hm8, hm8'])
    ⟨show (0 : Int) ≤ mi by omega, show (mi : Int) < 2 ^ 55 by omega⟩
  -- the registers and memory after the head
  have r5_2 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) S).getGD 2 = gprWord ⟨rStack, SP⟩ :=
    (s5.regs 2 (by decide)).trans (by simp [upd]; exact hsp)
  have r5_5 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) S).getGD 5 = gprWord ⟨rInput, (mi : Int) + 64 * j⟩ :=
    (s5.regs 5 (by decide)).trans (by simp [upd])
  have hM5 : (RV.run rodata prog (0 + 1 + 1 + 1 + 1 + 1) S).mem =
      memStore S.mem rStack 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) := s5.mem
  have m5_out : memStore S.mem rStack 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) rStack 131052 =
      S.mem rStack 131052 := memStore_other _ _ _ _ _ _ (Or.inr (by decide))
  have m5_in : memStore S.mem rStack 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) rStack 131053 =
      gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩ := memStore_same _ _ _ _
  have m5_cnt : memStore S.mem rStack 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) rStack 131054 =
      S.mem rStack 131054 := memStore_other _ _ _ _ _ _ (Or.inr (by decide))
  have m5_msg : ∀ q, memStore S.mem rStack 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) rInput q =
      S.mem rInput q := fun q => memStore_other _ _ _ _ _ _ (Or.inl (by decide))
  have m5_outm : ∀ q, memStore S.mem rStack 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) rOutput q =
      S.mem rOutput q := fun q => memStore_other _ _ _ _ _ _ (Or.inl (by decide))
  generalize memStore S.mem rStack 131053 (gprWord ⟨rInput, (mi : Int) + 64 * j + 64⟩) = M5 at hM5 m5_out m5_in m5_cnt m5_msg m5_outm
  have hρ := rho_ok j
  have hw : (rho j).within (2 ^ 54) := rho_within j (by omega)
  by_cases hm0 : mi = 0
  · -- aligned: the loads from the input node
    subst hm0
    have hbr : brHolds .eq ((0 : Nat) : Int) 0 = true := rfl
    rw [hbr, if_pos rfl] at s5
    generalize hH : RV.run rodata prog 5 S = H at s5 r5_2 r5_5 hM5
    have hok : SliceCert.Ok H := s5.ctl.ok
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
      · exact ctrl_eq _ _ s5.ctl (by decide +kernel) (s5.pc.trans (by decide +kernel))
    have sr := GenSI.seg_run (rho j) hρ hw H hc0 hok
    have fr := GenSI.seg_frame (rho j) hρ hw H hc0 hok
    have dat := GenSI.seg_data (rho j) hρ hw H hc0 hok (AN input 0 j) (in_inv0 input j _ (by
      intro w hw'
      show envOf H ((rho j).var (memVar rInput (Int.ofNat (8 * 0 + w)))) = _
      rw [rho_var_in, envOf_mem, hM5, m5_msg, hmsg, nodeWordsB_zero input j w]
      unfold nodeWords; congr 1; simp only [Int.ofNat_eq_coe]; push_cast; omega))
    rw [an_aat_si] at dat
    generalize hP : GenSI.segAt1 H = P at sr fr dat
    obtain ⟨hrun, hokP, hcutP⟩ := sr
    have hlen : GenSI.segLen = 8 := by decide +kernel
    have hrunP : RV.run rodata prog (inSteps 0) S = P := by
      rw [show inSteps 0 = 5 + 8 from rfl, Isa.run_add _ _ _ 5 8, hH, ← hlen, hrun]
    rw [hrunP]
    have hmem : ∀ r q, P.mem r q = M5 r q := by intro r q; rw [fr r q rfl, hM5]
    refine ⟨?_, hokP, ?_, (hmem _ _).trans m5_out, by rw [hmem, m5_in], (hmem _ _).trans m5_cnt,
      fun q => (hmem _ _).trans (m5_msg q), fun q => (hmem _ _).trans (m5_outm q)⟩
    · apply cut_transfer (rho j) (rho j) hρ hρ GenSI.ctl1 GenSC.ctl0 GenSI.sc1 GenSC.sc0 P P hcutP
        (hL_dec _ _ (by decide +kernel)) (fun i _ => rfl) (hval_same _ _ _ _ _ (by decide +kernel))
      obtain ⟨hC, hp⟩ := ctl0_of_cut _ _ _ _ hcutP hokP (by decide +kernel)
      exact ctrl_eq _ _ hC (by decide +kernel) (hp.trans (by decide +kernel))
    · exact dat
  · -- misaligned: through the bounce buffer
    have hbr : brHolds .eq (mi : Int) 0 = false := by simp only [brHolds, beq_eq_false_iff_ne, ne_eq]; omega
    rw [hbr, if_neg (by decide)] at s5
    -- mv t1, sp; li a7, 64
    have s6 := St.mv s5 6 2 prog_25 (by decide) (by decide) (by decide) (by decide)
    have s7 := St.li s6 17 0x40#64 prog_26 (by decide) (by decide)
    have r7_2 : (RV.run rodata prog 7 S).getGD 2 = gprWord ⟨rStack, SP⟩ := by
      rw [s7.regs 2 (by decide)]; simp only [upd]; simp; exact (s5.regs 2 (by decide)).symm.trans r5_2
    have r7_5 : (RV.run rodata prog 7 S).getGD 5 = gprWord ⟨rInput, (mi : Int) + 64 * j⟩ := by
      rw [s7.regs 5 (by decide)]; simp [upd]
    have r7_6 : (RV.run rodata prog 7 S).getGD 6 = gprWord ⟨rStack, 8 * 131044⟩ := by
      rw [s7.regs 6 (by decide)]; simp only [upd]; simp; exact (s5.regs 2 (by decide)).symm.trans r5_2
    have r7_17 : (RV.run rodata prog 7 S).getGD 17 = gprWord ⟨0, ((64 : Nat) : Int)⟩ := by
      rw [s7.regs 17 (by decide)]; simp only [upd]; simp; decide
    have hM7 : (RV.run rodata prog 7 S).mem = M5 := s7.mem.trans (s5.mem.symm.trans hM5)
    have hcp := copy_loop 2 rodata prog 27 5 6 7 17 code_in regs_in rInput rStack ((mi : Int) + 64 * j) (8 * 131044)
      (by decide) (by decide) (by decide) (by decide) (by decide) 64 (by decide) (by omega) (by decide) (by omega)
      (by decide) (by decide) _ s7.ctl s7.pc r7_5 r7_6 r7_17
    obtain ⟨hT1, hp1⟩ := hcp
    generalize hT0 : RV.run rodata prog 7 S = T0 at hT1 hp1 r7_2 hM7
    generalize hT1e : RV.run rodata prog (6 * 64) T0 = T1 at hT1 hp1
    -- mv t0, sp
    have s8 : St (RV.run rodata prog 0 T1) 33 (fun r => T1.getGD r) T1.mem := ⟨hT1.ctl, hp1, fun _ _ => rfl, rfl⟩
    have s9 := St.mv s8 5 2 prog_33 (by decide) (by decide) (by decide) (by decide)
    have hT1sp : T1.getGD 2 = gprWord ⟨rStack, SP⟩ := by
      rw [hT1.regs 2 (by decide) (by decide) (by decide) (by decide)]; exact r7_2
    generalize hH : RV.run rodata prog (0 + 1) T1 = H at s9
    have hH5 : H.getGD 5 = gprWord ⟨rStack, SP⟩ := by rw [s9.regs 5 (by decide)]; simp [upd]; exact hT1sp
    have hH2 : H.getGD 2 = gprWord ⟨rStack, SP⟩ := by rw [s9.regs 2 (by decide)]; simp [upd]; exact hT1sp
    have hok : SliceCert.Ok H := s9.ctl.ok
    -- the bounce buffer holds the node
    have hbuf : ∀ w : Nat, w < 8 → H.mem rStack (131044 + (w : Int)) = nodeWordsB input mi j w := by
      intro w hw'
      rw [s9.mem, hT1.word_copy _ (by omega) (by omega), hM7]
      unfold nodeWordsB
      have e : ∀ x y : Int, x = y → wordAt (M5 rInput) x = wordAt input y := by
        intro x y hxy; rw [hxy]; unfold wordAt; simp only [m5_msg, hmsg]
      exact e _ _ (by push_cast; omega)
    have hc0 : relocState (rho j) (cutOf GenSJ.ctl0 GenSJ.sc0) = cutOf GenSJ.ctl0 H := by
      apply relocState_cutOf (rho j) GenSJ.ctl0 GenSJ.sc0 H
      · intro i hi
        simp only [GenSJ.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl
        · rw [cutVar_ptr_of GenSJ.ctl0 H 258 ⟨rStack, SP⟩ (by decide) ((envOf_gdVar H 2 (by decide)).trans hH2) sp_wf
              (by decide), show cutVar GenSJ.ctl0 GenSJ.sc0 258 = .ptr ⟨rStack, SP⟩ by decide +kernel, reloc_ptr_stack]
        · rw [cutVar_ptr_of GenSJ.ctl0 H 261 ⟨rStack, SP⟩ (by decide) ((envOf_gdVar H 5 (by decide)).trans hH5) sp_wf
              (by decide), show cutVar GenSJ.ctl0 GenSJ.sc0 261 = .ptr ⟨rStack, SP⟩ by decide +kernel, reloc_ptr_stack]
      · intro i hi h; simp only [GenSJ.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
      · exact ctrl_eq _ _ s9.ctl (by decide +kernel) (s9.pc.trans (by decide +kernel))
    have sr := GenSJ.seg_run (rho j) hρ hw H hc0 hok
    have fr := GenSJ.seg_frame (rho j) hρ hw H hc0 hok
    have dat := GenSJ.seg_data (rho j) hρ hw H hc0 hok (AN input mi j) (buf_inv0 input mi j _ (by
      intro w hw'
      show envOf H ((rho j).var (memVar 3 (131044 + (w : Int)))) = _
      rw [rho_var_stack j (memVar 3 (131044 + (w : Int))) (memVar_ge _ _) (memVarRegion_memVar _ _), envOf_mem]
      exact hbuf w hw'))
    rw [an_aat_sj] at dat
    generalize hP : GenSJ.segAt1 H = P at sr fr dat
    obtain ⟨hrun, hokP, hcutP⟩ := sr
    have hlen : GenSJ.segLen = 8 := by decide +kernel
    have hrunP : RV.run rodata prog (inSteps mi) S = P := by
      rw [show inSteps mi = 7 + 6 * 64 + (0 + 1) + 8 by simp [inSteps, hm0], Isa.run_add _ _ _ (7 + 6 * 64 + (0 + 1)) 8,
        Isa.run_add _ _ _ (7 + 6 * 64) (0 + 1), Isa.run_add _ _ _ 7 (6 * 64), hT0, hT1e, hH, ← hlen, hrun]
    rw [hrunP]
    -- the memory outside the buffer
    have hmem : ∀ r q, (r ≠ rStack ∨ 131052 ≤ q) → P.mem r q = M5 r q := by
      intro r q hrq
      rw [fr r q rfl, s9.mem, hT1.word_other r q (by
        rcases hrq with h | h
        · exact Or.inl h
        · right; right; omega), hM7]
    refine ⟨?_, hokP, ?_, (hmem _ _ (Or.inr (by decide))).trans m5_out,
      by rw [hmem _ _ (Or.inr (by decide)), m5_in], (hmem _ _ (Or.inr (by decide))).trans m5_cnt,
      fun q => (hmem _ _ (Or.inl (by decide))).trans (m5_msg q),
      fun q => (hmem _ _ (Or.inl (by decide))).trans (m5_outm q)⟩
    · apply cut_transfer (rho j) (rho j) hρ hρ GenSJ.ctl1 GenSC.ctl0 GenSJ.sc1 GenSC.sc0 P P hcutP
        (hL_dec _ _ (by decide +kernel)) (fun i _ => rfl) (hval_same _ _ _ _ _ (by decide +kernel))
      obtain ⟨hC, hp⟩ := ctl0_of_cut _ _ _ _ hcutP hokP (by decide +kernel)
      exact ctrl_eq _ _ hC (by decide +kernel) (hp.trans (by decide +kernel))
    · exact dat

end Keccaktree.Kernels.ZbbX1.AllU

