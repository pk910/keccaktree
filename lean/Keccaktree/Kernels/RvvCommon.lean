import Keccaktree.Kernels.RiscvCommon
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The frame of the RVV kernels, for every count

`rvv` and `rvv_zvkb` share their frame (only the batch body differs):

     1: beqz a2, ret                      5: or a7, a0, a1      7: mv t3, a2            13: bnez a7, bounce
     2: addi sp, sp, -512                 6: andi a7, a7, 7     8: beqz a7, 12          14: vlseg8e64 v0, (a1)
     3: li t5, 1                                                12: vsetvli t0, t3       … body …
     4: slli t5, t5, 63                                                                  s: sub a2, a2, t0
                                                                                      s+1: bnez a2, 7
                                                                                      s+2: addi sp, sp, 512
                                                                                      s+3: ret

(the misaligned path `9..11`, `16..21` is not taken: the buffers are node-aligned).  This module
proves the frame's concrete steps for every count: the entry (`entry_zero`, `entry_pos`), the
head of an iteration (`run_head`: `vl = min(r, VLMAX)` for `r` nodes left), the back edge
(`run_tail`) and the exit (`run_exit`), around the per-`vl` batch bodies of each kernel.

**Assumption (vector length choice).** The model's `vsetvli` sets `vl = min(avl, VLMAX)` (`run_head`).
RVV 1.0 also allows `⌈avl/2⌉ ≤ vl ≤ VLMAX` when `VLMAX < avl < 2·VLMAX`; that freedom is not covered here
(the bodies are proved for every `vl ∈ 1..VLMAX`; only the frame fixes the choice).
-/
namespace Keccaktree.Kernels.RvvCommon
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon
open Keccaktree.Asm.Riscv (setR getR brHolds run_one exec_br_num exec_j_eq exec_ret_eq getR_zero getR_pos
  envOf_setR_other setR_getGD_same setR_getGD_other setR_mem' setR_pc setR_halted setR_err setR_tail setR_k
  setR_flags setR_g next_getGD next_halted next_err next_tail next_pc next_mem next_g next_k next_zf next_cf next_nf next_vf
  next_vl next_depth setR_zf setR_cf setR_nf setR_vf setR_vl setR_depth exec_mv_eq exec_op_eq exec_li_eq exec_opi_eq exec_vsetvli_num gprWord_sub_nat align_zero)

/-- The state at the loop head (`p = 7`) or at the exit (`p = s + 2`) after `j` of the `c` nodes:
the control part (general registers as data words, no flags), the pointers at node `off + j`, the
count register `c - j`, the alignment flag `a7 = 0`, `t5 = 1 << 63`, the message, the earlier
output words and the digests of the nodes done. -/
structure Mid (off c : Nat) (input : Int → BitVec 64) (S0 S : State (BitVec 64)) (j p : Nat) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.pc = p ∧ S.depth = 0
  ok : SliceCert.Ok S
  a0 : S.getGD 10 = gprWord ⟨rOutput, 32 * ((off + j : Nat) : Int)⟩
  a1 : S.getGD 11 = gprWord ⟨rInput, 64 * ((off + j : Nat) : Int)⟩
  a2 : S.getGD 12 = gprWord ⟨0, (c : Int) - (j : Int)⟩
  a7 : S.getGD 17 = 0#64
  t5 : S.getGD 30 = 0x8000000000000000#64
  inp : ∀ q, S.mem rInput q = input q
  pre : ∀ q : Int, q < 4 * (off : Int) → S.mem rOutput q = S0.mem rOutput q
  dig : ∀ n, n < j → Digest input S (off + n)

/-! ## The head of an iteration -/

/-- The state after `mv t3, a2; beqz a7, 12; vsetvli t0, t3; bnez a7, 16` with `r` nodes left. -/
def H4 (V : Nat) (S : State (BitVec 64)) (r : Int) : State (BitVec 64) :=
  { Riscv.next { setR { Riscv.next (setR S 28 (gprWord ⟨0, r⟩)) with pc := 12 } 5 (BitVec.ofNat 64 (min r.toNat V))
      with vl := min r.toNat V } with pc := 14 }

theorem zero_word : (0#64 : BitVec 64) = gprWord ⟨0, 0⟩ := rfl

theorem run_head (V : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr)
    (hp7 : prog.getD 7 .nop = .mv 28 12) (hp8 : prog.getD 8 .nop = .br .eq 17 0 12)
    (hp12 : prog.getD 12 .nop = .vsetvli 5 28) (hp13 : prog.getD 13 .nop = .br .ne 17 0 16)
    (S : State (BitVec 64)) (r : Int) (hh : S.halted = false) (hpc : S.pc = 7)
    (h12 : S.getGD 12 = gprWord ⟨0, r⟩) (h17 : S.getGD 17 = 0#64) (h0 : 0 ≤ r) (h1 : r < 2 ^ 55) :
    (Riscv.isa V).run rodata prog 4 S = H4 V S r := by
  have e1 : (Riscv.isa V).run rodata prog 1 S = Riscv.next (setR S 28 (gprWord ⟨0, r⟩)) := by
    rw [run_one V rodata prog S hh, hpc, hp7, exec_mv_eq V rodata S 28 12 hh, getR_pos S 12 (by decide), h12]
  generalize hX1 : Riscv.next (setR S 28 (gprWord ⟨0, r⟩)) = X1 at e1
  have hh1 : X1.halted = false := by rw [← hX1]; simp only [Riscv.next, setR_halted, hh]
  have hpc1 : X1.pc = 8 := by rw [← hX1]; simp only [Riscv.next, setR_pc, hpc]
  have h17' : getR X1 17 = gprWord ⟨0, 0⟩ := by
    rw [getR_pos X1 17 (by decide), ← hX1]
    show (setR S 28 _).getGD 17 = _
    rw [setR_getGD_other S 28 17 (by decide), h17]; rfl
  have e2 : (Riscv.isa V).run rodata prog 1 X1 = { X1 with pc := 12 } := by
    rw [run_one V rodata prog X1 hh1, hpc1, hp8, exec_br_num V rodata X1 .eq 17 0 12 0 0 hh1 h17' (getR_zero X1) (by decide) (by decide)]
    rfl
  generalize hX2 : ({ X1 with pc := 12 } : State (BitVec 64)) = X2 at e2
  have hh2 : X2.halted = false := by rw [← hX2]; exact hh1
  have hpc2 : X2.pc = 12 := by rw [← hX2]
  have h28 : getR X2 28 = gprWord ⟨0, r⟩ := by
    rw [getR_pos _ 28 (by decide), ← hX2, ← hX1]
    exact setR_getGD_same S 28 (by decide) (by decide) (gprWord ⟨0, r⟩)
  have e3 : (Riscv.isa V).run rodata prog 1 X2 =
      Riscv.next { setR X2 5 (BitVec.ofNat 64 (min r.toNat V)) with vl := min r.toNat V } := by
    rw [run_one V rodata prog _ hh2, hpc2, hp12, exec_vsetvli_num V rodata _ 5 28 r hh2 h28 h0 h1]
  generalize hX3 : Riscv.next { setR X2 5 (BitVec.ofNat 64 (min r.toNat V)) with vl := min r.toNat V } = X3 at e3
  have hh3 : X3.halted = false := by
    rw [← hX3]; show (setR X2 5 (BitVec.ofNat 64 (min r.toNat V))).halted = false; rw [setR_halted]; exact hh2
  have hpc3 : X3.pc = 13 := by
    rw [← hX3]; show (setR X2 5 (BitVec.ofNat 64 (min r.toNat V))).pc + 1 = 13; rw [setR_pc, hpc2]
  have h17'' : getR X3 17 = gprWord ⟨0, 0⟩ := by
    rw [getR_pos X3 17 (by decide), ← hX3]
    show (setR X2 5 _).getGD 17 = _
    rw [setR_getGD_other _ 5 17 (by decide), ← hX2]
    rw [getR_pos X1 17 (by decide)] at h17'; exact h17'
  have e4 : (Riscv.isa V).run rodata prog 1 X3 = { X3 with pc := 14 } := by
    rw [run_one V rodata prog X3 hh3, hpc3, hp13, exec_br_num V rodata X3 .ne 17 0 16 0 0 hh3 h17'' (getR_zero X3) (by decide) (by decide)]
    simp only [brHolds, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hpc3]
  rw [show 4 = 1 + 1 + 1 + 1 from rfl, Isa.run_add, Isa.run_add, Isa.run_add, e1, e2, e3, e4, ← hX3, ← hX2, ← hX1]
  rfl

theorem H4_facts (V : Nat) (S : State (BitVec 64)) (r : Int) :
    (H4 V S r).pc = 14 ∧ (H4 V S r).vl = min r.toNat V ∧
    (H4 V S r).getGD 5 = BitVec.ofNat 64 (min r.toNat V) ∧
    (H4 V S r).g = (S.g.setIfInBounds 28 ⟨0, 0⟩).setIfInBounds 5 ⟨0, 0⟩ ∧ (H4 V S r).k = S.k ∧
    (H4 V S r).zf = S.zf ∧ (H4 V S r).cf = S.cf ∧ (H4 V S r).nf = S.nf ∧ (H4 V S r).vf = S.vf ∧
    (H4 V S r).depth = S.depth ∧ (H4 V S r).halted = S.halted ∧ (H4 V S r).err = S.err ∧
    (H4 V S r).tail = S.tail ∧ (H4 V S r).mem = S.mem := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact setR_getGD_same _ 5 (by decide) (by decide) _
  all_goals simp only [H4, Riscv.next, setR_g _ 5 (by decide : (5 : Nat) ≠ 0), setR_g _ 28 (by decide : (28 : Nat) ≠ 0),
    setR_k, setR_halted, setR_err, setR_tail, setR_mem', setR_zf, setR_cf, setR_nf, setR_vf, setR_depth]

theorem H4_env (V : Nat) (S : State (BitVec 64)) (r : Int) (i : Nat) (h5 : i ≠ 261) (h28 : i ≠ 284) :
    envOf (H4 V S r) i = envOf S i := by
  show envOf (setR { Riscv.next (setR S 28 (gprWord ⟨0, r⟩)) with pc := 12 } 5 _) i = _
  rw [envOf_setR_other _ 5 (by decide) _ i h5]
  show envOf (setR S 28 _) i = _
  rw [envOf_setR_other _ 28 (by decide) _ i h28]

/-! ## The back edge -/

/-- The state after `sub a2, a2, t0; bnez a2, 7` from `Sb` (`r` nodes left, `vl = w`). -/
def T2 (Sb : State (BitVec 64)) (r : Int) (w : Nat) : State (BitVec 64) :=
  { Riscv.next (setR Sb 12 (gprWord ⟨0, r - (w : Int)⟩)) with
    pc := if brHolds .ne (r - (w : Int)) 0 then 7 else Sb.pc + 1 + 1 }

theorem run_tail (V : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (s : Nat)
    (hps : prog.getD s .nop = .op 12 12 5 .sub) (hpb : prog.getD (s + 1) .nop = .br .ne 12 0 7)
    (Sb : State (BitVec 64)) (r : Int) (w : Nat) (hh : Sb.halted = false) (hpc : Sb.pc = s)
    (h12 : Sb.getGD 12 = gprWord ⟨0, r⟩) (h5 : Sb.getGD 5 = BitVec.ofNat 64 w)
    (h0 : 0 ≤ r - (w : Int)) (h1 : r - (w : Int) < 2 ^ 55) :
    (Riscv.isa V).run rodata prog 2 Sb = T2 Sb r w := by
  have e1 : (Riscv.isa V).run rodata prog 1 Sb = Riscv.next (setR Sb 12 (gprWord ⟨0, r - (w : Int)⟩)) := by
    rw [run_one V rodata prog Sb hh, hpc, hps, exec_op_eq V rodata Sb 12 12 5 .sub hh, getR_pos Sb 12 (by decide),
      getR_pos Sb 5 (by decide), h12, h5]
    show Riscv.next (setR Sb 12 (gprWord ⟨0, r⟩ + (~~~(BitVec.ofNat 64 w) + 1#64))) = _
    rw [gprWord_sub_nat]
  generalize hX : Riscv.next (setR Sb 12 (gprWord ⟨0, r - (w : Int)⟩)) = X at e1
  have hhX : X.halted = false := by rw [← hX]; simp only [Riscv.next, setR_halted, hh]
  have hpcX : X.pc = s + 1 := by rw [← hX]; simp only [Riscv.next, setR_pc, hpc]
  have h12X : getR X 12 = gprWord ⟨0, r - (w : Int)⟩ := by
    rw [getR_pos X 12 (by decide), ← hX]; exact setR_getGD_same Sb 12 (by decide) (by decide) _
  have e2 : (Riscv.isa V).run rodata prog 1 X = { X with pc := if brHolds .ne (r - (w : Int)) 0 then 7 else s + 1 + 1 } := by
    rw [run_one V rodata prog X hhX, hpcX, hpb, exec_br_num V rodata X .ne 12 0 7 (r - (w : Int)) 0 hhX h12X (getR_zero X)
      ⟨h0, h1⟩ (by decide), hpcX]
  rw [show 2 = 1 + 1 from rfl, Isa.run_add, e1, e2, ← hX, ← hpc]
  rfl

theorem T2_facts (Sb : State (BitVec 64)) (r : Int) (w : Nat) :
    (T2 Sb r w).getGD 12 = gprWord ⟨0, r - (w : Int)⟩ ∧
    (T2 Sb r w).g = Sb.g.setIfInBounds 12 ⟨0, 0⟩ ∧ (T2 Sb r w).k = Sb.k ∧
    (T2 Sb r w).zf = Sb.zf ∧ (T2 Sb r w).cf = Sb.cf ∧ (T2 Sb r w).nf = Sb.nf ∧ (T2 Sb r w).vf = Sb.vf ∧
    (T2 Sb r w).depth = Sb.depth ∧ (T2 Sb r w).halted = Sb.halted ∧ (T2 Sb r w).err = Sb.err ∧
    (T2 Sb r w).tail = Sb.tail ∧ (T2 Sb r w).mem = Sb.mem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact setR_getGD_same _ 12 (by decide) (by decide) _
  all_goals simp only [T2, Riscv.next, setR_g _ 12 (by decide : (12 : Nat) ≠ 0),
    setR_k, setR_halted, setR_err, setR_tail, setR_mem', setR_zf, setR_cf, setR_nf, setR_vf, setR_depth]

theorem T2_getGD (Sb : State (BitVec 64)) (r : Int) (w : Nat) (n : Nat) (hn : n ≠ 12) :
    (T2 Sb r w).getGD n = Sb.getGD n := by
  show (setR Sb 12 _).getGD n = _
  exact setR_getGD_other Sb 12 n hn _

theorem T2_pc (Sb : State (BitVec 64)) (r : Int) (w : Nat) (s : Nat) (hpc : Sb.pc = s) :
    (T2 Sb r w).pc = if r - (w : Int) = 0 then s + 2 else 7 := by
  show (if brHolds .ne (r - (w : Int)) 0 then 7 else Sb.pc + 1 + 1) = _
  rw [hpc]
  by_cases h : r - (w : Int) = 0 <;> simp [brHolds, h]

/-! ## Entry and exit -/

/-- The exit: `addi sp, sp, 512; ret` halts with the memory unchanged. -/
theorem run_exit (V : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (s : Nat)
    (hp2 : prog.getD (s + 2) .nop = .opi 2 2 .addi 0x200#64) (hp3 : prog.getD (s + 3) .nop = .ret)
    (U : State (BitVec 64)) (hh : U.halted = false) (hpc : U.pc = s + 2) :
    (Riscv.isa V).run rodata prog 2 U = { Riscv.next (setR U 2 (getR U 2 + 0x200#64)) with halted := true } := by
  have e1 : (Riscv.isa V).run rodata prog 1 U = Riscv.next (setR U 2 (getR U 2 + 0x200#64)) := by
    rw [run_one V rodata prog U hh, hpc, hp2, exec_opi_eq V rodata U 2 2 .addi _ hh]; rfl
  have hh1 : (Riscv.next (setR U 2 (getR U 2 + 0x200#64))).halted = false := by
    simp only [Riscv.next, setR_halted, hh]
  rw [show 2 = 1 + 1 from rfl, Isa.run_add, e1, run_one V rodata prog _ hh1,
    show (Riscv.next (setR U 2 (getR U 2 + 0x200#64))).pc = s + 3 by simp only [Riscv.next, setR_pc, hpc], hp3,
    exec_ret_eq V rodata _ hh1]

/-- The entry state of an RVV kernel call at node offset `off` (see `RiscvCommon`): the control
part of a fresh call at instruction 1, `a2 = count`, `a1`/`a0` at node `off` of the input/output
regions (8-byte aligned), the message in the input region; everything else arbitrary. -/
structure Entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.pc = 1 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  a2 : S.getGD 12 = gprWord ⟨0, count⟩
  a1 : S.getGD 11 = gprWord ⟨rInput, 64 * off⟩
  a0 : S.getGD 10 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

/-- No node: `beqz a2, ret; ret`. -/
theorem entry_zero (V : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (s : Nat)
    (hp1 : prog.getD 1 .nop = .br .eq 12 0 (s + 3)) (hp3 : prog.getD (s + 3) .nop = .ret)
    (off : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (hE : Entry off 0 input S) :
    (Riscv.isa V).run rodata prog 2 S = { S with pc := s + 3, halted := true } := by
  have hh := hE.ok.2.1
  have e1 : (Riscv.isa V).run rodata prog 1 S = { S with pc := s + 3 } := by
    rw [run_one V rodata prog S hh, hE.ctrl.2.2.2.2.2.2.1, hp1,
      exec_br_num V rodata S .eq 12 0 (s + 3) 0 0 hh ((getR_pos S 12 (by decide)).trans hE.a2) (getR_zero S) (by decide) (by decide)]
    rfl
  generalize hT : ({ S with pc := s + 3 } : State (BitVec 64)) = T at e1
  have hhT : T.halted = false := by rw [← hT]; exact hh
  have hpcT : T.pc = s + 3 := by rw [← hT]
  rw [show 2 = 1 + 1 from rfl, Isa.run_add, e1, run_one V rodata prog T hhT, hpcT, hp3, exec_ret_eq V rodata T hhT, ← hT]

/-- The frame set-up (`c ≥ 1`): six steps to the loop head with nothing done. -/
theorem entry_pos (V : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (s : Nat)
    (hp1 : prog.getD 1 .nop = .br .eq 12 0 (s + 3)) (hp2 : prog.getD 2 .nop = .opi 2 2 .addi 0xfffffffffffffe00#64)
    (hp3 : prog.getD 3 .nop = .li 30 0x1#64) (hp4 : prog.getD 4 .nop = .opi 30 30 .slli 0x3f#64)
    (hp5 : prog.getD 5 .nop = .op 17 10 11 .or) (hp6 : prog.getD 6 .nop = .opi 17 17 .andi 0x7#64)
    (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (hE : Entry off c input S) (hc : 0 < c)
    (hb : 64 * (off + c) ≤ 2 ^ 54) :
    Mid off c input S ((Riscv.isa V).run rodata prog 6 S) 0 7 := by
  have hh := hE.ok.2.1
  have hcwf : (⟨0, (c : Int)⟩ : Addr).wf := by
    show 0 ≤ (c : Int) ∧ (c : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    constructor <;> omega
  -- the six states
  generalize hS1 : ({ S with pc := 2 } : State (BitVec 64)) = S1
  have e1 : (Riscv.isa V).run rodata prog 1 S = S1 := by
    rw [run_one V rodata prog S hh, hE.ctrl.2.2.2.2.2.2.1, hp1,
      exec_br_num V rodata S .eq 12 0 (s + 3) c 0 hh ((getR_pos S 12 (by decide)).trans hE.a2) (getR_zero S) hcwf (by decide),
      ← hS1]
    simp only [brHolds, hE.ctrl.2.2.2.2.2.2.1]
    have : ((c : Int) == 0) = false := by simp; omega
    rw [this]; rfl
  have hh1 : S1.halted = false := by subst hS1; exact hh
  generalize hS2 : Riscv.next (setR S1 2 (getR S1 2 + 0xfffffffffffffe00#64)) = S2
  have e2 : (Riscv.isa V).run rodata prog 1 S1 = S2 := by
    rw [run_one V rodata prog S1 hh1, show S1.pc = 2 by rw [← hS1], hp2, exec_opi_eq V rodata S1 2 2 .addi _ hh1, ← hS2]; rfl
  have hh2 : S2.halted = false := by subst hS2; simp only [Riscv.next, setR_halted, hh1]
  have hpc2 : S2.pc = 3 := by subst hS2 hS1; simp only [Riscv.next, setR_pc]
  generalize hS3 : Riscv.next (setR S2 30 0x1#64) = S3
  have e3 : (Riscv.isa V).run rodata prog 1 S2 = S3 := by
    rw [run_one V rodata prog S2 hh2, hpc2, hp3, exec_li_eq V rodata S2 30 _ hh2, ← hS3]
  have hh3 : S3.halted = false := by subst hS3; simp only [Riscv.next, setR_halted, hh2]
  have hpc3 : S3.pc = 4 := by subst hS3; simp only [Riscv.next, setR_pc, hpc2]
  generalize hS4 : Riscv.next (setR S3 30 0x8000000000000000#64) = S4
  have e4 : (Riscv.isa V).run rodata prog 1 S3 = S4 := by
    have h30 : S3.getGD 30 = 0x1#64 := by subst hS3; rw [next_getGD, setR_getGD_same S2 30 (by decide) (by decide) (0x1#64)]
    have hv : (Riscv.opi .slli (0x1#64 : BitVec 64) 0x3f#64 : BitVec 64) = 0x8000000000000000#64 := by decide +kernel
    rw [run_one V rodata prog S3 hh3, hpc3, hp4, exec_opi_eq V rodata S3 30 30 .slli _ hh3, getR_pos S3 30 (by decide), h30, hv, ← hS4]
  have hh4 : S4.halted = false := by subst hS4; simp only [Riscv.next, setR_halted, hh3]
  have hpc4 : S4.pc = 5 := by subst hS4; simp only [Riscv.next, setR_pc, hpc3]
  -- a0, a1 survive the first four steps
  have g4 : ∀ n, n ≠ 2 → n ≠ 30 → S4.getGD n = S.getGD n := by
    intro n h2 h30
    subst hS4 hS3 hS2 hS1
    rw [next_getGD, setR_getGD_other _ 30 n h30, next_getGD, setR_getGD_other _ 30 n h30, next_getGD,
      setR_getGD_other _ 2 n h2]
    rfl
  generalize hS5 : Riscv.next (setR S4 17 (gprWord ⟨rOutput, 32 * (off : Int)⟩ ||| gprWord ⟨rInput, 64 * (off : Int)⟩)) = S5
  have e5 : (Riscv.isa V).run rodata prog 1 S4 = S5 := by
    rw [run_one V rodata prog S4 hh4, hpc4, hp5, exec_op_eq V rodata S4 17 10 11 .or hh4, ← hS5,
      getR_pos S4 10 (by decide), getR_pos S4 11 (by decide), g4 10 (by decide) (by decide), g4 11 (by decide) (by decide),
      hE.a0, hE.a1]
    rfl
  have hh5 : S5.halted = false := by subst hS5; simp only [Riscv.next, setR_halted, hh4]
  have hpc5 : S5.pc = 6 := by subst hS5; simp only [Riscv.next, setR_pc, hpc4]
  generalize hS6 : Riscv.next (setR S5 17 0#64) = S6
  have e6 : (Riscv.isa V).run rodata prog 1 S5 = S6 := by
    rw [run_one V rodata prog S5 hh5, hpc5, hp6, exec_opi_eq V rodata S5 17 17 .andi _ hh5, ← hS6, getR_pos S5 17 (by decide)]
    have : S5.getGD 17 = gprWord ⟨rOutput, 32 * (off : Int)⟩ ||| gprWord ⟨rInput, 64 * (off : Int)⟩ := by
      subst hS5; rw [next_getGD, setR_getGD_same S4 17 (by decide) (by decide)]
    have hv : (Riscv.opi .andi (gprWord ⟨rOutput, 32 * (off : Int)⟩ ||| gprWord ⟨rInput, 64 * (off : Int)⟩) 0x7#64 : BitVec 64) = 0#64 :=
      align_zero off off
    rw [this, hv]
  have hrun : (Riscv.isa V).run rodata prog 6 S = S6 := by
    rw [show 6 = 1 + 1 + 1 + 1 + 1 + 1 from rfl, Isa.run_add, Isa.run_add, Isa.run_add, Isa.run_add, Isa.run_add,
      e1, e2, e3, e4, e5, e6]
  rw [hrun]
  have g6 : ∀ n, n ≠ 2 → n ≠ 30 → n ≠ 17 → S6.getGD n = S.getGD n := by
    intro n h2 h30 h17
    have := g4 n h2 h30
    subst hS6 hS5
    rw [next_getGD, setR_getGD_other _ 17 n h17, next_getGD, setR_getGD_other _ 17 n h17]
    exact this
  have hmem : S6.mem = S.mem := by
    subst hS6 hS5 hS4 hS3 hS2 hS1; simp only [Riscv.next, setR_mem']
  obtain ⟨cg, ck, cz, cc, cn, cv, cpc, cd⟩ := hE.ctrl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun q => by rw [hmem]; exact hE.inp q,
    fun q _ => by rw [hmem], fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  · subst hS6 hS5 hS4 hS3 hS2 hS1
    simp only [next_g, setR_g _ 17 (by decide : (17 : Nat) ≠ 0), setR_g _ 30 (by decide : (30 : Nat) ≠ 0),
      setR_g _ 2 (by decide : (2 : Nat) ≠ 0)]
    show ((((S.g.setIfInBounds 2 ⟨0, 0⟩).setIfInBounds 30 ⟨0, 0⟩).setIfInBounds 30 ⟨0, 0⟩).setIfInBounds 17 ⟨0, 0⟩).setIfInBounds 17 ⟨0, 0⟩ = _
    rw [cg]
    decide +kernel
  all_goals first
    | (subst hS6 hS5 hS4 hS3 hS2 hS1
       simp only [next_k, next_halted, next_err, next_tail, next_pc, next_zf, next_cf, next_nf, next_vf, next_depth,
         setR_k, setR_halted, setR_err, setR_tail, setR_pc, setR_zf, setR_cf, setR_nf, setR_vf, setR_depth,
         ck, cz, cc, cn, cv, cd, hE.ok.1, hE.ok.2.2, hh]; done)
    | skip
  · rw [g6 10 (by decide) (by decide) (by decide), hE.a0]; simp
  · rw [g6 11 (by decide) (by decide) (by decide), hE.a1]; simp
  · rw [g6 12 (by decide) (by decide) (by decide), hE.a2]; simp
  · subst hS6; rw [next_getGD, setR_getGD_same S5 17 (by decide) (by decide)]
  · subst hS6 hS5 hS4
    rw [next_getGD, setR_getGD_other _ 17 30 (by decide), next_getGD, setR_getGD_other _ 17 30 (by decide), next_getGD,
      setR_getGD_same S3 30 (by decide) (by decide)]

end Keccaktree.Kernels.RvvCommon
