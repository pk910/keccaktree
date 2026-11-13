import Keccaktree.Asm.KernelGlue
import Keccaktree.Asm.ArmFootprint
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Concrete AArch64 steps on counts

The count-dependent instructions of the AArch64 kernels' frames (`cbz x2`, `subs x2, x2, #k`,
`cmp x2, #k`, `b.cond`, `ret`) on concrete states whose count register holds any number.
-/
namespace Keccaktree.Asm
open X86 (State envOf)

namespace Arm

theorem gx_of_word (S : State (BitVec 64)) (n : Nat) (a : Addr) (h : S.getGD n = gprWord a) (hwf : a.wf) :
    gx S n = some a := by
  simp only [gx, h]
  show some (wordGpr (gprWord a)) = some a
  rw [wordGpr_gprWord a hwf]

/-- One fetch-execute step of a running state. -/
theorem run_one (rodata : Array (BitVec 64)) (prog : Array Instr) (S : State (BitVec 64))
    (hh : S.halted = false) : isa.run rodata prog 1 S = exec rodata (prog.getD S.pc .nop) S := by
  show (if S.halted then S else isa.run rodata prog 0 (isa.exec rodata (prog.getD S.pc isa.nop) S)) = _
  rw [hh]; rfl

/-- `cbz xa, t` on a register holding the number `c`. -/
theorem exec_cbz_num (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (a t : Nat) (c : Int)
    (hh : S.halted = false) (h : S.getGD a = gprWord ⟨0, c⟩) (hwf : (⟨0, c⟩ : Addr).wf) :
    exec rodata (.cbz a t) S = { S with pc := if c = 0 then t else S.pc + 1 } := by
  have hg := gx_of_word S a ⟨0, c⟩ h hwf
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg]

/-- `subs xd, xa, #imm` on a register holding the number `c`. -/
theorem exec_subs_num (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d a : Nat) (imm c : Int)
    (hh : S.halted = false) (h : S.getGD a = gprWord ⟨0, c⟩) (hwf : (⟨0, c⟩ : Addr).wf) :
    exec rodata (.subs d a imm) S = next (setFlags (S.setGD d (gprWord ⟨0, c - imm⟩)) c imm) := by
  have hg := gx_of_word S a ⟨0, c⟩ h hwf
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg]
  rfl

/-- `sub xd, xa, #imm` on a register holding the number `c` (no flags). -/
theorem exec_sub_num (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d a : Nat) (imm c : Int)
    (hh : S.halted = false) (h : S.getGD a = gprWord ⟨0, c⟩) (hwf : (⟨0, c⟩ : Addr).wf) :
    exec rodata (.sub d a imm) S = next (S.setGD d (gprWord ⟨0, c - imm⟩)) := by
  have hg := gx_of_word S a ⟨0, c⟩ h hwf
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg]
  rfl

/-- `cmp xa, #imm` on a register holding the number `c`. -/
theorem exec_cmp_num (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (a : Nat) (imm c : Int)
    (hh : S.halted = false) (h : S.getGD a = gprWord ⟨0, c⟩) (hwf : (⟨0, c⟩ : Addr).wf) :
    exec rodata (.cmp a imm) S = next (setFlags S c imm) := by
  have hg := gx_of_word S a ⟨0, c⟩ h hwf
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg]

theorem exec_bcond_eq (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (c : Cond) (t : Nat) (hh : S.halted = false) :
    exec rodata (.bcond c t) S = { S with pc := if condHolds S c then t else S.pc + 1 } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

theorem exec_b_eq (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (t : Nat) (hh : S.halted = false) :
    exec rodata (.b t) S = { S with pc := t } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

theorem exec_ret_eq (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (hh : S.halted = false) :
    exec rodata .ret S = { S with halted := true } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

theorem exec_tailcall_eq (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (n : String) (hh : S.halted = false) :
    exec rodata (.tailcall n) S = { S with halted := true, tail := some n } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

theorem getGD_setGD_same (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) (hn : n < 32) :
    (S.setGD n x).getGD n = x := by
  simp [X86.State.getGD, X86.State.setGD, Vector.getD, hn]

theorem getGD_setGD_other (S : State (BitVec 64)) (n m : Nat) (x : BitVec 64) (h : m ≠ n) :
    (S.setGD n x).getGD m = S.getGD m := by
  simp [X86.State.getGD, X86.State.setGD, Vector.getD, Vector.getElem?_setIfInBounds, h.symm]

theorem envOf_setGD_other (S : State (BitVec 64)) (n i : Nat) (x : BitVec 64) (h : i ≠ 256 + n) :
    envOf (S.setGD n x) i = envOf S i := by
  unfold envOf
  by_cases h1 : i < 256
  · simp only [h1, ↓reduceIte]; rfl
  · by_cases h2 : i < 288
    · simp only [h1, h2, ↓reduceIte]
      have h3 : i - 256 ≠ n := by omega
      simp [X86.State.setGD, Vector.getD, Vector.getElem?_setIfInBounds, Ne.symm h3]
    · simp only [h1, h2, ↓reduceIte]; rfl

end Arm
end Keccaktree.Asm
