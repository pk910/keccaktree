import Keccaktree.Asm.Iter
import Keccaktree.Asm.ArmReloc
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Memory footprint of the AArch64 model

Only `str` and `stp` store; every other instruction (and a failed store) keeps the
memory.  `Arm.isaFoot` is the `Isa.Footprint` instance the segment certificates use.
-/
namespace Keccaktree.Asm
namespace Arm
open Keccaktree.Asm.X86 (State State.storeWords storeWords_frame)

variable {α : Type} [LaneOps α]

/-- The cells an AArch64 instruction stores to (from the state before it). -/
def writes (s : State α) : Instr → List (Region × Int)
  | .str r base off => match addr s base off with
    | some a => storeCells a (regWords s r).length
    | none => []
  | .stp r1 r2 base off wb => match addr s base (if wb = 2 then 0 else off) with
    | some a => storeCells a (regWords s r1 ++ regWords s r2).length
    | none => []
  | _ => []

theorem withX_mem (s : State α) (n : Nat) (k : Addr → State α) (hk : ∀ a, (k a).mem = s.mem) :
    (withX s n k).mem = s.mem := by
  unfold withX; split
  · exact hk _
  · rfl

theorem withAddr_mem (s : State α) (b : Nat) (o : Int) (k : Addr → State α) (hk : ∀ a, (k a).mem = s.mem) :
    (withAddr s b o k).mem = s.mem := by
  unfold withAddr; split
  · exact hk _
  · rfl

theorem exec_frame (rodata : Array (BitVec 64)) (i : Instr) (s : State α) (hne : (exec rodata i s).err = false)
    (r : Region) (q : Int) (hw : (r, q) ∉ writes s i) : (exec rodata i s).mem r q = s.mem r q := by
  cases hh : s.halted
  · cases i with
    | str rr base off =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      unfold withAddr at hne ⊢
      rcases ha : addr s base off with _ | a
      · rfl
      · simp only [ha] at hne hw ⊢
        rcases hs : s.storeWords a (regWords s rr) with _ | s'
        · rfl
        · exact storeWords_frame s s' a _ hs r q hw
    | stp r1 r2 base off wb =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      unfold withAddr at hne ⊢
      rcases ha : addr s base (if wb = 2 then 0 else off) with _ | a
      · rfl
      · simp only [ha] at hne hw ⊢
        rcases hs : s.storeWords a (regWords s r1 ++ regWords s r2) with _ | s'
        · rfl
        · have := storeWords_frame s s' a _ hs r q hw
          try simp only
          split <;> exact this
    | ldr rr base off =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      refine congrFun (congrFun (withAddr_mem s base off _ fun a => ?_) r) q
      split
      · cases rr <;> rfl
      · rfl
    | ldp r1 r2 base off wb =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      refine congrFun (congrFun (withAddr_mem s base _ _ fun a => ?_) r) q
      split
      · split <;> (cases r1 <;> cases r2 <;> rfl)
      · rfl
    | add d a imm =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      refine congrFun (congrFun (withX_mem s a _ fun x => ?_) r) q
      first | rfl | rfl
    | sub d a imm =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      refine congrFun (congrFun (withX_mem s a _ fun x => ?_) r) q
      first | rfl | rfl
    | subs d a imm =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      refine congrFun (congrFun (withX_mem s a _ fun x => ?_) r) q
      first | rfl | (split <;> rfl)
    | cmp a imm =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      refine congrFun (congrFun (withX_mem s a _ fun x => ?_) r) q
      first | rfl | (split <;> rfl)
    | cbz a t =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      refine congrFun (congrFun (withX_mem s a _ fun x => ?_) r) q
      first | rfl | (split <;> rfl)
    | tbl d a b => simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]; split <;> rfl
    | ldrlit rr lo hi => simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]; cases rr <;> rfl
    | _ => simp only [exec, hh, Bool.false_eq_true, ↓reduceIte] <;> rfl
  · simp only [exec, hh, ↓reduceIte]

/-- The AArch64 footprint. -/
def isaFoot : isa.Footprint where
  writes := fun s i => writes s i
  exec_frame := fun rodata i s hne r q hw => exec_frame rodata i s hne r q hw

end Arm
end Keccaktree.Asm
