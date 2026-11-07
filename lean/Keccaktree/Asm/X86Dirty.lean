import Keccaktree.Asm.X86
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Mask registers and flags at a kernel's entry are irrelevant

A kernel is called (from C, or by another kernel's tail call) with arbitrary mask
registers and flags.  The generated proofs fix them (the cut's control part).  This file
shows that runs from states differing only there agree:

* `exec_setK`: an instruction that does not read the mask registers (everything but a
  masked `vmov` and `kmovw`) commutes with replacing them.
-/
namespace Keccaktree.Asm.X86
open Keccaktree.Asm

variable {α : Type} [LaneOps α]

/-- The instructions that read a mask register. -/
def Instr.readsK : Instr → Bool
  | .vmov _ _ _ (some _) => true
  | .kmovw _ _ => true
  | _ => false

/-- Replace the mask registers. -/
def setK (s : State α) (K : Vector Nat 8) : State α := { s with k := K }

@[simp] theorem setK_halted (s : State α) (K : Vector Nat 8) : (setK s K).halted = s.halted := rfl
@[simp] theorem setK_gd (s : State α) (K : Vector Nat 8) : (setK s K).gd = s.gd := rfl
@[simp] theorem setK_v (s : State α) (K : Vector Nat 8) : (setK s K).v = s.v := rfl
@[simp] theorem setK_mem (s : State α) (K : Vector Nat 8) : (setK s K).mem = s.mem := rfl
@[simp] theorem setK_pc (s : State α) (K : Vector Nat 8) : (setK s K).pc = s.pc := rfl
@[simp] theorem setK_depth (s : State α) (K : Vector Nat 8) : (setK s K).depth = s.depth := rfl
@[simp] theorem setK_zf (s : State α) (K : Vector Nat 8) : (setK s K).zf = s.zf := rfl
@[simp] theorem setK_cf (s : State α) (K : Vector Nat 8) : (setK s K).cf = s.cf := rfl

theorem condHolds_setK (s : State α) (K : Vector Nat 8) (c : Cond) : condHolds (setK s K) c = condHolds s c := rfl
theorem next_setK (s : State α) (K : Vector Nat 8) : next (setK s K) = setK (next s) K := rfl
theorem fail_setK (s : State α) (K : Vector Nat 8) : (setK s K).fail = setK s.fail K := rfl
theorem setX_setK (s : State α) (K : Vector Nat 8) (n : Nat) (a : Addr) : setX (setK s K) n a = setK (setX s n a) K := rfl
theorem setGD_setK (s : State α) (K : Vector Nat 8) (n : Nat) (x : α) : (setK s K).setGD n x = setK (s.setGD n x) K := rfl
theorem writeV_setK (s : State α) (K : Vector Nat 8) (n l : Nat) (vs : List α) :
    writeV (setK s K) n l vs = setK (writeV s n l vs) K := rfl
theorem setFlagsSub_setK (s : State α) (K : Vector Nat 8) (a b : Addr) :
    setFlagsSub (setK s K) a b = setK (setFlagsSub s a b) K := by
  unfold setFlagsSub; split <;> rfl

theorem ite_eq_ite_of {β : Type} {c : Prop} [Decidable c] {a a' b b' : β} (h1 : c → a = a') (h2 : ¬c → b = b') :
    (if c then a else b) = (if c then a' else b') := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

theorem ite_setK_eq {c : Prop} [Decidable c] {a b a' b' : State α} {K : Vector Nat 8}
    (h1 : c → a = setK a' K) (h2 : ¬c → b = setK b' K) : (if c then a else b) = setK (if c then a' else b') K := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact h1 h
  · rw [if_neg h, if_neg h]; exact h2 h

theorem setK_ite (c : Prop) [Decidable c] (a b : State α) (K : Vector Nat 8) :
    setK (if c then a else b) K = if c then setK a K else setK b K := by
  split <;> rfl

theorem withStore_setK (s : State α) (K : Vector Nat 8) (a : Addr) (vs : List α) (f : State α → State α) :
    withStore (setK s K) a vs f =
      match s.storeWords a vs with
      | some t => f (setK t K)
      | none => setK s.fail K := by
  unfold withStore State.storeWords
  by_cases h : a.off % 8 = 0 ∧ a.region ≠ rRodata
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

theorem repBody_setK (rodata : Array (BitVec 64)) (s : State α) (K : Vector Nat 8) (n a b : Addr) :
    repBody rodata (setK s K) n a b = setK (repBody rodata s n a b) K := by
  unfold repBody
  simp only [withLoad, State.loadWords, State.read, setK_mem, withStore_setK, setK_ite]
  repeat' (first | rfl | contradiction | (refine ite_eq_ite_of ?_ ?_ <;> intro _) | simp only [setK_ite, setFlagsSub_setK, setX_setK, setGD_setK, next_setK, fail_setK, writeV_setK] | split | simp only [withStore, withLoad, State.loadWords] | simp_all only [Option.some.injEq, reduceCtorEq])

macro "kt_k " s:ident : tactic => `(tactic| (
  cases hh : ($s).halted <;>
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withStore_setK, setK_ite, setK_halted, setK_gd, setK_v, setK_mem, setK_pc, setK_depth, setK_zf,
    setK_cf, withX, withMem, withSrc, withLoad, readG, binop, gx, State.getGD, State.getV, State.loadWords,
    State.read, readSrc, memAddr?, condHolds_setK, repBody_setK]
  <;> repeat' (first | rfl | contradiction | (refine ite_eq_ite_of ?_ ?_ <;> intro _) | simp only [setK_ite, setFlagsSub_setK, setX_setK, setGD_setK, next_setK, fail_setK, writeV_setK] | split | simp only [withStore, withLoad, State.loadWords] | simp_all only [Option.some.injEq, reduceCtorEq])))

theorem exec_setK (rodata : Array (BitVec 64)) (i : Instr) (s : State α) (K : Vector Nat 8)
    (hi : i.readsK = false) :
    exec rodata i (setK s K) = setK (exec rodata i s) K := by
  cases i
  case vmov l d src mask =>
    cases mask
    · kt_k s
    · simp only [Instr.readsK, Bool.true_eq_false] at hi
  case kmovw => simp only [Instr.readsK, Bool.true_eq_false] at hi
  case vpermt2q =>
    cases hh : s.halted <;> simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withSrc, readSrc, memAddr?, gx,
      State.getGD, State.getV, State.loadWords, State.read, setK_v, setK_gd, setK_mem, setK_halted]
    · split
      · exact ite_setK_eq (fun _ => rfl) (fun _ => rfl)
      · rfl
  all_goals kt_k s

end Keccaktree.Asm.X86
