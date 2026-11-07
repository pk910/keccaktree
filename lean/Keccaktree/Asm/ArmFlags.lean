import Keccaktree.Asm.Flags
import Keccaktree.Asm.ArmFootprint
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# AArch64: the flag-oblivious instructions

Every instruction except `subs`, `cmp` (write the flags), `csel` and `b.cond` (read them)
commutes with replacing the flags: `Arm.flagObl`.
-/
namespace Keccaktree.Asm
namespace Arm
open X86 (State)

/-- The instructions that neither read nor write the flags. -/
def flagFree : Instr → Bool
  | .subs .. | .cmp .. | .csel .. | .bcond .. => false
  | _ => true

theorem gx_withFlags (s : State (BitVec 64)) (n : Nat) (z c nn v : Bool) : gx (s.withFlags z c nn v) n = gx s n := rfl
theorem addr_withFlags (s : State (BitVec 64)) (b : Nat) (o : Int) (z c nn v : Bool) :
    addr (s.withFlags z c nn v) b o = addr s b o := rfl
theorem loadWords_withFlags (rodata : Array (BitVec 64)) (s : State (BitVec 64)) (a : Addr) (k : Nat) (z c nn v : Bool) :
    (s.withFlags z c nn v).loadWords rodata a k = s.loadWords rodata a k := rfl
theorem storeWords_withFlags (s : State (BitVec 64)) (a : Addr) (vs : List (BitVec 64)) (z c nn v : Bool) :
    (s.withFlags z c nn v).storeWords a vs = (s.storeWords a vs).map (·.withFlags z c nn v) := by
  simp only [X86.State.storeWords, X86.State.withFlags]
  split <;> rfl
theorem lane_withFlags (s : State (BitVec 64)) (n l : Nat) (z c nn v : Bool) :
    lane (s.withFlags z c nn v) n l = lane s n l := rfl
theorem regWords_withFlags (s : State (BitVec 64)) (r : LReg) (z c nn v : Bool) :
    regWords (s.withFlags z c nn v) r = regWords s r := by cases r <;> rfl

theorem exec_flags (rodata : Array (BitVec 64)) (i : Instr) (s : State (BitVec 64)) (z c nn v : Bool)
    (h : flagFree i = true) : exec rodata i (s.withFlags z c nn v) = (exec rodata i s).withFlags z c nn v := by
  cases hh : s.halted
  · have hh' : (s.withFlags z c nn v).halted = false := hh
    cases i with
    | subs => cases h
    | cmp => cases h
    | csel => cases h
    | bcond => cases h
    | add d a imm =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte, withX, gx_withFlags]
      split <;> rfl
    | sub d a imm =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte, withX, gx_withFlags]
      split <;> rfl
    | cbz a t =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte, withX, gx_withFlags]
      split
      · split <;> rfl
      · rfl
    | tbl d a b =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte, lane_withFlags]
      split <;> rfl
    | ldr r base off =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte, withAddr, addr_withFlags, loadWords_withFlags]
      split
      · split
        · cases r <;> rfl
        · rfl
      · rfl
    | ldp r1 r2 base off wb =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte, withAddr, addr_withFlags, loadWords_withFlags]
      split
      · split
        · split <;> (cases r1 <;> cases r2 <;> rfl)
        · rfl
      · rfl
    | str r base off =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte, withAddr, addr_withFlags, regWords_withFlags,
        storeWords_withFlags]
      split
      · rcases hs : s.storeWords _ _ with _ | s' <;> rfl
      · rfl
    | stp r1 r2 base off wb =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte, withAddr, addr_withFlags, regWords_withFlags,
        storeWords_withFlags]
      split
      · rcases hs : s.storeWords _ _ with _ | s'
        · rfl
        · simp only [Option.map_some]
          split <;> rfl
      · rfl
    | ldrlit r lo hi =>
      simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte]
      cases r <;> rfl
    | _ => simp only [exec, hh, hh', Bool.false_eq_true, ↓reduceIte] <;> rfl
  · have hh' : (s.withFlags z c nn v).halted = true := hh
    simp only [exec, hh, hh', ↓reduceIte]

/-- The AArch64 flag-oblivious instructions. -/
def flagObl : isa.FlagObl where
  free := flagFree
  exec_flags := fun rodata i s z c n v h => exec_flags rodata i s z c n v h

end Arm
end Keccaktree.Asm
