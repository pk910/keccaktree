import Keccaktree.Asm.RiscvReloc
import Keccaktree.Asm.Iter
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# RISC-V memory footprint

The cells a RISC-V step stores to (`sd`: one word, `vsseg`: `nf·vl` words, `sb`: the byte's word,
`vse8`: the `vl/8` words, or the `vl/8 + 1` words they straddle), with the
frame property (`exec_frame`): a non-failing step keeps every other cell.  The
footprint `Riscv.isaFoot vlmax` of the instruction set `Riscv.isa vlmax`.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next
open Keccaktree.Asm.Arm (gx setX withX addr withAddr)
open LaneOps

variable {α : Type} [LaneOps α]

/-- The cells a RISC-V instruction stores to (from the state before it). -/
def writes (s : State α) : Instr → List (Region × Int)
  | .sd _ base off => match addr s base off with
    | some a => storeCells a 1
    | none => []
  | .vsseg _ base nf => match addr s base 0 with
    | some a => storeCells a (nf * s.vl)
    | none => []
  | .sb _ base off => match addr s base off with
    | some a => storeCells (wordOf a) 1
    | none => []
  | .vse8 _ base => match addr s base 0 with
    | some a => if byteOf a = 0 then storeCells a (s.vl / 8) else storeCells (wordOf a) (s.vl / 8 + 1)
    | none => []
  | _ => []

@[simp] theorem next_mem' (s : State α) : (next s).mem = s.mem := rfl
@[simp] theorem setR_mem (s : State α) (n : Nat) (x : α) : (setR s n x).mem = s.mem := by
  unfold setR; split <;> rfl
@[simp] theorem setActive_mem (s : State α) (d : Nat) (f : Nat → α) : (setActive s d f).mem = s.mem := rfl

theorem foldl_setActive_mem (l : List Nat) (g : Nat → Nat → α) (nf d : Nat) (s : State α) :
    (l.foldl (fun s' f => setActive s' (d + f) (g f)) s).mem = s.mem := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; rw [ih]; rfl

@[simp] theorem setLanes_mem (s : State α) (d c : Nat) (f : Nat → α) : (setLanes s d c f).mem = s.mem := rfl

theorem setGroup_mem (vlmax : Nat) (s : State α) (d : Nat) (ws : List α) (n : Nat) :
    (setGroup vlmax s d ws n).mem = s.mem := by
  unfold setGroup
  generalize List.range ((n + vlmax - 1) / vlmax) = l
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; rw [ih]; rfl

theorem storeBytes_frame (rodata : Array (BitVec 64)) (s s' : State α) (a : Addr) (vs : List α) (n : Nat)
    (h : storeBytes rodata s a vs n = some s') (hn : vs.length = n) (r : Region) (q : Int)
    (hw : (r, q) ∉ (if byteOf a = 0 then storeCells a n else storeCells (wordOf a) (n + 1))) : s'.mem r q = s.mem r q := by
  unfold storeBytes at h
  split at h
  · rename_i hk
    simp only [hk, ↓reduceIte] at hw
    exact X86.storeWords_frame s s' a vs h r q (by rw [hn]; exact hw)
  · rename_i hk
    simp only [hk, ↓reduceIte] at hw
    split at h
    · exact X86.storeWords_frame s s' _ _ h r q (by simp only [splitWords, List.length_map, List.length_range]; exact hw)
    · cases h

set_option maxHeartbeats 4000000 in
/-- **The footprint of a RISC-V step**: a non-failing step changes memory only in the cells it
stores to. -/
theorem exec_frame (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (s : State α)
    (hne : (exec vlmax rodata i s).err = false)
    (r : Region) (q : Int) (hw : (r, q) ∉ writes s i) : (exec vlmax rodata i s).mem r q = s.mem r q := by
  cases hh : s.halted
  · cases i with
    | sd src base off =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes, withAddr] at hne hw ⊢
      rcases ha : addr s base off with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        rcases hs : s.storeWords a [getR s src] with _ | s'
        · simp only [hs] at hne ⊢; rfl
        · simp only [hs, next_mem']
          exact X86.storeWords_frame s s' a _ hs r q hw
    | vsseg src base nf =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes, withAddr] at hne hw ⊢
      rcases ha : addr s base 0 with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        rcases hs : s.storeWords a ((List.range (nf * s.vl)).map fun q => lane s (src + q % nf) (q / nf)) with _ | s'
        · simp only [hs] at hne ⊢; rfl
        · simp only [hs, next_mem']
          exact X86.storeWords_frame s s' a _ hs r q (by simpa using hw)
    | vlseg d base nf =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr]
      rcases ha : addr s base 0 with _ | a
      · rfl
      · simp only
        rcases hl : s.loadWords rodata a (nf * s.vl) with _ | ws
        · rfl
        · simp only [next_mem']
          rw [foldl_setActive_mem _ _ nf d s]
    | sb src base off =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes, withAddr] at hne hw ⊢
      rcases ha : addr s base off with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        rcases hl : s.loadWords rodata (wordOf a) 1 with _ | l
        · simp only [hl]; rfl
        · rcases l with _ | ⟨w, _ | ⟨w2, l⟩⟩
          · simp only [hl]; rfl
          · simp only [hl]
            rcases hs : s.storeWords (wordOf a) [insByte w (getR s src) (byteOf a)] with _ | s'
            · simp only [hs]; rfl
            · simp only [hs, next_mem']
              exact X86.storeWords_frame s s' _ _ hs r q hw
          · simp only [hl]; rfl
    | vse8 src base =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes, withAddr] at hne hw ⊢
      rcases ha : addr s base 0 with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        split
        · split
          · rfl
          · rcases hs : storeBytes rodata s a ((List.range (s.vl / 8)).map fun j => groupWord vlmax s src j) (s.vl / 8)
              with _ | s'
            · simp only [hs]; rfl
            · simp only [hs, next_mem']
              exact storeBytes_frame rodata s s' a _ _ hs (by simp) r q hw
        · rfl
    | lbu d base off =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr]
      rcases ha : addr s base off with _ | a
      · rfl
      · simp only
        split <;> simp
    | vle8 d base =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr]
      rcases ha : addr s base 0 with _ | a
      · rfl
      · simp only
        split
        · split
          · simp only [next_mem']; exact congrFun (congrFun (setGroup_mem vlmax s d _ _) r) q
          · rfl
        · rfl
    | vsetvlie8 d a lmul =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      split
      · split
        · simp only [next_mem']; show (setR s d _).mem r q = _; rw [setR_mem]
        · rfl
      · rfl
    | ld d base off =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr]
      rcases ha : addr s base off with _ | a
      · rfl
      · simp only
        split <;> simp
    | lea d a =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      split <;> rfl
    | br c a b t =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      split
      · split <;> rfl
      · rfl
    | vsetvli d a =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [next_mem']; show (setR s d _).mem r q = _; rw [setR_mem]
      · rfl
    | vshiftx d a k x =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
      split <;> rfl
    | op => simp [exec, hh]
    | opi => simp [exec, hh]
    | li => simp [exec, hh]
    | mv => simp [exec, hh]
    | not => simp [exec, hh]
    | j => simp [exec, hh]
    | ret => simp [exec, hh]
    | nop => simp [exec, hh]
    | unsupported => simp [exec, hh, State.fail]
    | vop => simp [exec, hh]
    | vnot => simp [exec, hh]
    | vshifti => simp [exec, hh]
    | vxorx => simp [exec, hh]
    | vmvi => simp [exec, hh]
    | vmvx => simp [exec, hh]
    | vmvv => simp [exec, hh]
  · simp only [exec, hh, ↓reduceIte]

/-- The RISC-V footprint. -/
def isaFoot (vlmax : Nat) : (isa vlmax).Footprint where
  writes := fun s i => writes s i
  exec_frame := fun rodata i s hne r q hw => exec_frame vlmax rodata i s hne r q hw

end Keccaktree.Asm.Riscv
