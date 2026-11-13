import Keccaktree.Asm.AliasGen
import Keccaktree.Asm.ArmFootprint
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# AArch64 footprints and memory locality (in-place hashing)

`Arm.reads`: the cells an AArch64 step loads (`Arm.writes`, the cells it stores to: `ArmFootprint.lean`) (`str`/`stp`, `ldr`/`ldp`;
the literal loads read no memory); `exec_frame` and `exec_local` as for x86 (`Alias.lean`).
-/
namespace Keccaktree.Asm.Arm
open Keccaktree.Asm
open Keccaktree.Asm.X86 (State rebase Agree rebase_nil)
open LaneOps

variable {α : Type} [LaneOps α]

def reads (s : State α) : Instr → List (Region × Int)
  | .ldr r base off => match addr s base off with
    | some a => storeCells a (regSize r / 8).toNat
    | none => []
  | .ldp r1 r2 base off wb => match addr s base (if wb = 2 then 0 else off) with
    | some a => storeCells a ((regSize r1 + regSize r2) / 8).toNat
    | none => []
  | _ => []

theorem addr_wm (s : State α) (m' : Region → Int → α) (b : Nat) (o : Int) :
    addr ({ s with mem := m' } : State α) b o = addr s b o := rfl
theorem regWords_wm (s : State α) (m' : Region → Int → α) (r : LReg) :
    regWords ({ s with mem := m' } : State α) r = regWords s r := rfl
@[simp] theorem lane_wm (s : State α) (m' : Region → Int → α) (n l : Nat) :
    lane ({ s with mem := m' } : State α) n l = lane s n l := rfl
@[simp] theorem condHolds_wm' (s : State α) (m' : Region → Int → α) (c : Cond) :
    condHolds ({ s with mem := m' } : State α) c = condHolds s c := rfl

@[simp] theorem gx_wm' (s : State α) (m' : Region → Int → α) (n : Nat) :
    gx ({ s with mem := m' } : State α) n = gx s n := rfl

syntax "wm_close'" : tactic
macro_rules
  | `(tactic| wm_close') => `(tactic| first
    | rfl
    | (split <;> rename_i h <;> (try simp only [h, ↓reduceIte]) <;> wm_close')
    | (simp only [lane_wm, condHolds_wm', X86.getGD_wm, X86.getV_wm, gx_wm', withX, setFlags] <;> wm_close'))

set_option maxHeartbeats 8000000 in
/-- **Memory locality of an AArch64 step** (as `X86.exec_local`). -/
theorem exec_local (rodata : Array (BitVec 64)) (m' : Region → Int → α) (i : Instr) (s : State α)
    (hh : s.halted = false) (hne : (exec rodata i s).err = false) (hag : Agree m' (reads s i) s) :
    exec rodata i ({ s with mem := m' } : State α) = rebase (writes s i) m' (exec rodata i s) := by
  have hT : (s.halted = true) = False := by simp [hh]
  cases i with
  | eor d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | bic d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | eor3 d a b c =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | bcax d a b c =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | rax1 d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | xar d a b n =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | shl d a n =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | sri d a n =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | addv d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | tbl d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | zip1 d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | zip2 d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | movv d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | movi0 d =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | eorx d a b n =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | bicx d a b n =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | rorx d a n =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | movx d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | movi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | add d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | sub d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | subs d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | cmp a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | csel d a b c =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | ldr r base off =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    simp only [withAddr, addr_wm] at hne ⊢
    rcases ha : addr s base off with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.loadWords_loc rodata m' s a _ (by simpa [reads, ha] using hag)]
      rw [rebase_nil]
      rcases hl : s.loadWords rodata a _ with _ | ws
      · rfl
      · simp only []
        first
        | (cases r <;> rfl)
        | (cases r1 <;> cases r2 <;> by_cases hw : wb = 0 <;> simp only [hw, ↓reduceIte] <;> rfl)
  | ldrlit r lo hi =>
    cases r <;>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | str r base off =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [withAddr, addr_wm, writes] at hne ⊢
    rcases ha : addr s base off with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.storeWords_loc m' s a]; simp only [regWords_wm]
      rcases hs : s.storeWords a (regWords s r) with _ | s'
      · simp [hs, State.fail] at hne
      · simp only [hs, Option.map_some]; rfl
  | ldp r1 r2 base off wb =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    simp only [withAddr, addr_wm] at hne ⊢
    rcases ha : addr s base (if wb = 2 then 0 else off) with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.loadWords_loc rodata m' s a _ (by simpa [reads, ha] using hag)]
      rw [rebase_nil]
      rcases hl : s.loadWords rodata a _ with _ | ws
      · rfl
      · simp only []
        first
        | (cases r <;> rfl)
        | (cases r1 <;> cases r2 <;> by_cases hw : wb = 0 <;> simp only [hw, ↓reduceIte] <;> rfl)
  | stp r1 r2 base off wb =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [withAddr, addr_wm, writes] at hne ⊢
    rcases ha : addr s base (if wb = 2 then 0 else off) with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.storeWords_loc m' s a]; simp only [regWords_wm]
      rcases hs : s.storeWords a (regWords s r1 ++ regWords s r2) with _ | s'
      · simp [hs, State.fail] at hne
      · simp only [hs, Option.map_some]
        by_cases hw : wb = 0 <;> simp only [hw, ↓reduceIte] <;> rfl
  | cbz a t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | bcond c t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | b t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | tailcall name =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | ret =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | nop =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'
  | data =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close'

theorem writes_wm (s : State (BitVec 64)) (m' : Region → Int → BitVec 64) (i : Instr) :
    writes ({ s with mem := m' } : State (BitVec 64)) i = writes s i := by
  cases i <;> rfl

/-- **The AArch64 instruction set with footprints**: the aliased machine, the access condition and
the in-place simulation of `AliasGen.lean` apply. -/
def footIsa : FootIsa where
  Instr := Instr
  nop := .nop
  exec := exec
  reads := reads
  writes := writes
  writes_wm := writes_wm
  exec_local := fun rodata m' i s hh hne hag => exec_local rodata m' i s hh hne hag
  exec_halted := fun rodata i s h => by simp [exec, h]

end Keccaktree.Asm.Arm
