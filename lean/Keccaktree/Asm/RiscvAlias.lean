import Keccaktree.Asm.AliasGen
import Keccaktree.Asm.ArmAlias
import Keccaktree.Asm.RiscvFoot
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# RISC-V read footprints and memory locality (in-place hashing)

`Riscv.reads`: the cells a RISC-V step loads (`ld`: one word, `vlseg`: `nf·vl` words);
`exec_local` as for x86; `footIsa vlmax`: the instruction set with footprints (`AliasGen.lean`).
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 (State rebase Agree rebase_nil)
open Keccaktree.Asm.Arm (gx setX withX addr withAddr)
open LaneOps

variable {α : Type} [LaneOps α]

def reads (s : State α) : Instr → List (Region × Int)
  | .ld _ base off => match addr s base off with
    | some a => storeCells a 1
    | none => []
  | .vlseg _ base nf => match addr s base 0 with
    | some a => storeCells a (nf * s.vl)
    | none => []
  | _ => []

@[simp] theorem getR_wm (s : State α) (m' : Region → Int → α) (n : Nat) :
    getR ({ s with mem := m' } : State α) n = getR s n := rfl
@[simp] theorem lane_wm (s : State α) (m' : Region → Int → α) (n l : Nat) :
    lane ({ s with mem := m' } : State α) n l = lane s n l := rfl
@[simp] theorem vl_wm (s : State α) (m' : Region → Int → α) : ({ s with mem := m' } : State α).vl = s.vl := rfl

theorem setActive_wm (s : State α) (m' : Region → Int → α) (d : Nat) (f : Nat → α) :
    setActive ({ s with mem := m' } : State α) d f = { setActive s d f with mem := m' } := rfl

theorem foldl_setActive_wm (l : List Nat) (g : Nat → Nat → α) (d : Nat) (s : State α) (m' : Region → Int → α) :
    l.foldl (fun s' f => setActive s' (d + f) (g f)) ({ s with mem := m' } : State α) =
      { l.foldl (fun s' f => setActive s' (d + f) (g f)) s with mem := m' } := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; rw [setActive_wm, ih]

syntax "wm_close''" : tactic
macro_rules
  | `(tactic| wm_close'') => `(tactic| first
    | rfl
    | (split <;> rename_i h <;> (try simp only [h, ↓reduceIte]) <;> wm_close'')
    | (simp only [getR_wm, lane_wm, vl_wm, X86.getGD_wm, X86.getV_wm, Arm.gx_wm', withX, setR] <;> wm_close''))

set_option maxHeartbeats 8000000 in
/-- **Memory locality of a RISC-V step** (as `X86.exec_local`). -/
theorem exec_local (vlmax : Nat) (rodata : Array (BitVec 64)) (m' : Region → Int → α) (i : Instr) (s : State α)
    (hh : s.halted = false) (hne : (exec vlmax rodata i s).err = false) (hag : Agree m' (reads s i) s) :
    exec vlmax rodata i ({ s with mem := m' } : State α) = rebase (writes s i) m' (exec vlmax rodata i s) := by
  have hT : (s.halted = true) = False := by simp [hh]
  cases i with
  | op d a b k =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | opi d a k imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | li d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | mv d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | not d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | lea d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | ld d base off =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    simp only [withAddr, Arm.addr_wm] at hne ⊢
    rcases ha : addr s base off with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.loadWords_loc rodata m' s a _ (by simpa [reads, ha] using hag), rebase_nil]
      wm_close''
  | sd src base off =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [withAddr, Arm.addr_wm, writes] at hne ⊢
    rcases ha : addr s base off with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.storeWords_loc m' s a]
      rcases hs : s.storeWords a [getR s src] with _ | s'
      · simp [hs, State.fail] at hne
      · simp only [hs, Option.map_some, getR_wm]; rfl
  | br c a b t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | j t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | ret =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | nop =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | unsupported name =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vsetvli d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vop d a b k =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vnot d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vshifti d a k imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vshiftx d a k x =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vxorx d a x =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vmvi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vmvx d x =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vmvv d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vlseg d base nf =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    simp only [withAddr, Arm.addr_wm] at hne ⊢
    rcases ha : addr s base 0 with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.loadWords_loc rodata m' s a _ (by simpa [reads, ha] using hag), rebase_nil]
      rcases hl : s.loadWords rodata a (nf * s.vl) with _ | ws
      · rfl
      · simp only []
        rw [foldl_setActive_wm _ (fun f l => ws.getD (nf * l + f) (LaneOps.const 0))]; rfl
  | vsseg src base nf =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [withAddr, Arm.addr_wm, writes] at hne ⊢
    rcases ha : addr s base 0 with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      simp only [lane_wm, vl_wm]
      rw [X86.storeWords_loc m' s a]
      rcases hs : s.storeWords a ((List.range (nf * s.vl)).map fun q => lane s (src + q % nf) (q / nf)) with _ | s'
      · simp [hs, State.fail] at hne
      · simp only [hs, Option.map_some, List.length_map, List.length_range]; rfl

theorem writes_wm (s : State (BitVec 64)) (m' : Region → Int → BitVec 64) (i : Instr) :
    writes ({ s with mem := m' } : State (BitVec 64)) i = writes s i := by
  cases i <;> rfl

/-- **The RISC-V instruction set (VLEN = 64·`vlmax`) with footprints.** -/
def footIsa (vlmax : Nat) : FootIsa where
  Instr := Instr
  nop := .nop
  exec := exec vlmax
  reads := reads
  writes := writes
  writes_wm := writes_wm
  exec_local := fun rodata m' i s hh hne hag => exec_local vlmax rodata m' i s hh hne hag
  exec_halted := fun rodata i s h => by simp [exec, h]

end Keccaktree.Asm.Riscv
