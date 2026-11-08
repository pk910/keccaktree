import Keccaktree.Asm.LibAliasGen
import Keccaktree.Asm.ArmAlias
import Keccaktree.Asm.ArmReloc
import Keccaktree.Asm.LibArm
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# AArch64 in place: footprints of relocated runs, the aliased machine, the in-place library

* `cells_map`, `cells_reloc`: an AArch64 step's read and write cells (`ldr`/`ldp`, `str`/`stp`) in an
  evaluated / relocated state are those of the symbolic state (shifted by the relocation);
  `reads_ovr`/`writes_ovr`: they do not depend on the flags.
* **`Arm.alIsa`**: AArch64 as an `AlIsa` — the aliased machine `Arm.alIsa.isaAl`, the simulation, the
  segment hook (`Arm.alIsa.chain_access` on the generated `SliceCert Arm.isa Arm.isaReloc` lists) of
  `AliasIsa.lean`.
* **`mkKernelArmAl`**: an AArch64 kernel of the in-place library (`EntryArmAl`: any flags at entry) from
  the kernel's normalised all-count theorem (`NormThmArm`), its flag annotation (as `mkKernelArm`) and
  its access theorem (`AccessThmArm`); **`lib_inplace_arm`**: the in-place AArch64 library for a table of
  the library's shape.
-/
namespace Keccaktree.Asm.Arm
open Keccaktree.Asm
open Keccaktree.Asm.X86 (State Dom Ctl ovr mapState relocState shiftCell)
open LaneOps

variable {α β : Type} [LaneOps α] [LaneOps β]

theorem writes_wm' (s : State α) (m' : Region → Int → α) (i : Instr) :
    writes ({ s with mem := m' } : State α) i = writes s i := by
  cases i <;> rfl

theorem reads_ovr (D : Dom) (c : Ctl) (s : State α) (i : Instr) : reads (ovr D c s) i = reads s i := by
  cases i <;> rfl

theorem writes_ovr (D : Dom) (c : Ctl) (s : State α) (i : Instr) : writes (ovr D c s) i = writes s i := by
  cases i <;> rfl

theorem addr_some_of_withAddr (s : State α) (base : Nat) (off : Int) (k : Addr → State α)
    (h : (withAddr s base off k).err = false) : ∃ a, addr s base off = some a := by
  simp only [withAddr] at h
  split at h
  · rename_i a ha; exact ⟨a, ha⟩
  · simp [State.fail] at h

set_option maxHeartbeats 4000000 in
/-- **Footprints under evaluation** (AArch64). -/
theorem cells_map {f : α → β} (hf : IsHom f) (rodata : Array (BitVec 64)) (i : Instr) (X : State α)
    (hh : X.halted = false) (hne : (exec rodata i X).err = false) :
    reads (mapState f X) i = reads X i ∧ writes (mapState f X) i = writes X i := by
  have hT : (X.halted = true) = False := by simp [hh]
  cases i
  case ldr r base off =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    simp [reads, writes, ha, addr_map_some hf _ _ _ _ ha]
  case str r base off =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    simp [reads, writes, ha, addr_map_some hf _ _ _ _ ha, regWords_map hf]
  case ldp r1 r2 base off wb =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    simp [reads, writes, ha, addr_map_some hf _ _ _ _ ha]
  case stp r1 r2 base off wb =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    simp [reads, writes, ha, addr_map_some hf _ _ _ _ ha, regWords_map hf]
  all_goals exact ⟨rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **Footprints under relocation** (AArch64). -/
theorem cells_reloc (ρ : Reloc) (hρ : ρ.ok) (rodata : Array (BitVec 64)) (i : Instr) (X : State E)
    (hh : X.halted = false) (hne : (exec rodata i X).err = false) (hok : ∀ e ∈ decodes rodata i X, E.relocOk ρ e) :
    reads (relocState ρ X) i = (reads X i).map (shiftCell ρ) ∧
      writes (relocState ρ X) i = (writes X i).map (shiftCell ρ) := by
  have hT : (X.halted = true) = False := by simp [hh]
  cases i
  case ldr r base off =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hr := addr_reloc ρ hρ X base off a ha (hok _ (by simp [decodes]))
    simp [reads, writes, ha, hr, X86.storeCells_addr ρ hρ]
  case str r base off =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hr := addr_reloc ρ hρ X base off a ha (hok _ (by simp [decodes]))
    simp [reads, writes, ha, hr, X86.storeCells_addr ρ hρ, regWords_reloc]
  case ldp r1 r2 base off wb =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hr := addr_reloc ρ hρ X base _ a ha (hok _ (by simp [decodes]))
    simp [reads, writes, ha, hr, X86.storeCells_addr ρ hρ]
  case stp r1 r2 base off wb =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hr := addr_reloc ρ hρ X base _ a ha (hok _ (by simp [decodes]))
    simp [reads, writes, ha, hr, X86.storeCells_addr ρ hρ, regWords_reloc]
  all_goals exact ⟨rfl, rfl⟩

/-- **AArch64 as an instruction set for the in-place development.** -/
def alIsa : AlIsa where
  isa := isa
  R := isaReloc
  reads := reads
  writes := writes
  writes_wm := writes_wm'
  fpOk := fun _ _ => true
  reads_ovr := fun D c s i _ => reads_ovr D c s i
  writes_ovr := fun D c s i _ => writes_ovr D c s i
  exec_local := fun rodata m' i s hh hne hag => exec_local rodata m' i s hh hne hag
  cells_map := fun f hf rodata i X hh hne => cells_map hf rodata i X hh hne
  cells_reloc := fun ρ hρ rodata i X hh hne hok => cells_reloc ρ hρ rodata i X hh hne hok

end Keccaktree.Asm.Arm

/-! ## The in-place AArch64 library -/
namespace Keccaktree.Asm.LibArmAl
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibTable Keccaktree.Asm.LibAliasGen

/-- **The in-place AArch64 calling convention** (any flags at entry). -/
abbrev EntryArmAl := EntryAlG EntryA

/-- What an AArch64 kernel's in-place proof provides (`AccessThmG` for `Arm.alIsa`, `EntryA`). -/
abbrev AccessThmArm (rodata : Array (BitVec 64)) (prog : Array Arm.Instr) (entry : Nat) (steps : Nat → Nat → Nat) : Prop :=
  AccessThmG Arm.alIsa EntryA rodata prog entry steps

theorem entryA_mem : MemInput EntryA := by
  intro off count input input' S S' hE hS' hin
  rw [hS']
  exact ⟨hE.ctrl, hE.ok, hE.x2, hE.sp, hE.x1, hE.x0, hin⟩

theorem entryA_pc : PcFree EntryA := fun _ _ _ _ p hE => hE.with_pc p

/-- **An AArch64 kernel of the in-place library**: the arguments of `LibArm.mkKernelArm` and the
kernel's access theorem. -/
def mkKernelArmAl (name : String) (rank : Nat) (targets : List String) (rodata : Array (BitVec 64))
    (prog : Array Arm.Instr) (entry : Nat) (steps : Nat → Nat → Nat) (ann : Nat → Dom)
    (hann : Arm.AnnOk prog ann) (hentry : ann entry = Dom.all)
    (h : LibArm.NormThmArm rodata prog entry steps targets) (ha : AccessThmArm rodata prog entry steps) :
    Library.KernelThm Arm.alIsa.isaAl EntryArmAl Digest :=
  mkKernelAlG Arm.alIsa EntryA entryA_mem entryA_pc
    (LibArm.mkKernelArm name rank targets rodata prog entry steps ann hann hentry h) ha
    (ctlThm_of Arm.alIsa EntryA rodata prog entry steps ann hentry (fun _ => rfl)
      (fun n s c he => Arm.run_ovr_ann rodata prog ann hann n s c he))

/-- **The in-place AArch64 library** (as `LibTable.lib_arm`). -/
theorem lib_inplace_arm (T : Library.Table Arm.alIsa.isaAl EntryArmAl Digest) (hT : T.shape = armShape) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryArmAl K.name off count input S → Library.LibOk T K off count input S :=
  lib_of_shape T armShape hT armShape_ok

end Keccaktree.Asm.LibArmAl
