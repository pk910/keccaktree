import Keccaktree.Asm.ArmAliasTrace
import Keccaktree.Asm.RiscvAlias
import Keccaktree.Asm.RiscvReloc
import Keccaktree.Asm.LibRv
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# RISC-V in place: footprints of relocated runs, the aliased machine, the in-place library

As `ArmAliasTrace.lean`: `cells_map`, `cells_reloc` (`ld`/`vlseg`, `sd`/`vsseg`), **`Riscv.alIsa vlmax`**,
**`mkKernelRvAl`**, **`lib_inplace_rv`**.  The vector loads and stores move `nf·vl` words, so their
footprint depends on `vl`: it is control-independent exactly when the instruction may run with the
dirty set (`fpOk := ctlOk`, no vector instruction with `vl` dirty) — what the kernels' `vl`
annotations (`Kernels/RvVl.lean`) check.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 (State Dom Ctl ovr mapState relocState shiftCell)
open Keccaktree.Asm.Arm (gx setX withX addr withAddr addr_map_some addr_reloc addr_some_of_withAddr)
open LaneOps

variable {α β : Type} [LaneOps α] [LaneOps β]

theorem writes_wm' (s : State α) (m' : Region → Int → α) (i : Instr) :
    writes ({ s with mem := m' } : State α) i = writes s i := by
  cases i <;> rfl

theorem ovr_vl_clean (D : Dom) (c : Ctl) (s : State α) (h : D.vl = false) : (ovr D c s).vl = s.vl := by
  simp [ovr, h]

theorem reads_ovr (D : Dom) (c : Ctl) (s : State α) (i : Instr) (h : ctlOk D i = true) :
    reads (ovr D c s) i = reads s i := by
  cases i
  case vlseg d base nf =>
    have hv : D.vl = false := by simpa [ctlOk, isVec] using h
    simp only [reads, ovr_vl_clean D c s hv] <;> rfl
  all_goals rfl

theorem writes_ovr (D : Dom) (c : Ctl) (s : State α) (i : Instr) (h : ctlOk D i = true) :
    writes (ovr D c s) i = writes s i := by
  cases i
  case vsseg src base nf =>
    have hv : D.vl = false := by simpa [ctlOk, isVec] using h
    simp only [writes, ovr_vl_clean D c s hv] <;> rfl
  all_goals rfl

set_option maxHeartbeats 4000000 in
/-- **Footprints under evaluation** (RISC-V). -/
theorem cells_map {f : α → β} (hf : IsHom f) (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (X : State α)
    (hh : X.halted = false) (hne : (exec vlmax rodata i X).err = false) :
    reads (mapState f X) i = reads X i ∧ writes (mapState f X) i = writes X i := by
  have hT : (X.halted = true) = False := by simp [hh]
  cases i
  case ld d base off =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    simp [reads, writes, ha, addr_map_some hf _ _ _ _ ha]
  case sd src base off =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    simp [reads, writes, ha, addr_map_some hf _ _ _ _ ha]
  case vlseg d base nf =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hv : (mapState f X).vl = X.vl := rfl
    refine ⟨?_, ?_⟩ <;> simp only [reads, writes, ha, addr_map_some hf _ _ _ _ ha, hv]
  case vsseg src base nf =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hv : (mapState f X).vl = X.vl := rfl
    refine ⟨?_, ?_⟩ <;> simp only [reads, writes, ha, addr_map_some hf _ _ _ _ ha, hv]
  all_goals exact ⟨rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **Footprints under relocation** (RISC-V). -/
theorem cells_reloc (ρ : Reloc) (hρ : ρ.ok) (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (X : State E)
    (hh : X.halted = false) (hne : (exec vlmax rodata i X).err = false) (hok : ∀ e ∈ decodes rodata i X, E.relocOk ρ e) :
    reads (relocState ρ X) i = (reads X i).map (shiftCell ρ) ∧
      writes (relocState ρ X) i = (writes X i).map (shiftCell ρ) := by
  have hT : (X.halted = true) = False := by simp [hh]
  cases i
  case ld d base off =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hr := addr_reloc ρ hρ X base off a ha (hok _ (by simp [decodes]))
    simp [reads, writes, ha, hr, X86.storeCells_addr ρ hρ]
  case sd src base off =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hr := addr_reloc ρ hρ X base off a ha (hok _ (by simp [decodes]))
    simp [reads, writes, ha, hr, X86.storeCells_addr ρ hρ]
  case vlseg d base nf =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hr := addr_reloc ρ hρ X base 0 a ha (hok _ (by simp [decodes]))
    have hv : (relocState ρ X).vl = X.vl := rfl
    refine ⟨?_, ?_⟩ <;> simp only [reads, writes, ha, hr, hv, X86.storeCells_addr ρ hρ, List.map_nil]
  case vsseg src base nf =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨a, ha⟩ := addr_some_of_withAddr _ _ _ _ hne
    have hr := addr_reloc ρ hρ X base 0 a ha (hok _ (by simp [decodes]))
    have hv : (relocState ρ X).vl = X.vl := rfl
    refine ⟨?_, ?_⟩ <;> simp only [reads, writes, ha, hr, hv, X86.storeCells_addr ρ hρ, List.map_nil]
  all_goals exact ⟨rfl, rfl⟩

/-- **RISC-V (VLEN = 64·`vlmax`) as an instruction set for the in-place development.** -/
def alIsa (vlmax : Nat) : AlIsa where
  isa := isa vlmax
  R := isaReloc vlmax
  reads := reads
  writes := writes
  writes_wm := writes_wm'
  fpOk := ctlOk
  reads_ovr := fun D c s i h => reads_ovr D c s i h
  writes_ovr := fun D c s i h => writes_ovr D c s i h
  exec_local := fun rodata m' i s hh hne hag => exec_local vlmax rodata m' i s hh hne hag
  cells_map := fun f hf rodata i X hh hne => cells_map hf vlmax rodata i X hh hne
  cells_reloc := fun ρ hρ rodata i X hh hne hok => cells_reloc ρ hρ vlmax rodata i X hh hne hok

end Keccaktree.Asm.Riscv

/-! ## The in-place RISC-V library -/
namespace Keccaktree.Asm.LibRvAl
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibTable Keccaktree.Asm.LibAliasGen

/-- **The in-place RISC-V calling convention** (any `vl` at entry). -/
abbrev EntryRvAl := EntryAlG EntryR

/-- What a RISC-V kernel's in-place proof provides (`AccessThmG` for `Riscv.alIsa vlmax`, `EntryR`). -/
abbrev AccessThmRv (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (entry : Nat)
    (steps : Nat → Nat → Nat) : Prop :=
  AccessThmG (Riscv.alIsa vlmax) EntryR rodata prog entry steps

theorem entryR_mem : MemInput EntryR := by
  intro off count input input' S S' hE hS' hin
  rw [hS']
  exact ⟨hE.ctrl, hE.ok, hE.a2, hE.sp, hE.a1, hE.a0, hin⟩

theorem entryR_pc : PcFree EntryR := fun _ _ _ _ p hE => hE.with_pc p

/-- **A RISC-V kernel of the in-place library**: the arguments of `LibRv.mkKernelRv` and the kernel's
access theorem. -/
def mkKernelRvAl (vlmax : Nat) (name : String) (rank : Nat) (targets : List String) (rodata : Array (BitVec 64))
    (prog : Array Riscv.Instr) (entry : Nat) (steps : Nat → Nat → Nat) (ann : Nat → Dom)
    (hann : Riscv.AnnOk prog ann) (hentry : ann entry = Dom.all)
    (h : LibRv.NormThmRv vlmax rodata prog entry steps targets) (ha : AccessThmRv vlmax rodata prog entry steps) :
    Library.KernelThm (Riscv.alIsa vlmax).isaAl EntryRvAl Digest :=
  mkKernelAlG (Riscv.alIsa vlmax) EntryR entryR_mem entryR_pc
    (LibRv.mkKernelRv vlmax name rank targets rodata prog entry steps ann hann hentry h) ha
    (ctlThm_of (Riscv.alIsa vlmax) EntryR rodata prog entry steps ann hentry (fun p => (hann p).1)
      (fun n s c he => Riscv.run_ovr_ann vlmax rodata prog ann hann n s c he))

/-- **The in-place RISC-V library**, for every vector length (as `LibTable.lib_rv`). -/
theorem lib_inplace_rv (vlmax : Nat) (T : Library.Table (Riscv.alIsa vlmax).isaAl EntryRvAl Digest)
    (hT : T.shape = rvShape) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryRvAl K.name off count input S → Library.LibOk T K off count input S :=
  lib_of_shape T rvShape hT rvShape_ok

end Keccaktree.Asm.LibRvAl
