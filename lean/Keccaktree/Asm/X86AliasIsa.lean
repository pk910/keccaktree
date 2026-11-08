import Keccaktree.Asm.LibAlias
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# x86 as an `AlIsa`: the generic in-place library for x86 kernels

`X86.alIsa` packages the x86 footprint lemmas (`exec_local`, `cells_map`, `cells_reloc`) as an `AlIsa`.
Its aliased machine is `X86.isaAl` (`isaAl_eq`, definitional) and its access condition is
`X86.AccessRun` (`accessRun_iff`), so the generic layer (`LibAliasGen`) applies to x86 kernels with the
types of `LibAlias`:

* **`mkKernelAlOf`**: an x86 kernel of the in-place library from *any* kernel of the separate-region
  library (`KernelThm X86.isa EntryX86 Digest`, e.g. from `mkKernel` or agent x86b's `mkKernelAnn`), its
  `AccessThm` and a `CtlThm` (the run from any control state is the normalised run with some control
  components overridden, at every step count; `ctlThm_of_pred` builds it from a run lemma such as
  `run_ovr_annJ`).  Kernels whose program passes `mkKernel`'s static check can use `mkKernelAl`
  (`LibAlias.lean`) directly.
-/
namespace Keccaktree.Asm.X86

variable {α : Type} [LaneOps α]

theorem reads_ovr (D : Dom) (c : Ctl) (s : State α) (i : Instr) : reads (ovr D c s) i = reads s i := by
  cases i <;> rfl

/-- **x86 as an instruction set for the generic in-place development.** -/
@[reducible] def alIsa : AlIsa where
  isa := X86.isa
  R := X86.isaReloc
  reads := reads
  writes := writes
  writes_wm := writes_wm
  fpOk := fun _ _ => true
  reads_ovr := fun D c s i _ => reads_ovr D c s i
  writes_ovr := fun D c s i _ => writes_ovr D c s i
  exec_local := fun rodata m' i s hh hne hag => exec_local rodata m' i s hh hne hag
  cells_map := fun f hf rodata i X hh hne => cells_map hf i X (decOk_of_exec rodata i X hh hne)
  cells_reloc := fun ρ hρ rodata i X hh hne hok => cells_reloc ρ hρ rodata i X (decOk_of_exec rodata i X hh hne) hok

theorem isaAl_eq : alIsa.isaAl = X86.isaAl := rfl

theorem accessRun_iff (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (B Bf : Int) (s : State (BitVec 64)),
      alIsa.AccessRun rodata prog n B Bf s ↔ AccessRun rodata prog n B Bf s
  | 0, B, Bf, s => Iff.rfl
  | n + 1, B, Bf, s => by
    cases hh : s.halted
    · simp only [AlIsa.AccessRun, X86.AccessRun, hh, Bool.false_eq_true, ↓reduceIte, accessRun_iff rodata prog n] <;>
        exact Iff.rfl
    · simp only [AlIsa.AccessRun, X86.AccessRun, hh, ↓reduceIte]

end Keccaktree.Asm.X86

namespace Keccaktree.Asm.LibAlias
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibAliasGen

theorem entry_mem : MemInput Entry := fun _ _ input input' S S' hE hS' hin =>
  entry_transfer _ _ input input' S S' hE hS' hin

theorem entry_pc : PcFree Entry := fun _ _ _ _ p hE => hE.with_pc p

theorem accessThm_g (rodata : Array (BitVec 64)) (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (h : AccessThm rodata prog entry steps) : AccessThmG X86.alIsa Entry rodata prog entry steps := by
  intro off count input S hE hb hpc
  obtain ⟨Bf, h1, h2⟩ := h off count input S hE hb hpc
  exact ⟨Bf, (accessRun_iff rodata prog _ _ _ _).2 h1, h2⟩

/-- **An x86 kernel of the in-place library** from any kernel of the separate-region library (any
control state at entry), its access theorem and its control theorem (the generic route; used for
kernels whose control components are handled by an annotation, e.g. the AVX-512 kernels). -/
def mkKernelAlOf (K : Library.KernelThm X86.isa EntryX86 Digest) (ha : AccessThm K.rodata K.prog K.entry K.steps)
    (hctl : CtlThm X86.alIsa Entry K.rodata K.prog K.entry K.steps) :
    Library.KernelThm X86.isaAl EntryAlX86 Digest :=
  mkKernelAlG X86.alIsa Entry entry_mem entry_pc K (accessThm_g _ _ _ _ ha) hctl

end Keccaktree.Asm.LibAlias
