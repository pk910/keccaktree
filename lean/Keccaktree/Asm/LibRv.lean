import Keccaktree.Asm.LibTable
import Keccaktree.Asm.RiscvEntryCtl
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# RISC-V kernels as kernels of the library

`mkKernelRv` turns a RISC-V kernel's all-count theorem from the normalised
control state (`NormThmRv`) into a `Library.KernelThm` for `EntryRv` (any
`vl` at entry, as the ABI leaves it),
given a dirty-set annotation of the program checked by the kernel (`annOk`,
with the entry dirty: `ann.getD entry Dom.all = Dom.all`).
-/
namespace Keccaktree.Asm.LibRv
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibTable

theorem outcome_ovr_rv (targets : List String) (off count : Nat) (input : Int → BitVec 64) (S S' X : State (BitVec 64))
    (D : Dom) (c : Ctl) (hmem : S'.mem = S.mem)
    (h : Library.Outcome EntryRv Digest targets off count input S X) :
    Library.Outcome EntryRv Digest targets off count input S' (ovr D c X) := by
  obtain ⟨hh, he, hp, hout⟩ := h
  refine ⟨hh, he, fun q hq => (hp q hq).trans (by rw [hmem]), ?_⟩
  rcases hout with ⟨ht, hd⟩ | ⟨next, done, ht, hmemb, hdone, hd, hpos, hnext⟩
  · exact Or.inl ⟨ht, hd⟩
  · refine Or.inr ⟨next, done, ht, hmemb, hdone, hd, hpos, ?_⟩
    unfold EntryRv at hnext ⊢
    rw [normCtl_ovr_upd]; exact hnext

/-- What a RISC-V kernel's generated all-count proof provides, from a normalised entry state. -/
def NormThmRv (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (targets : List String) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryR off count input S → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    Library.Outcome EntryRv Digest targets off count input S ((Riscv.isa vlmax).run rodata prog (steps off count) S)

theorem _root_.Keccaktree.Asm.LibTable.EntryR.with_pc {off count : Nat} {input : Int → BitVec 64} {S : State (BitVec 64)} (h : EntryR off count input S)
    (p : Nat) : EntryR off count input { S with pc := p } :=
  ⟨h.ctrl, h.ok, h.a2, h.sp, h.a1, h.a0, h.inp⟩

/-- **A RISC-V kernel of the library** (any `vl` at entry). -/
def mkKernelRv (vlmax : Nat) (name : String) (rank : Nat) (targets : List String) (rodata : Array (BitVec 64))
    (prog : Array Riscv.Instr) (entry : Nat) (steps : Nat → Nat → Nat) (ann : Nat → Dom)
    (hann : Riscv.AnnOk prog ann) (hentry : ann entry = Dom.all)
    (h : NormThmRv vlmax rodata prog entry steps targets) : Library.KernelThm (Riscv.isa vlmax) EntryRv Digest where
  name := name
  rank := rank
  targets := targets
  rodata := rodata
  prog := prog
  entry := entry
  steps := steps
  thm := fun off count input S hS => by
    obtain ⟨hE, hb⟩ := hS
    have h0 := h off count input { normCtl S with pc := entry } (hE.with_pc entry) hb rfl
    obtain ⟨c', hc'⟩ := Riscv.run_ovr_ann vlmax rodata prog ann hann (steps off count) { normCtl S with pc := entry }
      (Ctl.of { S with pc := entry }) h0.2.1
    have hS1 : ovr (ann ({ normCtl S with pc := entry } : State (BitVec 64)).pc) (Ctl.of { S with pc := entry })
        { normCtl S with pc := entry } = { S with pc := entry } := by
      show ovr (ann entry) _ (normCtl { S with pc := entry }) = _
      rw [hentry, ovr_normCtl]
    rw [hS1] at hc'
    rw [hc']
    exact outcome_ovr_rv targets off count input _ _ _ _ _ rfl h0

end Keccaktree.Asm.LibRv
