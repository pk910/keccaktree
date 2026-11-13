import Keccaktree.Asm.LibTable
import Keccaktree.Asm.ArmEntryCtl
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# AArch64 kernels as kernels of the library

`mkKernelArm` turns an AArch64 kernel's all-count theorem from the normalised
control state (`NormThmArm`) into a `Library.KernelThm` for `EntryArm` (any
NZCV flags at entry — after a tail call, or as the ABI leaves them at a call),
given a dirty-set annotation of the program checked by the kernel (`annOk`,
with the entry dirty: `ann.getD entry Dom.all = Dom.all`).
-/
namespace Keccaktree.Asm.LibArm
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibTable

theorem outcome_ovr_arm (targets : List String) (off count : Nat) (input : Int → BitVec 64) (S S' X : State (BitVec 64))
    (D : Dom) (c : Ctl) (hmem : S'.mem = S.mem)
    (h : Library.Outcome EntryArm Digest targets off count input S X) :
    Library.Outcome EntryArm Digest targets off count input S' (ovr D c X) := by
  obtain ⟨hh, he, hp, hout⟩ := h
  refine ⟨hh, he, fun q hq => (hp q hq).trans (by rw [hmem]), ?_⟩
  rcases hout with ⟨ht, hd⟩ | ⟨next, done, ht, hmemb, hdone, hd, hnext⟩
  · exact Or.inl ⟨ht, hd⟩
  · refine Or.inr ⟨next, done, ht, hmemb, hdone, hd, ?_⟩
    unfold EntryArm at hnext ⊢
    rw [normCtl_ovr_upd]; exact hnext

/-- What an AArch64 kernel's generated all-count proof provides, from a normalised entry state. -/
def NormThmArm (rodata : Array (BitVec 64)) (prog : Array Arm.Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (targets : List String) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryA off count input S → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    Library.Outcome EntryArm Digest targets off count input S (Arm.isa.run rodata prog (steps off count) S)

theorem _root_.Keccaktree.Asm.LibTable.EntryA.with_pc {off count : Nat} {input : Int → BitVec 64} {S : State (BitVec 64)} (h : EntryA off count input S)
    (p : Nat) : EntryA off count input { S with pc := p } :=
  ⟨h.ctrl, h.ok, h.x2, h.sp, h.x1, h.x0, h.inp⟩

/-- **An AArch64 kernel of the library** (any flags at entry). -/
def mkKernelArm (name : String) (rank : Nat) (targets : List String) (rodata : Array (BitVec 64))
    (prog : Array Arm.Instr) (entry : Nat) (steps : Nat → Nat → Nat) (ann : Nat → Dom)
    (hann : Arm.AnnOk prog ann) (hentry : ann entry = Dom.all)
    (h : NormThmArm rodata prog entry steps targets) : Library.KernelThm Arm.isa EntryArm Digest where
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
    obtain ⟨c', hc'⟩ := Arm.run_ovr_ann rodata prog ann hann (steps off count) { normCtl S with pc := entry }
      (Ctl.of { S with pc := entry }) h0.2.1
    have hS1 : ovr (ann ({ normCtl S with pc := entry } : State (BitVec 64)).pc) (Ctl.of { S with pc := entry })
        { normCtl S with pc := entry } = { S with pc := entry } := by
      show ovr (ann entry) _ (normCtl { S with pc := entry }) = _
      rw [hentry, ovr_normCtl]
    rw [hS1] at hc'
    rw [hc']
    exact outcome_ovr_arm targets off count input _ _ _ _ _ rfl h0

end Keccaktree.Asm.LibArm
