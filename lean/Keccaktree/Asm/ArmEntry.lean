import Keccaktree.Asm.Nodes
import Keccaktree.Asm.LibArm
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
/-!
# The AArch64 calling convention of the library (shared by the AArch64 all-count theorems)

`Arm.Entry off count input S`: the state at the entry of a call `kernel(out, in, count)` at node
offset `off` (AAPCS64): `x0`/`x1` at node `off` of the output/input regions, `x2 = count`, `sp` at the
top of the stack region, the input region holding the message, the control part of a fresh call
**except the flags (any)**.  The vector registers, the other general registers and every other memory
word are arbitrary.  The library's convention is `LibTable.EntryArm` (agent `lib`); the two lemmas below
convert between them.
-/
namespace Keccaktree.Asm.Arm
open Keccaktree.Asm Keccaktree.Asm.X86

structure Entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.vl = 0 ∧ S.pc = 0 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  x2 : S.getGD 2 = gprWord ⟨0, count⟩
  sp : S.getGD 31 = gprWord ⟨rStack, 1048576⟩
  x1 : S.getGD 1 = gprWord ⟨rInput, 64 * off⟩
  x0 : S.getGD 0 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

/-- The library's entry state (`LibTable.EntryA`: flags clear, any `pc`) at `pc = 0` is an entry state. -/
theorem entry_of_entryA {off count : Nat} {input : Int → BitVec 64} {S : State (BitVec 64)}
    (h : LibTable.EntryA off count input S) (hpc : S.pc = 0) : Entry off count input S :=
  ⟨⟨h.ctrl.1, h.ctrl.2.1, h.ctrl.2.2.2.2.2.2.1, hpc, h.ctrl.2.2.2.2.2.2.2⟩, h.ok, h.x2, h.sp, h.x1, h.x0, h.inp⟩

/-- A hand-over state that is an entry state (at `pc = 0`) satisfies the library's AArch64 calling
convention (`LibTable.EntryArm`: the normalised control part). -/
theorem entryA_of_entry {off count : Nat} {input : Int → BitVec 64} {X : State (BitVec 64)}
    (h : Entry off count input { X with pc := 0 }) : LibTable.EntryA off count input (normCtl X) :=
  ⟨⟨h.ctrl.1, normCtl_k X, rfl, rfl, rfl, rfl, rfl, h.ctrl.2.2.2.2⟩, h.ok, h.x2, h.sp, h.x1, h.x0, h.inp⟩

end Keccaktree.Asm.Arm
