import Keccaktree.Asm.Compose
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
Generic chaining of concrete slices: if a concrete state has the control part
of a cut and the slice's symbolic run does not fail, the state after the
slice is the evaluation of the symbolic result, and its cut environment is
the evaluated one.  Iterating this over a kernel's slices turns the
per-slice `step` theorems (on cut environments) into a statement about the
concrete machine (`Keccaktree.Kernels.<K>.Gen.Final`).
-/
namespace Keccaktree.Asm.X86
open Keccaktree.Asm

/-- One concrete slice: from a state with the cut's control part. -/
theorem slice_concrete (isa : Isa) (rodata : Array (BitVec 64)) (slice : List isa.Instr) (ctl : List Nat)
    (cut : State E) (S : State (BitVec 64))
    (hc : cutOf ctl S = cut) (hs : S.err = false ∧ S.halted = false ∧ S.tail = none)
    (hne : (isa.execTrace rodata slice cut).err = false) :
    envOf (isa.execTrace rodata slice S) = fun i => E.eval (envOf S) (readVar (isa.execTrace rodata slice cut) i) := by
  funext i
  rw [execTrace_cut isa rodata slice ctl cut S hc hs hne, envOf_mapState]

/-- The control part of the state after a concrete slice is the symbolic result's. -/
theorem slice_ctrl (isa : Isa) (rodata : Array (BitVec 64)) (slice : List isa.Instr) (ctl : List Nat)
    (cut : State E) (S : State (BitVec 64))
    (hc : cutOf ctl S = cut) (hs : S.err = false ∧ S.halted = false ∧ S.tail = none)
    (hne : (isa.execTrace rodata slice cut).err = false) :
    let T := isa.execTrace rodata slice S
    let R := isa.execTrace rodata slice cut
    T.g = R.g ∧ T.k = R.k ∧ T.zf = R.zf ∧ T.cf = R.cf ∧ T.nf = R.nf ∧ T.vf = R.vf ∧ T.vl = R.vl ∧
    T.pc = R.pc ∧ T.depth = R.depth ∧ T.err = R.err ∧ T.halted = R.halted ∧ T.tail = R.tail := by
  intro T R
  have h := execTrace_cut isa rodata slice ctl cut S hc hs hne
  simp only [T, R, h, mapState, and_self]

/-- `cutOf ctl` only looks at the control part and the control words `ctl`:
the cut of `S` is the cut of the (closed) control state `Sc` that the
generated proofs name. -/
theorem cutOf_eq_of_ctrl (ctl : List Nat) (S Sc : State (BitVec 64))
    (h : S.g = Sc.g ∧ S.k = Sc.k ∧ S.zf = Sc.zf ∧ S.cf = Sc.cf ∧ S.nf = Sc.nf ∧ S.vf = Sc.vf ∧ S.vl = Sc.vl ∧
         S.pc = Sc.pc ∧ S.depth = Sc.depth)
    (hv : ∀ i, i ∈ ctl → envOf S i = envOf Sc i) :
    cutOf ctl S = cutOf ctl Sc := by
  have hc : ∀ i, cutVar ctl S i = cutVar ctl Sc i := by
    intro i; unfold cutVar; split
    · rename_i hi; rw [hv i (List.contains_iff_mem.mp hi)]
    · rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only [cutOf, hc, h1, h2, h3, h4, h5, h6, h7, h8, h9]

end Keccaktree.Asm.X86
