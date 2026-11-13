import Keccaktree.Asm.Final
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Composition of segment proofs: loops over batches

The generated proofs cover a *plan*: one recorded run of a kernel cut into
slices, from a cut state whose control words (pointers, counts, frame cells)
are constants.  A kernel call on `m·N + r` nodes runs the batch body `m`
times, each time with the input/output pointers advanced by one batch and the
count reduced by `N`.  The body is proved once, at its first iteration; the
other iterations are obtained by *relocation*: a translation of the pointer
constants and of the input/output memory variables, which the symbolic
execution commutes with (`RelocFacts`, to be provided by `Reloc.lean`).

This file states what the composition needs from relocation (`RelocFacts`),
derives the relocated form of a proved slice (`slice_run_reloc`) and of a
chain of slices (`seg_run_reloc`), the loop by induction (`loop_run`), and the
shape of a kernel's all-count theorem (`KernelOutcome`).  Everything here is
axiom-free: the relocation facts are hypotheses.
-/
namespace Keccaktree.Asm.Loop
open Keccaktree.Asm Keccaktree.Asm.X86

/-- Status of a concrete state at a cut (as in the generated proofs). -/
def Ok (S : State (BitVec 64)) : Prop := S.err = false ∧ S.halted = false ∧ S.tail = none

/-- What the loop composition needs from the relocation theory (`Reloc.lean`
instantiates it): relocations form a monoid; a relocation acts on `E` (leaf
substitution: pointer constants shifted, input/output memory variables moved)
and on symbolic states (lanes relocated, memory shifted); the symbolic run and
the recorded path commute with it on non-failing runs whose count-dependent
branches are *safe* (the same outcome before and after the shift, which the
loop proves from a bound on the remaining count); evaluation of a relocated
expression is evaluation of the original under the shifted environment; and
reading a variable off a relocated state is the relocation of the variable at
its original location. -/
structure RelocFacts (isa : Isa) where
  Reloc : Type
  one : Reloc
  comp : Reloc → Reloc → Reloc
  relocE : Reloc → E → E
  relocState : Reloc → State E → State E
  /-- base variable ↦ the variable at the relocated location (memory variables of the
  input/output regions shift, everything else is fixed) -/
  shiftVar : Reloc → Nat → Nat
  unshiftVar : Reloc → Nat → Nat
  shift_unshift : ∀ ρ i, shiftVar ρ (unshiftVar ρ i) = i
  unshift_shift : ∀ ρ i, unshiftVar ρ (shiftVar ρ i) = i
  /-- the count-dependent branches of a trace from a state have the same outcome after the shift -/
  BranchSafe : Reloc → Array (BitVec 64) → List isa.Instr → State E → Prop
  relocState_one : ∀ s, relocState one s = s
  relocState_comp : ∀ ρ σ s, relocState ρ (relocState σ s) = relocState (comp ρ σ) s
  execTrace_reloc : ∀ (ρ : Reloc) (rodata : Array (BitVec 64)) (l : List isa.Instr) (s : State E),
    (isa.execTrace rodata l s).err = false → BranchSafe ρ rodata l s →
    isa.execTrace rodata l (relocState ρ s) = relocState ρ (isa.execTrace rodata l s)
  pathOk_reloc : ∀ (ρ : Reloc) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (idx : List Nat) (s : State E),
    isa.pathOk rodata prog idx s = true → BranchSafe ρ rodata (idx.map (prog.getD · isa.nop)) s →
    isa.pathOk rodata prog idx (relocState ρ s) = true
  readVar_reloc : ∀ ρ (t : State E) i, readVar (relocState ρ t) i = relocE ρ (readVar t (unshiftVar ρ i))
  eval_reloc : ∀ ρ (env : Nat → BitVec 64) (e : E), E.eval env (relocE ρ e) = E.eval (fun j => env (shiftVar ρ j)) e
  err_reloc : ∀ ρ (t : State E), (relocState ρ t).err = t.err

variable {isa : Isa} (R : RelocFacts isa)

/-- The environment of a relocated run, seen through the base variables: variable `j` of the
base run is read at its shifted location. -/
def RelocFacts.envShift (ρ : R.Reloc) (env : Nat → BitVec 64) : Nat → BitVec 64 := fun j => env (R.shiftVar ρ j)

/-- …and back. -/
def RelocFacts.envUnshift (ρ : R.Reloc) (env : Nat → BitVec 64) : Nat → BitVec 64 := fun i => env (R.unshiftVar ρ i)

/-- A symbolic environment map (of one base slice or segment) conjugated by a relocation:
what the relocated run does to the environment. -/
def RelocFacts.conj (ρ : R.Reloc) (F : (Nat → BitVec 64) → (Nat → BitVec 64)) :
    (Nat → BitVec 64) → (Nat → BitVec 64) :=
  fun env => R.envUnshift ρ (F (R.envShift ρ env))

theorem RelocFacts.envUnshift_envShift (ρ : R.Reloc) (env : Nat → BitVec 64) :
    R.envUnshift ρ (R.envShift ρ env) = env := by
  funext i; simp only [RelocFacts.envUnshift, RelocFacts.envShift, R.shift_unshift]

theorem RelocFacts.envShift_envUnshift (ρ : R.Reloc) (env : Nat → BitVec 64) :
    R.envShift ρ (R.envUnshift ρ env) = env := by
  funext i; simp only [RelocFacts.envUnshift, RelocFacts.envShift, R.unshift_shift]

theorem RelocFacts.conj_comp (ρ : R.Reloc) (F G : (Nat → BitVec 64) → (Nat → BitVec 64)) :
    R.conj ρ (G ∘ F) = R.conj ρ G ∘ R.conj ρ F := by
  funext env; simp only [RelocFacts.conj, Function.comp, R.envShift_envUnshift]

/-- Reading the symbolic result of a relocated run under a concrete environment is reading the base
result under the shifted environment, at the original variable. -/
theorem RelocFacts.eval_readVar_reloc (ρ : R.Reloc) (env : Nat → BitVec 64) (t : State E) (i : Nat) :
    E.eval env (readVar (R.relocState ρ t) i) = E.eval (R.envShift ρ env) (readVar t (R.unshiftVar ρ i)) := by
  rw [R.readVar_reloc, R.eval_reloc]; rfl

/-- The symbolic environment map of a symbolic result `t`: variable `i` ↦ its lane evaluated. -/
def envMap (t : State E) : (Nat → BitVec 64) → (Nat → BitVec 64) := fun env i => E.eval env (readVar t i)

theorem RelocFacts.envMap_reloc (ρ : R.Reloc) (t : State E) : envMap (R.relocState ρ t) = R.conj ρ (envMap t) := by
  funext env i
  simp only [envMap, RelocFacts.conj, RelocFacts.envUnshift, R.eval_readVar_reloc]

/-! ## One slice, at its base position and relocated -/

/-- The recorded path ends without a fault: the symbolic run of the path's instructions does not fail. -/
theorem pathOk_execTrace (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (idx : List Nat) (s : State E)
    (h : isa.pathOk rodata prog idx s = true) :
    (isa.execTrace rodata (idx.map (prog.getD · isa.nop)) s).err = false := by
  induction idx generalizing s with
  | nil => simpa [Isa.pathOk, Isa.execTrace] using h
  | cons i rest ih =>
    simp only [Isa.pathOk, Bool.and_eq_true] at h
    simp only [List.map_cons, Isa.execTrace, List.foldl_cons]
    exact ih _ h.2

/-- The facts the generator proves about one slice, kernel-checked at its base position: the cut
(control words and the closed control state), the recorded path, and the glue to the next cut:
after the slice, the next cut's control words are the expected constants — stated for every
relocation `ρ` of the base position (the generated proof discharges it from the closed
constants and the relocation facts). -/
structure SliceFacts (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (R : RelocFacts isa) where
  ctl : List Nat
  sc : State (BitVec 64)
  idx : List Nat
  ctlNext : List Nat
  scNext : State (BitVec 64)
  path : isa.pathOk rodata prog idx (cutOf ctl sc) = true
  safe : ∀ ρ, R.BranchSafe ρ rodata (idx.map (prog.getD · isa.nop)) (cutOf ctl sc)
  glue : ∀ (ρ : R.Reloc) (S : State (BitVec 64)), cutOf ctl S = R.relocState ρ (cutOf ctl sc) → Ok S →
    Ok (isa.execTrace rodata (idx.map (prog.getD · isa.nop)) S) ∧
    cutOf ctlNext (isa.execTrace rodata (idx.map (prog.getD · isa.nop)) S) = R.relocState ρ (cutOf ctlNext scNext)

namespace SliceFacts
variable {rodata : Array (BitVec 64)} {prog : Array isa.Instr} (F : SliceFacts isa rodata prog R)

def cut : State E := cutOf F.ctl F.sc
def cutNext : State E := cutOf F.ctlNext F.scNext
def slice : List isa.Instr := F.idx.map (prog.getD · isa.nop)
def result : State E := isa.execTrace rodata F.slice F.cut
def len : Nat := F.idx.length

theorem result_err : F.result.err = false := pathOk_execTrace rodata prog F.idx F.cut F.path

/-- **A slice at a relocated position**: from a concrete state with the relocated cut, the
fetch-execute loop runs the recorded path and lands on the evaluation of the relocated symbolic
result; its cut environment is the base slice's environment map conjugated by the relocation. -/
theorem run_reloc (ρ : R.Reloc) (S : State (BitVec 64)) (hc : cutOf F.ctl S = R.relocState ρ F.cut) (hs : Ok S) :
    isa.run rodata prog F.len S = isa.execTrace rodata F.slice S ∧
    isa.execTrace rodata F.slice S = mapState (E.eval (envOf S)) (R.relocState ρ F.result) ∧
    envOf (isa.execTrace rodata F.slice S) = R.conj ρ (envMap F.result) (envOf S) := by
  have hpath := R.pathOk_reloc ρ rodata prog F.idx F.cut F.path (F.safe ρ)
  have hne : (isa.execTrace rodata F.slice (R.relocState ρ F.cut)).err = false := by
    rw [R.execTrace_reloc ρ rodata F.slice F.cut F.result_err (F.safe ρ), R.err_reloc]
    exact F.result_err
  have hrun : isa.execTrace rodata F.slice S = mapState (E.eval (envOf S)) (R.relocState ρ F.result) := by
    rw [execTrace_cut isa rodata F.slice F.ctl _ S hc hs hne,
      R.execTrace_reloc ρ rodata F.slice F.cut F.result_err (F.safe ρ)]
    rfl
  refine ⟨?_, hrun, ?_⟩
  · have h := isa.run_of_pathOk rodata prog F.idx (envOf S) (R.relocState ρ F.cut) hpath
    rw [← hc, eval_cutOf F.ctl S hs] at h
    exact h
  · rw [hrun]
    funext i
    rw [envOf_mapState, R.eval_readVar_reloc]
    rfl

end SliceFacts

/-! ## Segments: chains of slices -/

/-- Consecutive slices glue: each slice's next cut is the next slice's cut. -/
def Chained {rodata : Array (BitVec 64)} {prog : Array isa.Instr} : List (SliceFacts isa rodata prog R) → Prop
  | [] => True
  | [_] => True
  | F :: G :: rest => F.ctlNext = G.ctl ∧ F.scNext = G.sc ∧ Chained (G :: rest)

variable {rodata : Array (BitVec 64)} {prog : Array isa.Instr}

/-- The number of steps of a segment. -/
def segLen : List (SliceFacts isa rodata prog R) → Nat
  | [] => 0
  | F :: rest => F.len + segLen rest

/-- The symbolic environment map of a segment (the first slice applied first). -/
def segMap : List (SliceFacts isa rodata prog R) → (Nat → BitVec 64) → (Nat → BitVec 64)
  | [] => id
  | F :: rest => segMap rest ∘ envMap F.result

/-- The cut a segment starts from / ends at. -/
def segStart (F : SliceFacts isa rodata prog R) (L : List (SliceFacts isa rodata prog R)) : List Nat × State E :=
  (F.ctl, F.cut)
def segEnd (F : SliceFacts isa rodata prog R) : List (SliceFacts isa rodata prog R) → List Nat × State E
  | [] => (F.ctlNext, F.cutNext)
  | G :: rest => segEnd G rest

theorem RelocFacts.conj_id (ρ : R.Reloc) : R.conj ρ id = id := by
  funext env; simp only [RelocFacts.conj, id, R.envUnshift_envShift]

/-- **A segment at a relocated position**: the slices run one after the other along their recorded
paths; the final state is `Ok`, has the segment's end cut relocated, and its environment is the
segment's map conjugated by the relocation. -/
theorem seg_run_reloc (F : SliceFacts isa rodata prog R) (L : List (SliceFacts isa rodata prog R))
    (hch : Chained R (F :: L)) (ρ : R.Reloc) (S : State (BitVec 64))
    (hc : cutOf F.ctl S = R.relocState ρ F.cut) (hs : Ok S) :
    Ok (isa.run rodata prog (segLen R (F :: L)) S) ∧
    cutOf (segEnd R F L).1 (isa.run rodata prog (segLen R (F :: L)) S) = R.relocState ρ (segEnd R F L).2 ∧
    envOf (isa.run rodata prog (segLen R (F :: L)) S) = R.conj ρ (segMap R (F :: L)) (envOf S) := by
  induction L generalizing F S with
  | nil =>
    have h := F.run_reloc R ρ S hc hs
    have hg := F.glue ρ S hc hs
    simp only [segLen, Nat.add_zero, segEnd, segMap, Function.comp_id]
    rw [h.1]
    exact ⟨hg.1, hg.2, h.2.2⟩
  | cons G rest ih =>
    obtain ⟨h1, h2, hrest⟩ := hch
    have h := F.run_reloc R ρ S hc hs
    have hg := F.glue ρ S hc hs
    have hc' : cutOf G.ctl (isa.execTrace rodata F.slice S) = R.relocState ρ G.cut := by
      unfold SliceFacts.cut; rw [← h1, ← h2]; exact hg.2
    have this := ih G hrest (isa.execTrace rodata F.slice S) hc' hg.1
    have hlen : segLen R (F :: G :: rest) = F.len + segLen R (G :: rest) := rfl
    have hend : segEnd R F (G :: rest) = segEnd R G rest := rfl
    have hmap : segMap R (F :: G :: rest) = segMap R (G :: rest) ∘ envMap F.result := rfl
    rw [hlen, hend, hmap, Isa.run_add, h.1]
    refine ⟨this.1, this.2.1, ?_⟩
    rw [this.2.2, h.2.2, R.conj_comp]
    rfl

/-! ## The loop -/

/-- Powers of a relocation: `pow ρ k` is `k` iterations. -/
def RelocFacts.pow (ρ : R.Reloc) : Nat → R.Reloc
  | 0 => R.one
  | k + 1 => R.comp (pow ρ k) ρ

/-- The facts about the loop body: a chained non-empty segment that starts at the loop-head cut
`(ctl, cut)` and ends at the same cut relocated by one iteration `step`. -/
structure IterFacts (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (R : RelocFacts isa) where
  F : SliceFacts isa rodata prog R
  L : List (SliceFacts isa rodata prog R)
  chained : Chained R (F :: L)
  step : R.Reloc
  /-- the body ends at the head cut relocated by one iteration -/
  wrap : (segEnd R F L).1 = F.ctl ∧ (segEnd R F L).2 = R.relocState step F.cut

namespace IterFacts
variable (I : IterFacts isa rodata prog R)

abbrev len : Nat := segLen R (I.F :: I.L)
abbrev map : (Nat → BitVec 64) → (Nat → BitVec 64) := segMap R (I.F :: I.L)

/-- The environment after `m` iterations from iteration `k₀`. -/
def envAfter (k₀ : Nat) : Nat → (Nat → BitVec 64) → (Nat → BitVec 64)
  | 0 => id
  | m + 1 => fun env => R.conj (RelocFacts.pow R I.step (k₀ + m)) (segMap R (I.F :: I.L)) (envAfter k₀ m env)

/-- **The loop by induction**: from the loop head at iteration `k₀` (the head cut relocated by
`k₀` steps), `m` iterations of the body reach the loop head at iteration `k₀ + m`, `Ok`, with the
environment transformed by the `m` conjugated body maps. -/
theorem run (k₀ m : Nat) (S : State (BitVec 64))
    (hc : cutOf I.F.ctl S = R.relocState (RelocFacts.pow R I.step k₀) I.F.cut) (hs : Ok S) :
    Ok (isa.run rodata prog (m * IterFacts.len R I) S) ∧
    cutOf I.F.ctl (isa.run rodata prog (m * IterFacts.len R I) S) = R.relocState (RelocFacts.pow R I.step (k₀ + m)) I.F.cut ∧
    envOf (isa.run rodata prog (m * IterFacts.len R I) S) = IterFacts.envAfter R I k₀ m (envOf S) := by
  induction m generalizing S with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
    exact ⟨hs, hc, rfl⟩
  | succ m ih =>
    have h := seg_run_reloc R I.F I.L I.chained (RelocFacts.pow R I.step (k₀ + m)) _ (ih S hc hs).2.1 (ih S hc hs).1
    rw [I.wrap.1, I.wrap.2, R.relocState_comp] at h
    rw [Nat.succ_mul, Isa.run_add]
    refine ⟨h.1, ?_, ?_⟩
    · rw [h.2.1]; rfl
    · rw [h.2.2, (ih S hc hs).2.2]; rfl

end IterFacts

/-! ## The all-count theorem of a kernel -/

/-- What a kernel call does, for the library theorem: it halts without a model fault, and either
every node's digest is in place (`done`), or it hands the remaining nodes over to another kernel
by a tail call, from a state that is that kernel's entry state on the remaining nodes with the
pointers advanced (`handover`).  `digest input Sf n` says node `n`'s digest is in place in `Sf`. -/
inductive KernelOutcome (digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop)
    (entryOf : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop)
    (input : Int → BitVec 64) (count : Nat) (Sf : State (BitVec 64)) : Prop
  | done (hh : Sf.halted = true) (he : Sf.err = false) (ht : Sf.tail = none)
      (hd : ∀ n, n < count → digest input Sf n)
  | handover (K : String) (doneCount : Nat) (hh : Sf.halted = true) (he : Sf.err = false) (ht : Sf.tail = some K)
      (hlt : doneCount < count)
      (hd : ∀ n, n < doneCount → digest input Sf n)
      (hnext : entryOf K doneCount (count - doneCount) input Sf)

end Keccaktree.Asm.Loop
