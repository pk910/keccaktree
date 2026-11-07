import Keccaktree.Asm.Loop
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The library: kernels handing nodes over to each other

A kernel call on `count` nodes either finishes every node or ends in a tail
call to another kernel of the library with the remaining nodes (`jmp
other_kernel`, modelled as halting with `tail = some name`).  A call starts at
the kernel's entry instruction (`pc := entry`); the calling convention
`EntryAt` constrains the rest of the state.  `LibRun`
continues in the called kernel from the hand-over state; the library theorem
chains the per-kernel all-count theorems by strong induction on the measure
`count · (maxRank + 1) + rank`: a hand-over either finishes nodes (`count`
decreases) or, at the entry of a kernel, goes to a kernel of lower rank.

The calling convention (`EntryAt`: the entry state of a kernel on `count`
nodes at node offset `off`), the digest predicate and the per-kernel theorems
are parameters: each ISA instantiates them with its models and generated
proofs.
-/
namespace Keccaktree.Asm.Library
open Keccaktree.Asm Keccaktree.Asm.X86

/-- What a kernel call on `count` nodes at node offset `off` (entry state `S`) must achieve, for
the final state `Sf`: halted without a model fault, the earlier output words untouched, and either
no tail call with every node's digest in place, or a tail call to one of `targets` with the
first `done` nodes finished and the remaining ones handed over from that kernel's entry state
(pointers advanced). -/
def Outcome (EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop)
    (Digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop) (targets : List String)
    (off count : Nat) (input : Int → BitVec 64) (S Sf : State (BitVec 64)) : Prop :=
  Sf.halted = true ∧ Sf.err = false ∧
  (∀ q : Int, q < 4 * off → Sf.mem rOutput q = S.mem rOutput q) ∧
  ((Sf.tail = none ∧ ∀ n, n < count → Digest input Sf (off + n)) ∨
   ∃ (next : String) (done : Nat), Sf.tail = some next ∧ next ∈ targets ∧ done ≤ count ∧
     (∀ n, n < done → Digest input Sf (off + n)) ∧
     (done = 0 → count > 0) ∧
     EntryAt next (off + done) (count - done) input { Sf with halted := false, tail := none })

/-- A kernel of the library with its all-count theorem.  `thm` is what the generated proofs
provide for every count: from an entry state at node offset `off`, `steps off count` steps of the
fetch-execute loop reach an `Outcome`.  `targets` lists the kernels it may tail-call (static, from
the program's `tailcall`/`jcct` instructions; all of lower `rank`). -/
structure KernelThm (isa : Isa)
    (EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop)
    (Digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop) where
  name : String
  rank : Nat
  targets : List String
  rodata : Array (BitVec 64)
  prog : Array isa.Instr
  /-- the kernel's first instruction in `prog` (a call or a tail jump continues there) -/
  entry : Nat
  steps : Nat → Nat → Nat
  thm : ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryAt name off count input S →
    Outcome EntryAt Digest targets off count input S (isa.run rodata prog (steps off count) { S with pc := entry })

variable {isa : Isa}
  {EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop}
  {Digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop}

/-- The library: a table of kernels. -/
abbrev Table (isa : Isa) EntryAt Digest := List (KernelThm isa EntryAt Digest)

def Table.find (T : Table isa EntryAt Digest) (name : String) : Option (KernelThm isa EntryAt Digest) :=
  T.find? (·.name == name)

/-- The hand-over relation of a run: `Step T name off count S Sf` holds when running `name` from
`S` ends in `Sf` (no tail call) or in a tail call that the library continues. -/
inductive LibRun (T : Table isa EntryAt Digest) : String → Nat → Nat → State (BitVec 64) → State (BitVec 64) → Prop
  | stop (K : KernelThm isa EntryAt Digest) (hK : K ∈ T) (off count : Nat) (S : State (BitVec 64))
      (hnone : (isa.run K.rodata K.prog (K.steps off count) { S with pc := K.entry }).tail = none) :
      LibRun T K.name off count S (isa.run K.rodata K.prog (K.steps off count) { S with pc := K.entry })
  | tail (K : KernelThm isa EntryAt Digest) (hK : K ∈ T) (off count : Nat) (S : State (BitVec 64))
      (next : String) (done : Nat) (Sf' : State (BitVec 64))
      (htail : (isa.run K.rodata K.prog (K.steps off count) { S with pc := K.entry }).tail = some next)
      (hrest : LibRun T next (off + done) (count - done)
        { isa.run K.rodata K.prog (K.steps off count) { S with pc := K.entry } with halted := false, tail := none } Sf') :
      LibRun T K.name off count S Sf'

/-- The measure of a call: a hand-over finishes nodes or goes down in rank. -/
def measure (maxRank : Nat) (count rank : Nat) : Nat := count * (maxRank + 1) + rank

/-- Every tail-call target of a kernel is a kernel of the table of lower rank. -/
def RanksOk (T : Table isa EntryAt Digest) : Prop :=
  ∀ (K : KernelThm isa EntryAt Digest), K ∈ T → ∀ t ∈ K.targets, ∃ K' ∈ T, K'.name = t ∧ K'.rank < K.rank

/-- The shape of a table: name, rank and targets of each kernel. -/
def Table.shape (T : Table isa EntryAt Digest) : List (String × Nat × List String) :=
  T.map fun K => (K.name, K.rank, K.targets)

/-- The rank condition on a table shape (decidable). -/
def shapeOk (sh : List (String × Nat × List String)) : Bool :=
  sh.all fun (_, r, ts) => ts.all fun t => sh.any fun (n', r', _) => n' == t && decide (r' < r)

theorem ranksOk_of_shape (T : Table isa EntryAt Digest) (h : shapeOk T.shape = true) : RanksOk T := by
  intro K hK t ht
  simp only [shapeOk, Table.shape, List.all_map, List.any_map, List.all_eq_true, List.any_eq_true,
    Function.comp_def, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨K', hK', hn, hr⟩ := h K hK t ht
  exact ⟨K', hK', hn, hr⟩

/-- The digest predicate only looks at the output words of the node: a state that agrees with
another on those words has the same digests. -/
def DigestLocal (Digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop) : Prop :=
  ∀ input (S S' : State (BitVec 64)) (n : Nat),
    (∀ w : Int, 4 * (n : Int) ≤ w → w < 4 * (n : Int) + 4 → S'.mem rOutput w = S.mem rOutput w) →
    Digest input S n → Digest input S' n

/-- The conclusion of the library theorem for a kernel call. -/
def LibOk (T : Table isa EntryAt Digest) (K : KernelThm isa EntryAt Digest) (off count : Nat)
    (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  ∃ Sf, LibRun T K.name off count S Sf ∧ Sf.halted = true ∧ Sf.err = false ∧
    (∀ q : Int, q < 4 * off → Sf.mem rOutput q = S.mem rOutput q) ∧
    ∀ n, n < count → Digest input Sf (off + n)

/-- One kernel call, given the library theorem for every smaller measure. -/
theorem lib_step (T : Table isa EntryAt Digest) (maxRank : Nat)
    (hrank : ∀ K ∈ T, K.rank ≤ maxRank) (hranks : RanksOk T) (hloc : DigestLocal Digest)
    (μ : Nat)
    (ih : ∀ (K : KernelThm isa EntryAt Digest), K ∈ T → ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      measure maxRank count K.rank < μ → EntryAt K.name off count input S → LibOk T K off count input S)
    (K : KernelThm isa EntryAt Digest) (hK : K ∈ T) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hμ : measure maxRank count K.rank ≤ μ) (hS : EntryAt K.name off count input S) :
    LibOk T K off count input S := by
  have h := K.thm off count input S hS
  obtain ⟨hh, he, hpres, hout⟩ := h
  rcases hout with ⟨hnone, hd⟩ | ⟨next, done, htail, hmem, hdone, hd, hpos, hnext⟩
  · exact ⟨_, LibRun.stop K hK off count S hnone, hh, he, hpres, hd⟩
  · obtain ⟨K', hK', hname, hlt'⟩ := hranks K hK next hmem
    have hlt : done = 0 → K'.rank < K.rank := fun _ => hlt'
    subst hname
    have hμ' : measure maxRank (count - done) K'.rank < μ := by
      have hr := hrank K' hK'
      simp only [measure] at hμ ⊢
      rcases Nat.eq_zero_or_pos done with h0 | h0
      · subst h0
        have := hlt rfl
        simp only [Nat.sub_zero]
        omega
      · have h1 : count - done ≤ count - 1 := by omega
        have hc1 : count ≥ 1 := by omega
        have h4 : count * (maxRank + 1) = (count - 1) * (maxRank + 1) + (maxRank + 1) := by
          have := Nat.succ_mul (count - 1) (maxRank + 1)
          rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hc1] at this
          exact this
        have h3 := Nat.mul_le_mul_right (maxRank + 1) h1
        omega
    obtain ⟨Sf', hrun', hh', he', hpres', hd'⟩ := ih K' hK' (off + done) (count - done) input _ hμ' hnext
    refine ⟨Sf', LibRun.tail K hK off count S K'.name done Sf' htail hrun', hh', he', ?_, ?_⟩
    · intro q hq
      rw [hpres' q (by omega)]
      exact hpres q hq
    · intro n hn
      by_cases hlt : n < done
      · apply hloc input _ Sf' (off + n) ?_ (hd n hlt)
        intro w hw1 hw2
        exact hpres' w (by omega)
      · have := hd' (n - done) (by omega)
        rw [show off + done + (n - done) = off + n by omega] at this
        exact this

/-- **The library theorem**: from the entry state of any kernel of the table on `count` nodes,
the library run (the kernel and the kernels it hands over to) halts without a model fault with
every node's digest in place. -/
theorem lib_correct (T : Table isa EntryAt Digest) (maxRank : Nat)
    (hrank : ∀ K ∈ T, K.rank ≤ maxRank) (hranks : RanksOk T) (hloc : DigestLocal Digest) :
    ∀ (μ : Nat) (K : KernelThm isa EntryAt Digest), K ∈ T →
    ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      measure maxRank count K.rank ≤ μ → EntryAt K.name off count input S → LibOk T K off count input S := by
  intro μ
  induction μ with
  | zero =>
    intro K hK off count input S hμ hS
    exact lib_step T maxRank hrank hranks hloc 0 (fun K _ off count input S h _ => absurd h (Nat.not_lt_zero _))
      K hK off count input S hμ hS
  | succ μ ih =>
    intro K hK off count input S hμ hS
    exact lib_step T maxRank hrank hranks hloc (μ + 1)
      (fun K hK off count input S h hS => ih K hK off count input S (Nat.le_of_lt_succ h) hS)
      K hK off count input S hμ hS

/-- **The library for every runtime configuration.**  Two kernels read `.data` words that the
library's calibration sets at runtime (avx2_x4 `.Lsmall_tail_max`, avx2_x10 `.Lmid_tail_max`): the
constant images, hence the kernels' theorems, depend on a configuration `cfg`.  The library theorem
holds for every configuration as soon as each configuration's table satisfies the hypotheses (the
per-kernel theorems are proved per behaviour class of the configuration word: avx2_x4 {≤1, 2, ≥3},
avx2_x10 {≤4, 5, 6, 7, 8, ≥9}, every value of a class giving the same run). -/
theorem lib_correct_cfg {Cfg : Type} (T : Cfg → Table isa EntryAt Digest) (maxRank : Nat)
    (hrank : ∀ cfg, ∀ K ∈ T cfg, K.rank ≤ maxRank) (hranks : ∀ cfg, RanksOk (T cfg)) (hloc : DigestLocal Digest)
    (cfg : Cfg) (K : KernelThm isa EntryAt Digest) (hK : K ∈ T cfg)
    (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (hS : EntryAt K.name off count input S) :
    LibOk (T cfg) K off count input S :=
  lib_correct (T cfg) maxRank (hrank cfg) (hranks cfg) hloc _ K hK off count input S (Nat.le_refl _) hS

end Keccaktree.Asm.Library
