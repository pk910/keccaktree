import Keccaktree.Asm.LibX86
import Keccaktree.Asm.Alias
import Keccaktree.Asm.EntryCtlAl
import Keccaktree.Asm.LibTable
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# In-place hashing for an x86 kernel (`out == in`)

`inplace_lift` turns a kernel's all-count theorem for separate input and output buffers
(`LibX86.NormThm`) into the same statement for the aliased machine (`X86.runAl`: one storage, the
output pointer addressing it at the same offsets as the input pointer), under one condition on the
separate-region run: `AccessRun` — every input word it loads is at or above the current bound `B`
(above every output word stored so far), and it stores no input word.  The aliased run starts from
`T`; the separate-region run starts from `dupState T` (its output region a copy of the storage), so
`Entry` for `dupState T` is the calling convention of `keccaktree_hash(buf, buf, count)`.

The digests end up in the storage (`DigestAl`); the earlier storage words are kept; a tail call hands
the remaining nodes over in place, the storage above the final bound `Bf` still holding the message.
-/
namespace Keccaktree.Asm.LibAlias
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86

/-- What an in-place kernel call achieves (digests in the buffer, read through either view). -/
def OutcomeAl (targets : List String) (Bf : Int) (off count : Nat) (input : Int → BitVec 64) (T Tf : State (BitVec 64)) : Prop :=
  Tf.halted = true ∧ Tf.err = false ∧ Mirror Tf ∧
  (∀ q : Int, q < 4 * off → Tf.mem rOutput q = T.mem rOutput q) ∧
  (∀ q : Int, Bf ≤ q → Tf.mem rInput q = T.mem rInput q) ∧
  ((Tf.tail = none ∧ ∀ n, n < count → Digest input Tf (off + n)) ∨
   ∃ (next : String) (done : Nat), Tf.tail = some next ∧ next ∈ targets ∧ done ≤ count ∧
     (∀ n, n < done → Digest input Tf (off + n)) ∧
     EntryX86 next (off + done) (count - done) (fun q => Tf.mem rInput q)
       (dupState { Tf with halted := false, tail := none }))

theorem entry_transfer (off count : Nat) (input input' : Int → BitVec 64) (S S' : State (BitVec 64))
    (hE : Entry off count input S) (hS' : S' = { S with mem := S'.mem }) (hin : ∀ q, S'.mem rInput q = input' q) :
    Entry off count input' S' := by
  rw [hS']
  exact ⟨hE.ctrl, hE.ok, hE.rdx, hE.rsp, hE.rsi, hE.rdi, hin⟩

/-- **The in-place lifting.** -/
theorem inplace_lift (rodata : Array (BitVec 64)) (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (targets : List String) (h : NormThm rodata prog entry steps targets)
    (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64)) (hm : Mirror T)
    (hE : Entry off count input (dupState T)) (hb : 64 * (off + count) ≤ 2 ^ 54) (hpc : T.pc = entry)
    (B0 Bf : Int) (hacc : AccessRun rodata prog (steps off count) B0 Bf (dupState T)) :
    OutcomeAl targets Bf off count input T (runAl rodata prog (steps off count) T) := by
  have hO := h off count input (dupState T) hE hb hpc
  obtain ⟨hS, hC, hIn⟩ := sim_run rodata prog _ B0 Bf (dupState T) T hacc (sim_dup T hm) (clean_dup T B0)
  generalize hSf : X86.isa.run rodata prog (steps off count) (dupState T) = Sf at hO hS hC hIn
  generalize hTf : runAl rodata prog (steps off count) T = Tf at hS
  obtain ⟨hh, he, hpre, hout⟩ := hO
  have hmIn : ∀ q, Tf.mem rInput q = Sf.mem rOutput q := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmOut : ∀ q, Tf.mem rOutput q = Sf.mem rOutput q := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdig : ∀ n, Digest input Sf n → Digest input Tf n := by
    intro n hd w i hw hi
    rw [hmOut]; exact hd w i hw hi
  refine ⟨hS.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hh, hS.2.2.2.2.2.2.2.2.2.2.2.1.trans he,
    fun q => (hmOut q).trans (hmIn q).symm, ?_, ?_, ?_⟩
  · intro q hq
    rw [hmOut, hpre q hq]; simp only [dupState, ↓reduceIte]; exact (hm q).symm
  · intro q hq
    rw [hmIn, hC q hq, hIn q]; simp [dupState, show rInput ≠ rOutput by decide]
  · rcases hout with ⟨ht, hd⟩ | ⟨next, done, ht, hmem, hdone, hd, hnext⟩
    · exact Or.inl ⟨hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans ht, fun n hn => hdig _ (hd n hn)⟩
    · refine Or.inr ⟨next, done, hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans ht, hmem, hdone, fun n hn => hdig _ (hd n hn), ?_⟩
      obtain ⟨hEn, hbn⟩ := hnext
      refine ⟨entry_transfer _ _ input _ _ _ hEn ?_ (fun q => ?_), hbn⟩
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -⟩ := hS
        cases Tf; cases Sf
        simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
        subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
        rfl
      · simp only [normCtl, ovr, dupState, show rInput ≠ rOutput by decide, ↓reduceIte]

/-! ## In-place kernels of the library (any control state at entry) -/

/-- **The in-place x86 calling convention** `keccaktree_hash(buf + 32·off, buf + 64·off, count)` after
`off` nodes are done, entered by a call or by a tail call: one buffer (`Mirror`: both views agree),
the separate-region view at its entry with *any* flags, mask registers and vector length (`normCtl`),
and the message from word `8·off` on. -/
def EntryAlX86 (name : String) (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64)) : Prop :=
  Mirror T ∧ Entry off count (fun q => T.mem rInput q) (normCtl (dupState T)) ∧
  (∀ q : Int, 8 * (off : Int) ≤ q → T.mem rInput q = input q) ∧ 64 * (off + count) ≤ 2 ^ 54

/-- **What a kernel's in-place proof provides**, on the separate-region run from a normalised entry
state (as `NormThm`): the access condition from the bound `4·off` (`AccessRun`: input words loaded
only at or above the current bound, no input word stored) up to some final bound `Bf`, and, at a hand-over
of the first `done` nodes, `Bf ≤ 8·(off + done)` (the message words the next kernel reads are
still in the buffer). -/
def AccessThm (rodata : Array (BitVec 64)) (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    Entry off count input S → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    ∃ Bf : Int, AccessRun rodata prog (steps off count) (4 * (off : Int)) Bf S ∧
      ∀ (next : String) (done : Nat), (X86.isa.run rodata prog (steps off count) S).tail = some next →
        Entry (off + done) (count - done) input
          (normCtl { X86.isa.run rodata prog (steps off count) S with halted := false, tail := none }) →
        Bf ≤ 8 * ((off + done : Nat) : Int)

/-- Digests are those of the message words of the node. -/
theorem digest_input (input input' : Int → BitVec 64) (S : State (BitVec 64)) (n : Nat)
    (h : ∀ w : Nat, input' (Int.ofNat (8 * n + w)) = input (Int.ofNat (8 * n + w)))
    (hd : Digest input' S n) : Digest input S n := by
  have hw : nodeWords input' n = nodeWords input n := by
    funext w; exact h w
  intro w i hw' hi
  have := hd w i hw' hi
  rw [hw] at this; exact this

/-- **The in-place lifting, as a library outcome** (normalised entry): a kernel's all-count theorem
(`NormThm`) and its access theorem (`AccessThm`) give the outcome of the aliased run, with the
hand-over in place (`EntryAlX86`). -/
theorem inplace_outcome (rodata : Array (BitVec 64)) (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (targets : List String) (h : NormThm rodata prog entry steps targets) (ha : AccessThm rodata prog entry steps)
    (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64)) (hm : Mirror T)
    (hE : Entry off count (fun q => T.mem rInput q) (dupState T)) (hb : 64 * (off + count) ≤ 2 ^ 54)
    (hpc : T.pc = entry) (hin : ∀ q : Int, 8 * (off : Int) ≤ q → T.mem rInput q = input q) :
    Library.Outcome EntryAlX86 Digest targets off count input T (X86.isaAl.run rodata prog (steps off count) T) := by
  obtain ⟨Bf, hacc, hBf⟩ := ha off count _ (dupState T) hE hb hpc
  have hO := h off count _ (dupState T) hE hb hpc
  obtain ⟨hS, hC, hIn⟩ := sim_run rodata prog _ _ Bf (dupState T) T hacc (sim_dup T hm) (clean_dup T _)
  rw [← runAl_eq]
  generalize hSf : X86.isa.run rodata prog (steps off count) (dupState T) = Sf at hO hS hC hIn hBf
  generalize hTf : runAl rodata prog (steps off count) T = Tf at hS
  obtain ⟨hh, he, hpre, hout⟩ := hO
  have hmIn : ∀ q, Tf.mem rInput q = Sf.mem rOutput q := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmOut : ∀ q, Tf.mem rOutput q = Sf.mem rOutput q := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdig : ∀ n, off ≤ n → Digest (fun q => T.mem rInput q) Sf n → Digest input Tf n := by
    intro n hn hd
    apply digest_input _ _ _ _ (fun w => hin _ (by simp only [Int.ofNat_eq_coe]; omega))
    intro w i hw hi; rw [hmOut]; exact hd w i hw hi
  refine ⟨hS.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hh, hS.2.2.2.2.2.2.2.2.2.2.2.1.trans he, ?_, ?_⟩
  · intro q hq
    rw [hmOut, hpre q hq]; simp only [dupState, ↓reduceIte]; exact (hm q).symm
  · rcases hout with ⟨ht, hd⟩ | ⟨next, done, ht, hmem, hdone, hd, hnext⟩
    · exact Or.inl ⟨hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans ht, fun n hn => hdig _ (by omega) (hd n hn)⟩
    · refine Or.inr ⟨next, done, hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans ht, hmem, hdone,
        fun n hn => hdig _ (by omega) (hd n hn), ?_⟩
      obtain ⟨hEn, hbn⟩ := hnext
      have hB := hBf next done ht hEn
      refine ⟨fun q => by show Tf.mem rOutput q = Tf.mem rInput q; rw [hmOut, hmIn], ?_, fun q hq => ?_, hbn⟩
      · refine entry_transfer _ _ _ _ _ _ hEn ?_ (fun q => rfl)
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -⟩ := hS
        cases Tf; cases Sf
        simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
        subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
        rfl
      · show Tf.mem rInput q = input q
        rw [hmIn, hC q (by omega), hIn q]
        simp only [dupState, show rInput ≠ rOutput by decide, ↓reduceIte]
        exact hin q (by omega)

/-- The outcome is insensitive to leftover control components of the final state. -/
theorem outcome_ovr_al (targets : List String) (off count : Nat) (input : Int → BitVec 64) (S S' X : State (BitVec 64))
    (D : Dom) (c : Ctl) (hmem : S'.mem = S.mem)
    (h : Library.Outcome EntryAlX86 Digest targets off count input S X) :
    Library.Outcome EntryAlX86 Digest targets off count input S' (ovr D c X) := by
  obtain ⟨hh, he, hp, hout⟩ := h
  refine ⟨hh, he, fun q hq => (hp q hq).trans (by rw [hmem]), ?_⟩
  rcases hout with ⟨ht, hd⟩ | ⟨next, done, ht, hmemb, hdone, hd, hnext⟩
  · exact Or.inl ⟨ht, hd⟩
  · refine Or.inr ⟨next, done, ht, hmemb, hdone, hd, ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hnext
    refine ⟨h1, ?_, h3, h4⟩
    have e : normCtl (dupState ({ ovr D c X with halted := false, tail := none } : State (BitVec 64))) =
        normCtl (dupState ({ X with halted := false, tail := none } : State (BitVec 64))) :=
      normCtl_ovr D c (dupState ({ X with halted := false, tail := none } : State (BitVec 64)))
    rw [e]; exact h2

/-- **An x86 kernel of the in-place library** (entered by a call or a tail call: any flags, masks and
vector length), from its normalised all-count theorem (`NormThm`), its access theorem (`AccessThm`),
and the two program checks of `LibX86.mkKernel` (flag-writing entry prefix, no other instruction
touching the control components), on the aliased machine through `run_normCtl_al`. -/
def mkKernelAl (name : String) (rank : Nat) (targets : List String) (rodata : Array (BitVec 64))
    (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat) (m : Nat)
    (hpre : prefixOk prog entry 1048576 m = true)
    (hstatic : (prog.all fun i => ctlOk Dom1 i && ctlAfter Dom1 i == Dom1) = true)
    (hm : ∀ off count, m ≤ steps off count)
    (h : NormThm rodata prog entry steps targets) (ha : AccessThm rodata prog entry steps) :
    Library.KernelThm X86.isaAl EntryAlX86 Digest where
  name := name
  rank := rank
  targets := targets
  rodata := rodata
  prog := prog
  entry := entry
  steps := steps
  thm := fun off count input T hT => by
    obtain ⟨hm', hE, hin, hb⟩ := hT
    have h0 := inplace_outcome rodata prog entry steps targets h ha off count input
      (normCtl { T with pc := entry }) hm' (hE.with_pc entry) hb rfl hin
    have hrun := run_normCtl_al rodata prog m 1048576 (steps off count) { T with pc := entry } hpre hstatic
      (hm off count) hE.ok.2.1 hE.rsp (by decide) h0.2.1
    rw [hrun]
    exact outcome_ovr_al targets off count input _ _ _ _ _ rfl h0

/-- **The in-place x86 library** for a table of in-place kernels of the library's shape (as
`LibTable.lib_x86`). -/
theorem lib_inplace_x86 {Cfg : Type} (T : Cfg → Library.Table X86.isaAl EntryAlX86 Digest)
    (hT : ∀ cfg, (T cfg).shape = LibTable.x86Shape) (cfg : Cfg) :
    ∀ K ∈ T cfg, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryAlX86 K.name off count input S → Library.LibOk (T cfg) K off count input S :=
  LibTable.lib_of_shape (T cfg) LibTable.x86Shape (hT cfg) LibTable.x86Shape_ok

end Keccaktree.Asm.LibAlias
