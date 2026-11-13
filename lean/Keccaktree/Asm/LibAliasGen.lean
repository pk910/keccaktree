import Keccaktree.Asm.AliasIsa
import Keccaktree.Asm.LibTable
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The in-place library for any instruction set (`AlIsa`)

For an instruction set with footprints (`AlIsa`, the AArch64 and RISC-V instances in
`ArmAliasTrace.lean`/`RiscvAliasTrace.lean`) and its fresh-call entry predicate `E0` (`LibTable.EntryA`,
`LibTable.EntryR`, `LibX86.Entry`):

* `EntryN E0`: the library's calling convention (any control state: `E0` of `normCtl S`) — for the
  three instruction sets this is `EntryArm`, `EntryRv`, `EntryX86`;
* **`EntryAlG E0`**: the in-place calling convention (one buffer; the separate-region view at its entry
  with any control state; the message from word `8·off` on);
* **`AccessThmG`**: what a kernel's in-place proof provides (the access condition of the
  separate-region run from a normalised entry; at a hand-over of `done` nodes the final bound is at most
  `8·(off+done)`);
* **`CtlThm`**: the run from any control state is the normalised run with some control components
  overridden, at every step count (`ctlThm_of` below, from a static annotation, AArch64/RISC-V);
* **`mkKernelAlG`**: a kernel of the separate-region library (`KernelThm I.isa (EntryN E0)`, e.g. from
  `mkKernelArm`/`mkKernelRv`), its `AccessThmG` and its `CtlThm` give a kernel of the in-place library
  (`KernelThm I.isaAl (EntryAlG E0)`).  No run lemma of the aliased machine is needed: the aliased run
  from any control state follows the separate-region run from the same control state (`sim_run`), whose
  access condition is that of the normalised run (`accessRun_ovr`) and whose outcome is the kernel's.
-/
namespace Keccaktree.Asm.LibAliasGen
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86

variable (I : AlIsa) (E0 : Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop)

/-- The library calling convention from a fresh-call entry predicate: any control state. -/
def EntryN (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  E0 off count input (normCtl S) ∧ 64 * (off + count) ≤ 2 ^ 54

/-- **The in-place calling convention** (`keccaktree_hash(buf + 32·off, buf + 64·off, count)` after `off`
nodes, by a call or a tail call). -/
def EntryAlG (name : String) (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64)) : Prop :=
  Mirror T ∧ E0 off count (fun q => T.mem rInput q) (normCtl (dupState T)) ∧
  (∀ q : Int, 8 * (off : Int) ≤ q → T.mem rInput q = input q) ∧ 64 * (off + count) ≤ 2 ^ 54

/-- **What a kernel's in-place proof provides** (separate-region run from a normalised entry state). -/
def AccessThmG (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (entry : Nat) (steps : Nat → Nat → Nat) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    E0 off count input S → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    ∃ Bf : Int, I.AccessRun rodata prog (steps off count) (4 * (off : Int)) Bf S ∧
      ∀ (next : String) (done : Nat), done ≤ count → (I.isa.run rodata prog (steps off count) S).tail = some next →
        E0 (off + done) (count - done) input
          (normCtl { I.isa.run rodata prog (steps off count) S with halted := false, tail := none }) →
        Bf ≤ 8 * ((off + done : Nat) : Int)

/-- **The run from any control state** is the normalised run with some control components overridden,
at every step count up to the kernel's (given that the normalised run does not fail). -/
def CtlThm (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (entry : Nat) (steps : Nat → Nat → Nat) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    E0 off count input (normCtl S) → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    (I.isa.run rodata prog (steps off count) (normCtl S)).err = false →
    ∀ k, k ≤ steps off count → ∃ (D : Dom) (c : Ctl),
      I.isa.run rodata prog k S = ovr D c (I.isa.run rodata prog k (normCtl S)) ∧
      I.fpOk D (prog.getD (I.isa.run rodata prog k (normCtl S)).pc I.isa.nop) = true

/-- The entry predicate looks at memory only through the input region (the message). -/
def MemInput : Prop :=
  ∀ (off count : Nat) (input input' : Int → BitVec 64) (S S' : State (BitVec 64)), E0 off count input S →
    S' = { S with mem := S'.mem } → (∀ q, S'.mem rInput q = input' q) → E0 off count input' S'

/-- The entry predicate does not constrain `pc` (the library sets it to the kernel's entry). -/
def PcFree : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (p : Nat),
    E0 off count input S → E0 off count input { S with pc := p }

/-- Digests are those of the message words of the node. -/
theorem digest_input (input input' : Int → BitVec 64) (S : State (BitVec 64)) (n : Nat)
    (h : ∀ w : Nat, input' (Int.ofNat (8 * n + w)) = input (Int.ofNat (8 * n + w)))
    (hd : Digest input' S n) : Digest input S n := by
  have hw : nodeWords input' n = nodeWords input n := by
    funext w; exact h w
  intro w i hw' hi
  have := hd w i hw' hi
  rw [hw] at this; exact this

theorem normCtl_normCtl (S : State (BitVec 64)) : normCtl (normCtl S) = normCtl S := normCtl_ovr _ _ _

theorem run_err_true (J : Isa) (rodata : Array (BitVec 64)) (prog : Array J.Instr) :
    ∀ (n : Nat) (s : State (BitVec 64)), s.err = true → (J.run rodata prog n s).err = true
  | 0, s, h => h
  | n + 1, s, h => by
    simp only [Isa.run]
    split
    · exact h
    · exact run_err_true J rodata prog n _ (J.err_exec rodata _ s h)

theorem run_err_le (J : Isa) (rodata : Array (BitVec 64)) (prog : Array J.Instr) (s : State (BitVec 64))
    (k n : Nat) (hk : k ≤ n) (h : (J.run rodata prog n s).err = false) : (J.run rodata prog k s).err = false := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [Isa.run_add] at h
  cases hc : (J.run rodata prog k s).err
  · rfl
  · rw [run_err_true J rodata prog j _ hc] at h; exact absurd h (by decide)

/-- **The aliased outcome from the separate-region one**: if the separate-region run from `dupState T`
(any control state) satisfies the access condition from `4·off` and reaches the library outcome for
the buffer as message, the aliased run from `T` reaches the in-place outcome for `input` (which the
buffer holds from word `8·off` on). -/
theorem outcome_al (hE0 : MemInput E0) (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (n : Nat)
    (targets : List String) (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64)) (hm : Mirror T)
    (hin : ∀ q : Int, 8 * (off : Int) ≤ q → T.mem rInput q = input q) (Bf : Int)
    (hacc : I.AccessRun rodata prog n (4 * (off : Int)) Bf (dupState T))
    (hO : Library.Outcome (EntryN E0) Digest targets off count (fun q => T.mem rInput q) (dupState T)
      (I.isa.run rodata prog n (dupState T)))
    (hBf : ∀ (next : String) (done : Nat), done ≤ count → (I.isa.run rodata prog n (dupState T)).tail = some next →
      E0 (off + done) (count - done) (fun q => T.mem rInput q)
        (normCtl { I.isa.run rodata prog n (dupState T) with halted := false, tail := none }) →
      Bf ≤ 8 * ((off + done : Nat) : Int)) :
    Library.Outcome (EntryAlG E0) Digest targets off count input T (I.isaAl.run rodata prog n T) := by
  obtain ⟨hS, hC, hIn⟩ := I.sim_run rodata prog _ _ Bf (dupState T) T hacc (sim_dup T hm) (clean_dup T _)
  generalize hSf : I.isa.run rodata prog n (dupState T) = Sf at hO hS hC hIn hBf
  generalize hTf : I.isaAl.run rodata prog n T = Tf at hS
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
      have hB := hBf next done hdone ht hEn
      refine ⟨fun q => by show Tf.mem rOutput q = Tf.mem rInput q; rw [hmOut, hmIn], ?_, fun q hq => ?_, hbn⟩
      · refine hE0 _ _ _ _ _ _ hEn ?_ (fun q => rfl)
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -⟩ := hS
        cases Tf; cases Sf
        simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
        subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
        rfl
      · show Tf.mem rInput q = input q
        rw [hmIn, hC q (by omega), hIn q]
        simp only [dupState, show rInput ≠ rOutput by decide, ↓reduceIte]
        exact hin q (by omega)

/-- **A kernel of the in-place library** from a kernel of the separate-region library (any control
state at entry), its access theorem and its control theorem. -/
def mkKernelAlG (hE0 : MemInput E0) (hpc : PcFree E0) (K : Library.KernelThm I.isa (EntryN E0) Digest)
    (ha : AccessThmG I E0 K.rodata K.prog K.entry K.steps) (hctl : CtlThm I E0 K.rodata K.prog K.entry K.steps) :
    Library.KernelThm I.isaAl (EntryAlG E0) Digest where
  name := K.name
  rank := K.rank
  targets := K.targets
  rodata := K.rodata
  prog := K.prog
  entry := K.entry
  steps := K.steps
  thm := fun off count input T hT => by
    obtain ⟨hm, hE, hin, hb⟩ := hT
    -- the separate-region run from the same (any) control state: the kernel's outcome
    have hO := K.thm off count (fun q => T.mem rInput q) (dupState T) ⟨hE, hb⟩
    -- the normalised run: no model fault
    have hEn : E0 off count (fun q => T.mem rInput q) (normCtl (normCtl (dupState T))) := by
      rw [normCtl_normCtl]; exact hE
    have hOn := K.thm off count (fun q => T.mem rInput q) (normCtl (dupState T)) ⟨hEn, hb⟩
    -- the access condition of the normalised run
    obtain ⟨Bf, hacc, hBf⟩ := ha off count _ (normCtl (dupState { T with pc := K.entry }))
      (hpc _ _ _ _ _ hE) hb rfl
    -- the run from the actual control state commutes with the normalisation at every step
    have hk := hctl off count _ (dupState { T with pc := K.entry }) (hpc _ _ _ _ _ hE) hb rfl hOn.2.1
    have hacc' : I.AccessRun K.rodata K.prog (K.steps off count) (4 * (off : Int)) Bf (dupState { T with pc := K.entry }) :=
      I.accessRun_ovr K.rodata K.prog _ _ _ _ _ hk hacc
    have hBf' : ∀ (next : String) (done : Nat), done ≤ count →
        (I.isa.run K.rodata K.prog (K.steps off count) (dupState { T with pc := K.entry })).tail = some next →
        E0 (off + done) (count - done) (fun q => T.mem rInput q)
          (normCtl { I.isa.run K.rodata K.prog (K.steps off count) (dupState { T with pc := K.entry }) with
            halted := false, tail := none }) →
        Bf ≤ 8 * ((off + done : Nat) : Int) := by
      intro next done hdn ht hE'
      obtain ⟨D, c, hDc, -⟩ := hk _ (Nat.le_refl _)
      rw [hDc] at ht hE'
      have e : normCtl ({ ovr D c (I.isa.run K.rodata K.prog (K.steps off count) (normCtl (dupState { T with pc := K.entry })))
          with halted := false, tail := none } : State (BitVec 64)) =
          normCtl { I.isa.run K.rodata K.prog (K.steps off count) (normCtl (dupState { T with pc := K.entry }))
            with halted := false, tail := none } :=
        normCtl_ovr D c ({ I.isa.run K.rodata K.prog (K.steps off count) (normCtl (dupState { T with pc := K.entry }))
          with halted := false, tail := none } : State (BitVec 64))
      rw [e] at hE'
      exact hBf next done hdn ht hE'
    exact outcome_al I E0 hE0 K.rodata K.prog (K.steps off count) K.targets off count input { T with pc := K.entry }
      hm hin Bf hacc' hO hBf'

/-- `CtlThm` from a run lemma that commutes the override (for every step count) from the entry, where
every control component is dirty (`AnnOk`-style annotations of AArch64/RISC-V: `run_ovr_ann`). -/
theorem ctlThm_of (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (ann : Nat → Dom) (hentry : ann entry = Dom.all)
    (hfp : ∀ p, I.fpOk (ann p) (prog.getD p I.isa.nop) = true)
    (hrun : ∀ (n : Nat) (s : State (BitVec 64)) (c : Ctl), (I.isa.run rodata prog n s).err = false →
      ∃ c' : Ctl, I.isa.run rodata prog n (ovr (ann s.pc) c s) = ovr (ann (I.isa.run rodata prog n s).pc) c' (I.isa.run rodata prog n s)) :
    CtlThm I E0 rodata prog entry steps := by
  intro off count input S hE hb hpc herr k hk
  have hek := run_err_le I.isa rodata prog (normCtl S) k _ hk herr
  obtain ⟨c', hc'⟩ := hrun k (normCtl S) (Ctl.of S) hek
  have h1 : ovr (ann (normCtl S).pc) (Ctl.of S) (normCtl S) = S := by
    show ovr (ann S.pc) _ (normCtl S) = S
    rw [hpc, hentry, ovr_normCtl]
  rw [h1] at hc'
  exact ⟨_, c', hc', hfp _⟩

/-- `CtlThm` from a run lemma that needs an invariant `P` of the normalised entry state (e.g. agent
x86b's `run_ovr_annJ` with its call-depth invariant `DepthInv`). -/
theorem ctlThm_of_pred (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (ann : Nat → Dom) (hentry : ann entry = Dom.all) (P : State (BitVec 64) → Prop)
    (hP : ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)), E0 off count input (normCtl S) →
      S.pc = entry → P (normCtl S))
    (hfp : ∀ p, I.fpOk (ann p) (prog.getD p I.isa.nop) = true)
    (hrun : ∀ (n : Nat) (s : State (BitVec 64)) (c : Ctl), P s → (I.isa.run rodata prog n s).err = false →
      ∃ c' : Ctl, I.isa.run rodata prog n (ovr (ann s.pc) c s) = ovr (ann (I.isa.run rodata prog n s).pc) c' (I.isa.run rodata prog n s)) :
    CtlThm I E0 rodata prog entry steps := by
  intro off count input S hE hb hpc herr k hk
  have hek := run_err_le I.isa rodata prog (normCtl S) k _ hk herr
  obtain ⟨c', hc'⟩ := hrun k (normCtl S) (Ctl.of S) (hP off count input S hE hpc) hek
  have h1 : ovr (ann (normCtl S).pc) (Ctl.of S) (normCtl S) = S := by
    show ovr (ann S.pc) _ (normCtl S) = S
    rw [hpc, hentry, ovr_normCtl]
  rw [h1] at hc'
  exact ⟨_, c', hc', hfp _⟩

end Keccaktree.Asm.LibAliasGen
