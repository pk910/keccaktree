import Keccaktree.Asm.AliasCells
import Keccaktree.Asm.Iter
import Keccaktree.Asm.EntryCtl
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# In-place hashing for any relocatable instruction set with footprints

The x86 development (`Alias.lean`, `AliasTrace.lean`) uses, of the instruction set, only

* its step function (an `Isa`, relocatable: `Isa.Relocatable`),
* the cells a step reads and writes (`reads`/`writes`), the write cells not depending on memory or on
  the control components,
* memory locality (`exec_local`), and
* how the cells transfer to an evaluated state (`cells_map`) and to a relocated state (`cells_reloc`).

`AlIsa` packages these.  For every such instruction set (AArch64: `ArmAliasTrace.lean`, RISC-V:
`RiscvAliasTrace.lean`) this file gives, once:

* the aliased machine as an `Isa` (`isaAl`: one buffer for input and output);
* the access condition (`AccessRun`) and **the simulation** (`sim_run`): the aliased run follows the
  separate-region run as long as no input word is loaded below the current bound;
* the condition along a relocated symbolic path (`path_access`), for a certified slice
  (`sliceAccess`) and for a whole generated segment (`chain_access`, from the slices' footprint
  summaries, as `X86.chain_access`); sequencing (`accessRun_add`, `accessRun_step`);
* `accessRun_ovr`: the condition is insensitive to the control components (flags, masks, vector
  length) — a run from any control state that commutes with the override at every step satisfies
  the condition of the normalised run.
-/
namespace Keccaktree.Asm
open X86

/-- An instruction set for the in-place development (see the file header). -/
structure AlIsa where
  isa : Isa
  R : isa.Relocatable
  reads : {α : Type} → [LaneOps α] → State α → isa.Instr → List (Region × Int)
  writes : {α : Type} → [LaneOps α] → State α → isa.Instr → List (Region × Int)
  writes_wm : ∀ {α : Type} [LaneOps α] (s : State α) (m' : Region → Int → α) (i : isa.Instr),
    writes ({ s with mem := m' } : State α) i = writes s i
  /-- When an instruction's footprint does not depend on the dirty control components `D` (always on
  x86/AArch64; on RISC-V unless a vector instruction runs with `vl` dirty). -/
  fpOk : Dom → isa.Instr → Bool
  reads_ovr : ∀ {α : Type} [LaneOps α] (D : Dom) (c : Ctl) (s : State α) (i : isa.Instr),
    fpOk D i = true → reads (ovr D c s) i = reads s i
  writes_ovr : ∀ {α : Type} [LaneOps α] (D : Dom) (c : Ctl) (s : State α) (i : isa.Instr),
    fpOk D i = true → writes (ovr D c s) i = writes s i
  exec_local : ∀ (rodata : Array (BitVec 64)) (m' : Region → Int → BitVec 64) (i : isa.Instr) (s : State (BitVec 64)),
    s.halted = false → (isa.exec rodata i s).err = false → Agree m' (reads s i) s →
      isa.exec rodata i ({ s with mem := m' } : State (BitVec 64)) = rebase (writes s i) m' (isa.exec rodata i s)
  cells_map : ∀ {α β : Type} [LaneOps α] [LaneOps β] (f : α → β), IsHom f →
    ∀ (rodata : Array (BitVec 64)) (i : isa.Instr) (X : State α), X.halted = false → (isa.exec rodata i X).err = false →
      reads (mapState f X) i = reads X i ∧ writes (mapState f X) i = writes X i
  cells_reloc : ∀ (ρ : Reloc), ρ.ok → ∀ (rodata : Array (BitVec 64)) (i : isa.Instr) (X : State E),
    X.halted = false → (isa.exec rodata i X).err = false → (∀ e ∈ R.decodes rodata i X, E.relocOk ρ e) →
      reads (relocState ρ X) i = (reads X i).map (shiftCell ρ) ∧
      writes (relocState ρ X) i = (writes X i).map (shiftCell ρ)

namespace AlIsa
variable (I : AlIsa)

/-! ## The aliased machine -/

/-- The buffer after an aliased step that stored the cells `W` (result memory `m` of the step on the
joined view): a word stored through the output pointer, else the input region's word, in both
regions. -/
def alMem {α : Type} (W : List (Region × Int)) (m : Region → Int → α) : Region → Int → α :=
  fun r q => if r = rInput ∨ r = rOutput then (if (rOutput, q) ∈ W then m rOutput q else m rInput q) else m r q

/-- **One step of the aliased machine** (`keccaktree_hash(buf, buf, n)`). -/
def execAl {α : Type} [LaneOps α] (rodata : Array (BitVec 64)) (i : I.isa.Instr) (t : State α) : State α :=
  if t.halted then t else
  { I.isa.exec rodata i ({ t with mem := joinMem t.mem } : State α) with
    mem := alMem (I.writes ({ t with mem := joinMem t.mem } : State α) i)
      (I.isa.exec rodata i ({ t with mem := joinMem t.mem } : State α)).mem }

theorem execAl_eq {α : Type} [LaneOps α] (rodata : Array (BitVec 64)) (i : I.isa.Instr) (t : State α)
    (hh : t.halted = false) :
    I.execAl rodata i t = { I.isa.exec rodata i ({ t with mem := joinMem t.mem } : State α) with
      mem := alMem (I.writes ({ t with mem := joinMem t.mem } : State α) i)
        (I.isa.exec rodata i ({ t with mem := joinMem t.mem } : State α)).mem } := by
  simp only [execAl, hh, Bool.false_eq_true, ↓reduceIte]

theorem execAl_map {α β : Type} [LaneOps α] [LaneOps β] {f : α → β} (hf : IsHom f) (rodata : Array (BitVec 64))
    (i : I.isa.Instr) (t : State α) (hne : (I.execAl rodata i t).err = false) :
    I.execAl rodata i (mapState f t) = mapState f (I.execAl rodata i t) := by
  cases hh : t.halted
  · have hh' : (mapState f t).halted = false := hh
    rw [I.execAl_eq rodata i t hh] at hne
    have hne' : (I.isa.exec rodata i ({ t with mem := joinMem t.mem } : State α)).err = false := hne
    have hv : ({ t with mem := joinMem t.mem } : State α).halted = false := hh
    rw [I.execAl_eq rodata i _ hh', I.execAl_eq rodata i _ hh, view_map, I.isa.exec_map f hf rodata i _ hne',
      (I.cells_map f hf rodata i _ hv hne').2]
    have key : ∀ (W : List (Region × Int)) (X : State α),
        alMem W (mapState f X).mem = fun r q => f (alMem W X.mem r q) := by
      intro W X; funext r q
      by_cases h1 : r = rInput ∨ r = rOutput <;> by_cases h2 : (rOutput, q) ∈ W <;> simp [alMem, mapState, h1, h2]
    rw [key]
    rfl
  · rw [show I.execAl rodata i t = t by simp [execAl, hh],
      show I.execAl rodata i (mapState f t) = mapState f t by simp [execAl, hh, mapState]]

theorem err_execAl {α : Type} [LaneOps α] (rodata : Array (BitVec 64)) (i : I.isa.Instr) (t : State α)
    (h : t.err = true) : (I.execAl rodata i t).err = true := by
  unfold execAl
  split
  · exact h
  · exact I.isa.err_exec rodata i _ h

/-- **The aliased machine as an instruction set** (the library theorem applies to it). -/
@[reducible] def isaAl : Isa where
  Instr := I.isa.Instr
  nop := I.isa.nop
  exec := I.execAl
  exec_map := fun f hf rodata i st hne => I.execAl_map hf rodata i st hne
  err_exec := fun rodata i st h => I.err_execAl rodata i st h

/-! ## The access condition and the simulation (as `AliasGen.lean`, on `isa.run`) -/

theorem exec_frame (rodata : Array (BitVec 64)) (i : I.isa.Instr) (s : State (BitVec 64)) (hh : s.halted = false)
    (hne : (I.isa.exec rodata i s).err = false) (r : Region) (q : Int) (hw : (r, q) ∉ I.writes s i) :
    (I.isa.exec rodata i s).mem r q = s.mem r q := by
  have h := I.exec_local rodata s.mem i s hh hne (fun _ _ => rfl)
  have h2 : ({ s with mem := s.mem } : State (BitVec 64)) = s := rfl
  rw [h2] at h
  rw [h]; simp only [rebase, hw, ↓reduceIte]

def AccessOk (B : Int) (s : State (BitVec 64)) (i : I.isa.Instr) : Prop :=
  (∀ c ∈ I.reads s i, c.1 = rInput → B ≤ c.2) ∧ (∀ c ∈ I.writes s i, c.1 ≠ rInput)

def bumpB (B : Int) (s : State (BitVec 64)) (i : I.isa.Instr) : Int :=
  (I.writes s i).foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) B

/-- The access condition along a separate-region run (as `X86.AccessRun`). -/
def AccessRun (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) : Nat → Int → Int → State (BitVec 64) → Prop
  | 0, B, Bf, _ => B ≤ Bf
  | n + 1, B, Bf, s => if s.halted then B ≤ Bf else
      ((I.isa.exec rodata (prog.getD s.pc I.isa.nop) s).err = false ∧ I.AccessOk B s (prog.getD s.pc I.isa.nop) ∧
        AccessRun rodata prog n (I.bumpB B s (prog.getD s.pc I.isa.nop)) Bf (I.isa.exec rodata (prog.getD s.pc I.isa.nop) s))

set_option maxHeartbeats 4000000 in
theorem sim_step (rodata : Array (BitVec 64)) (i : I.isa.Instr) (s t : State (BitVec 64)) (B : Int)
    (hS : Sim s t) (hC : Clean B s) (hA : I.AccessOk B s i) (hh : s.halted = false)
    (hne : (I.isa.exec rodata i s).err = false) :
    Sim (I.isa.exec rodata i s) (I.execAl rodata i t) ∧ Clean (I.bumpB B s i) (I.isa.exec rodata i s) := by
  have hth : t.halted = false := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hh
  have hmIn := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmOt := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hag : Agree (joinMem t.mem) (I.reads s i) s := by
    rintro ⟨r, q⟩ hc
    simp only [joinMem]
    by_cases h2 : r = rOutput
    · subst h2; simp only [↓reduceIte]; exact hmIn q
    · simp only [h2, ↓reduceIte]
      by_cases h1 : r = rInput
      · subst h1; rw [hmIn q]; exact hC q (hA.1 _ hc rfl)
      · exact hmOt r q h1 h2
  have hloc := I.exec_local rodata (joinMem t.mem) i s hh hne hag
  have hfr := I.exec_frame rodata i s hh hne
  have hj : ({ t with mem := joinMem t.mem } : State (BitVec 64)) = { s with mem := joinMem t.mem } := joined_eq s t hS
  rw [I.execAl_eq rodata i t hth, hj, hloc, I.writes_wm s (joinMem t.mem) i]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -⟩ := hS
  have hst : ∀ q, (if (rOutput, q) ∈ I.writes s i then (rebase (I.writes s i) (joinMem t.mem) (I.isa.exec rodata i s)).mem rOutput q
      else (rebase (I.writes s i) (joinMem t.mem) (I.isa.exec rodata i s)).mem rInput q) = (I.isa.exec rodata i s).mem rOutput q := by
    intro q
    by_cases hw : (rOutput, q) ∈ I.writes s i
    · simp only [hw, ↓reduceIte, rebase]
    · have hw1 : (rInput, q) ∉ I.writes s i := fun h => hA.2 _ h rfl
      simp only [hw, hw1, ↓reduceIte, rebase, joinMem, show rInput ≠ rOutput by decide]
      rw [hmIn q, hfr rOutput q hw]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_, fun q => ?_, ?_⟩, ?_⟩
  · simp only [alMem, true_or, ↓reduceIte]; exact hst q
  · simp only [alMem, or_true, ↓reduceIte]; exact hst q
  · intro r q hr1 hr2
    simp only [alMem, hr1, hr2, or_self, ↓reduceIte, rebase]
    split
    · rfl
    · rename_i hw; simp only [joinMem, hr2, ↓reduceIte]; rw [hmOt r q hr1 hr2, hfr r q hw]
  · intro q hq
    have hw2 : (rOutput, q) ∉ I.writes s i := fun h => by
      have : q < I.bumpB B s i := X86.foldB_out (I.writes s i) B q h
      omega
    have hw1 : (rInput, q) ∉ I.writes s i := fun h => hA.2 _ h rfl
    rw [hfr _ _ hw2, hfr _ _ hw1]
    exact hC q (Int.le_trans (X86.foldB_ge (I.writes s i) B) hq)

theorem run_succ (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (n : Nat) (s : State (BitVec 64))
    (h : s.halted = false) :
    I.isa.run rodata prog (n + 1) s = I.isa.run rodata prog n (I.isa.exec rodata (prog.getD s.pc I.isa.nop) s) := by
  show (if s.halted then s else _) = _
  rw [h]; rfl

theorem runAl_succ (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (n : Nat) (t : State (BitVec 64))
    (h : t.halted = false) :
    I.isaAl.run rodata prog (n + 1) t = I.isaAl.run rodata prog n (I.execAl rodata (prog.getD t.pc I.isa.nop) t) := by
  show (if t.halted then t else _) = _
  rw [h]; rfl

/-- **The simulation along a run**: the aliased run follows the separate-region run; at the end the
output region of the latter still holds the input above `Bf`, and its input region is unchanged. -/
theorem sim_run (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) :
    ∀ (n : Nat) (B Bf : Int) (s t : State (BitVec 64)), I.AccessRun rodata prog n B Bf s → Sim s t → Clean B s →
      Sim (I.isa.run rodata prog n s) (I.isaAl.run rodata prog n t) ∧ Clean Bf (I.isa.run rodata prog n s) ∧
      ∀ q, (I.isa.run rodata prog n s).mem rInput q = s.mem rInput q := by
  intro n
  induction n with
  | zero => intro B Bf s t hA hS hC; exact ⟨hS, clean_mono _ _ _ hA hC, fun _ => rfl⟩
  | succ n ih =>
    intro B Bf s t hA hS hC
    have hth : t.halted = s.halted := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
    have htpc : t.pc = s.pc := hS.2.2.2.2.2.2.2.2.2.1
    cases hh : s.halted
    · simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte] at hA
      obtain ⟨hne, hok, hA⟩ := hA
      have hst := I.sim_step rodata (prog.getD s.pc I.isa.nop) s t B hS hC hok hh hne
      rw [I.run_succ rodata prog n s hh, I.runAl_succ rodata prog n t (hth.trans hh), htpc]
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ hA hst.1 hst.2
      refine ⟨h1, h2, fun q => (h3 q).trans ?_⟩
      exact I.exec_frame rodata _ s hh hne rInput q (fun hw => hok.2 _ hw rfl)
    · simp only [AccessRun, hh, ↓reduceIte] at hA
      rw [Isa.run_halted _ _ _ _ _ hh, Isa.run_halted _ _ _ _ _ (hth.trans hh)]
      exact ⟨hS, clean_mono _ _ _ hA hC, fun _ => rfl⟩

theorem bumpB_mono (B B' : Int) (s : State (BitVec 64)) (i : I.isa.Instr) (h : B' ≤ B) :
    I.bumpB B' s i ≤ I.bumpB B s i := by
  unfold bumpB
  generalize I.writes s i = l
  induction l generalizing B B' with
  | nil => exact h
  | cons c l ih2 => simp only [List.foldl_cons]; apply ih2; split <;> omega

theorem accessRun_mono (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) :
    ∀ (n : Nat) (B B' Bf : Int) (s : State (BitVec 64)), B' ≤ B → I.AccessRun rodata prog n B Bf s →
      I.AccessRun rodata prog n B' Bf s := by
  intro n
  induction n with
  | zero => intro B B' Bf s hB hA; exact Int.le_trans hB hA
  | succ n ih =>
    intro B B' Bf s hB hA
    cases hh : s.halted
    · simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte] at hA ⊢
      obtain ⟨hne, hok, hA⟩ := hA
      exact ⟨hne, ⟨fun c hc hr => Int.le_trans hB (hok.1 c hc hr), hok.2⟩, ih _ _ _ _ (I.bumpB_mono _ _ _ _ hB) hA⟩
    · simp only [AccessRun, hh, ↓reduceIte] at hA ⊢
      exact Int.le_trans hB hA

theorem accessRun_halted (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (m : Nat) (B Bf : Int)
    (s : State (BitVec 64)) (hh : s.halted = true) (h : I.AccessRun rodata prog m B Bf s) : B ≤ Bf := by
  cases m with
  | zero => exact h
  | succ m => simp only [AccessRun, hh, ↓reduceIte] at h; exact h

/-- **Sequencing**: the access condition of `n` steps up to an intermediate bound, then of `m` more. -/
theorem accessRun_add (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) :
    ∀ (n m : Nat) (B B' Bf : Int) (s : State (BitVec 64)), I.AccessRun rodata prog n B B' s →
      I.AccessRun rodata prog m B' Bf (I.isa.run rodata prog n s) → I.AccessRun rodata prog (n + m) B Bf s := by
  intro n
  induction n with
  | zero =>
    intro m B B' Bf s h1 h2
    simp only [Nat.zero_add]
    exact I.accessRun_mono rodata prog m B' B Bf s h1 h2
  | succ n ih =>
    intro m B B' Bf s h1 h2
    rw [show n + 1 + m = (n + m) + 1 by omega]
    cases hh : s.halted
    · simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
      obtain ⟨hne, hok, h1⟩ := h1
      refine ⟨hne, hok, ih m _ B' Bf _ h1 ?_⟩
      rw [I.run_succ rodata prog n s hh] at h2; exact h2
    · simp only [AccessRun, hh, ↓reduceIte] at h1 ⊢
      rw [Isa.run_halted _ _ _ _ _ hh] at h2
      exact Int.le_trans h1 (I.accessRun_halted rodata prog m B' Bf s hh h2)

/-- One step without input or output cells. -/
theorem accessRun_step (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) (m : Nat) (B Bf : Int)
    (s : State (BitVec 64)) (hh : s.halted = false)
    (hne : (I.isa.exec rodata (prog.getD s.pc I.isa.nop) s).err = false)
    (hr : ∀ c ∈ I.reads s (prog.getD s.pc I.isa.nop), c.1 ≠ rInput)
    (hw : ∀ c ∈ I.writes s (prog.getD s.pc I.isa.nop), c.1 ≠ rInput ∧ c.1 ≠ rOutput)
    (h : I.AccessRun rodata prog m B Bf (I.isa.exec rodata (prog.getD s.pc I.isa.nop) s)) :
    I.AccessRun rodata prog (m + 1) B Bf s := by
  simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte]
  refine ⟨hne, ⟨fun c hc h1 => absurd h1 (hr c hc), fun c hc => (hw c hc).1⟩, ?_⟩
  have : I.bumpB B s (prog.getD s.pc I.isa.nop) = B := by
    clear h hr hne
    unfold bumpB
    generalize I.writes s (prog.getD s.pc I.isa.nop) = l at hw
    induction l generalizing B with
    | nil => rfl
    | cons c l ih =>
      simp only [List.foldl_cons, (hw c List.mem_cons_self).2, ↓reduceIte]
      exact ih B (fun d hd => hw d (List.mem_cons_of_mem _ hd))
  rw [this]; exact h

/-! ## Control components -/

/-- **The access condition does not depend on the control components**: if the run from `s'`
is, at every step count up to `n`, the run from `s` with some control components `D` overridden (and
the footprint of the next instruction does not depend on them), the access condition of the run from
`s` holds for `s'`. -/
theorem accessRun_ovr (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) :
    ∀ (n : Nat) (B Bf : Int) (s s' : State (BitVec 64)),
      (∀ k, k ≤ n → ∃ (D : Dom) (c : Ctl), I.isa.run rodata prog k s' = ovr D c (I.isa.run rodata prog k s) ∧
        I.fpOk D (prog.getD (I.isa.run rodata prog k s).pc I.isa.nop) = true) →
      I.AccessRun rodata prog n B Bf s → I.AccessRun rodata prog n B Bf s' := by
  intro n
  induction n with
  | zero => intro B Bf s s' _ h; exact h
  | succ n ih =>
    intro B Bf s s' hk hA
    obtain ⟨D, c, h0, hf0⟩ := hk 0 (Nat.zero_le _)
    change s' = ovr D c s at h0
    change I.fpOk D (prog.getD s.pc I.isa.nop) = true at hf0
    subst h0
    cases hh : s.halted
    · have hh' : (ovr D c s).halted = false := hh
      simp only [AccessRun, hh, hh', Bool.false_eq_true, ↓reduceIte] at hA ⊢
      obtain ⟨hne, hok, hA⟩ := hA
      obtain ⟨D1, c1, h1, -⟩ := hk 1 (by omega)
      have h1' : I.isa.exec rodata (prog.getD s.pc I.isa.nop) (ovr D c s) =
          ovr D1 c1 (I.isa.exec rodata (prog.getD s.pc I.isa.nop) s) := by
        simpa only [Isa.run, hh, hh', ovr_pc, Bool.false_eq_true, ↓reduceIte] using h1
      have hpc : (ovr D c s).pc = s.pc := rfl
      rw [hpc, h1']
      refine ⟨hne, ⟨fun x hx => hok.1 x (by rwa [I.reads_ovr _ _ _ _ hf0] at hx),
        fun x hx => hok.2 x (by rwa [I.writes_ovr _ _ _ _ hf0] at hx)⟩, ?_⟩
      have hb : I.bumpB B (ovr D c s) (prog.getD s.pc I.isa.nop) = I.bumpB B s (prog.getD s.pc I.isa.nop) := by
        unfold bumpB; rw [I.writes_ovr _ _ _ _ hf0]
      rw [hb]
      apply ih _ _ _ _ _ hA
      intro k hk'
      obtain ⟨D2, c2, h2, hf2⟩ := hk (k + 1) (by omega)
      rw [I.run_succ rodata prog k _ hh', I.run_succ rodata prog k _ hh, hpc, h1'] at h2
      rw [I.run_succ rodata prog k _ hh] at hf2
      exact ⟨D2, c2, h2, hf2⟩
    · have hh' : (ovr D c s).halted = true := hh
      simp only [AccessRun, hh, hh', ↓reduceIte] at hA ⊢
      exact hA

/-! ## Footprints of relocated runs (as `AliasTrace.lean`) -/

/-- The read and write cells of each step along a path of a symbolic state. -/
def traceCells (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) : List Nat → State E → List (Cells × Cells)
  | [], _ => []
  | i :: rest, s => (I.reads s (prog.getD i I.isa.nop), I.writes s (prog.getD i I.isa.nop)) ::
      traceCells rodata prog rest (I.isa.exec rodata (prog.getD i I.isa.nop) s)

theorem bumpB_eq (ρ : Reloc) (b : Int) (s : State (BitVec 64)) (i : I.isa.Instr) (W : Cells)
    (hw : I.writes s i = W.map (shiftCell ρ)) : I.bumpB b s i = bumpC (ρ.wshift rOutput) b W := by
  unfold bumpB; rw [hw]; exact fold_shift ρ W b

set_option maxHeartbeats 4000000 in
/-- **The access condition along a relocated symbolic path**, from the base cells. -/
theorem path_access (ρ : Reloc) (hρ : ρ.ok) (rodata : Array (BitVec 64)) (prog : Array I.isa.Instr) :
    ∀ (idx : List Nat) (t : State E) (env : Nat → BitVec 64) (b bf : Int),
      I.isa.pathOk rodata prog idx t = true →
      (∀ e ∈ I.R.traceDecodes rodata (idx.map (prog.getD · I.isa.nop)) t, E.relocOk ρ e) →
      accessCells (ρ.wshift rInput) (ρ.wshift rOutput) b bf (I.traceCells rodata prog idx t) →
      I.AccessRun rodata prog idx.length b bf (mapState (E.eval env) (relocState ρ t)) := by
  intro idx
  induction idx with
  | nil => intro t env b bf _ _ h; exact h
  | cons i rest ih =>
    intro t env b bf hp hdec hacc
    simp only [Isa.pathOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
    obtain ⟨⟨⟨he, hh⟩, hpc⟩, hrest⟩ := hp
    simp only [List.map_cons, Isa.Relocatable.traceDecodes, List.mem_append] at hdec
    simp only [traceCells, accessCells] at hacc
    obtain ⟨hr, hw, hacc⟩ := hacc
    generalize hins : prog.getD i I.isa.nop = ins at hdec hr hw hacc hrest
    have hne1 : (I.isa.exec rodata ins t).err = false := I.isa.pathOk_err rodata prog rest _ hrest
    have hdec1 : ∀ e ∈ I.R.decodes rodata ins t, E.relocOk ρ e := fun e h => hdec e (Or.inl h)
    have hrel : I.isa.exec rodata ins (relocState ρ t) = relocState ρ (I.isa.exec rodata ins t) :=
      I.R.exec_reloc ρ hρ rodata ins t hne1 hdec1
    have hne2 : (I.isa.exec rodata ins (relocState ρ t)).err = false := by rw [hrel]; exact hne1
    have hmap : I.isa.exec rodata ins (mapState (E.eval env) (relocState ρ t)) =
        mapState (E.eval env) (relocState ρ (I.isa.exec rodata ins t)) := by
      rw [I.isa.exec_map (E.eval env) (E.eval_isHom env) rodata ins _ hne2, hrel]
    have hh2 : (relocState ρ t).halted = false := hh
    obtain ⟨hcr, hcw⟩ := I.cells_reloc ρ hρ rodata ins t hh hne1 hdec1
    obtain ⟨hmr, hmw⟩ := I.cells_map (E.eval env) (E.eval_isHom env) rodata ins (relocState ρ t) hh2 hne2
    have hh3 : (mapState (E.eval env) (relocState ρ t)).halted = false := hh
    have hpc3 : (mapState (E.eval env) (relocState ρ t)).pc = i := hpc
    simp only [List.length_cons, AccessRun, hh3, Bool.false_eq_true, ↓reduceIte, hpc3, hins]
    refine ⟨?_, ⟨fun c hc hc1 => ?_, fun c hc hc1 => ?_⟩, ?_⟩
    · rw [hmap]; exact hne1
    · rw [hmr, hcr] at hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      simp only [shiftCell] at hc1 ⊢
      have := hr c0 hc0 hc1; rw [hc1]; exact this
    · rw [hmw, hcw] at hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      exact hw c0 hc0 hc1
    · rw [I.bumpB_eq ρ b _ ins (I.writes t ins) (hmw.trans hcw), hmap]
      exact ih _ env _ bf hrest (fun e h => hdec e (Or.inr h)) hacc


/-- **The access condition of a certified slice at a relocated position.** -/
theorem sliceAccess {rodata : Array (BitVec 64)} {prog : Array I.isa.Instr} {B : Int}
    (C : SliceCert I.isa I.R rodata prog B) (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B)
    (S : State (BitVec 64)) (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) (hs : SliceCert.Ok S)
    (b bf : Int) (h : accessCells (ρ.wshift rInput) (ρ.wshift rOutput) b bf (I.traceCells rodata prog C.idx C.cut)) :
    I.AccessRun rodata prog C.idx.length b bf S := by
  have he : mapState (E.eval (envOf S)) (relocState ρ C.cut) = S := by
    show mapState (E.eval (envOf S)) (relocState ρ (cutOf C.ctl C.sc)) = S
    rw [hc]; exact eval_cutOf C.ctl S hs
  rw [← he]
  exact I.path_access ρ hρ rodata prog C.idx C.cut _ b bf C.path (C.dec_ok ρ hρ hw) h

/-- Consecutive slices share their cuts (as the generated segments do). -/
def ChainOk {rodata : Array (BitVec 64)} {prog : Array I.isa.Instr} {B : Int} :
    List (SliceCert I.isa I.R rodata prog B) → Prop
  | [] => True
  | [_] => True
  | C :: D :: L => C.ctl' = D.ctl ∧ C.sc' = D.sc ∧ ChainOk (D :: L)

/-- **A segment's access condition** from its slices' summaries (as `X86.chain_access`). -/
theorem chain_access {rodata : Array (BitVec 64)} {prog : Array I.isa.Instr} {B : Int}
    (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) :
    ∀ (L : List (SliceCert I.isa I.R rodata prog B)) (S : State (BitVec 64)) (b bf : Int),
      I.ChainOk L → (∀ C ∈ L.head?, relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) → SliceCert.Ok S →
      SummOk (ρ.wshift rInput) (ρ.wshift rOutput) b bf (L.map fun C => summ (I.traceCells rodata prog C.idx C.cut)) →
      I.AccessRun rodata prog (L.map fun C => C.idx.length).sum b bf S := by
  intro L
  induction L with
  | nil => intro S b bf _ _ _ h; exact h
  | cons C L ih =>
    intro S b bf hch hc hs hsum
    simp only [List.map_cons, SummOk] at hsum
    obtain ⟨hlo, hgap, hin, hrest⟩ := hsum
    have hc' := hc C rfl
    have st := C.step ρ hρ hw S hc' hs
    have hacc : I.AccessRun rodata prog C.idx.length b (nextB (ρ.wshift rOutput) b (summ (I.traceCells rodata prog C.idx C.cut))) S := by
      apply I.sliceAccess C ρ hρ hw S hc' hs
      apply summ_access _ _ _ _ _ hlo hgap
      · unfold nextB; split <;> omega
      · intro hi h; unfold nextB; rw [h]; simp only; omega
      · exact hin
    simp only [List.map_cons, List.sum_cons]
    apply I.accessRun_add rodata prog _ _ _ _ _ S hacc
    rw [st.1]
    cases L with
    | nil => simp only [List.map_nil, List.sum_nil]; simp only [List.map_nil, SummOk] at hrest; exact hrest
    | cons D L =>
      obtain ⟨h1, h2, hch'⟩ := hch
      apply ih _ _ _ hch' _ st.2.2.1 hrest
      intro D' hD'
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hD'
      subst hD'
      rw [← h1, ← h2]; exact st.2.2.2

/-- A one-slice segment without input or output cells keeps any bound. -/
theorem seg1_access {rodata : Array (BitVec 64)} {prog : Array I.isa.Instr} {B : Int}
    (C : SliceCert I.isa I.R rodata prog B) (ρ : Reloc) (hρ : ρ.ok)
    (hw : ρ.within B) (S : State (BitVec 64)) (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S)
    (hs : SliceCert.Ok S) (hsum : summ (I.traceCells rodata prog C.idx C.cut) = ⟨none, none, none, false⟩) (b : Int) :
    I.AccessRun rodata prog C.idx.length b b S := by
  have := I.chain_access ρ hρ hw [C] S b b trivial (by intro D hD; simp at hD; subst hD; exact hc) hs
    (by simp only [List.map_cons, List.map_nil, SummOk, hsum, nextB]; simp)
  simpa using this

end AlIsa
end Keccaktree.Asm

/-! ## Overrides and the views of the aliased machine -/
namespace Keccaktree.Asm.X86
variable {α : Type} [LaneOps α]

theorem normCtl_ovr (D : Dom) (c : Ctl) (X : State α) : normCtl (ovr D c X) = normCtl X := by
  simp only [normCtl, ovr, Dom.all, Bool.cond_true, State.mk.injEq, and_true, true_and]
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  have : [0, 1, 2, 3, 4, 5, 6, 7].contains i = true := by
    simp only [List.contains_iff_mem]; simp; omega
  rw [this]; rfl

theorem dupState_ovr (D : Dom) (c : Ctl) (X : State α) : dupState (ovr D c X) = ovr D c (dupState X) := rfl

theorem dupState_normCtl (X : State α) : dupState (normCtl X) = normCtl (dupState X) := rfl

end Keccaktree.Asm.X86
