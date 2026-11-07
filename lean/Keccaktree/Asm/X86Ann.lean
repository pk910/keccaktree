import Keccaktree.Asm.ArmEntryCtl
import Keccaktree.Asm.LibX86
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# x86: control components left behind by a caller, with a per-index annotation

`LibX86.mkKernel` needs the whole program to leave the dirty components alone
(`run_ovr_static`).  The AVX-512 kernels write the mask `k1` (`kmovw`) at the start
of their batch subroutine and read it in masked moves inside: there `k1` is clean.
As on AArch64 (`Arm.run_ovr_ann`), a per-index annotation of dirty sets, checked by
the kernel, gives the run from any control state.  x86 has internal calls: the
successor of a `ret` is not static, so the dirty set after a `ret` must be included
in *every* index's annotation (`annOk` checks it against all entries and the default).
-/
namespace Keccaktree.Asm.X86
open Keccaktree.Asm
open LaneOps

variable {α : Type} [LaneOps α]

/-- The static successors of instruction `i` at index `p`; `none`: any index (`ret`). -/
def succsX (p : Nat) : Instr → Option (List Nat)
  | .jmp t => some [t]
  | .jcc _ t => some [t, p + 1]
  | .call t => some [t]
  | .ret => none
  | .tailcall _ => some []
  | _ => some [p + 1]

/-- The step either continues at a successor or halts in place without changing the dirty set. -/
def PcOk (i : Instr) (s t : State α) : Prop :=
  (t.halted = false ∧ (succsX s.pc i = none ∨ ∃ l, succsX s.pc i = some l ∧ t.pc ∈ l)) ∨
  (t.halted = true ∧ t.pc = s.pc ∧ ∀ D, ctlAfter D i = D)

section
variable (s : State α)
@[simp] theorem next_pc_x : (next s).pc = s.pc + 1 := rfl
@[simp] theorem next_halted_x : (next s).halted = s.halted := rfl
@[simp] theorem setGD_pc_x (n : Nat) (x : α) : (s.setGD n x).pc = s.pc := rfl
@[simp] theorem setGD_halted_x (n : Nat) (x : α) : (s.setGD n x).halted = s.halted := rfl
@[simp] theorem setX_pc_x (n : Nat) (a : Addr) : (setX s n a).pc = s.pc := rfl
@[simp] theorem setX_halted_x (n : Nat) (a : Addr) : (setX s n a).halted = s.halted := rfl
@[simp] theorem writeV_pc_x (n l : Nat) (vs : List α) : (writeV s n l vs).pc = s.pc := rfl
@[simp] theorem writeV_halted_x (n l : Nat) (vs : List α) : (writeV s n l vs).halted = s.halted := rfl
@[simp] theorem fail_halted_x : (s.fail).halted = true := rfl
@[simp] theorem fail_err_x : (s.fail).err = true := rfl
end

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- Where a successful step goes. -/
theorem exec_pcX (rodata : Array (BitVec 64)) (i : Instr) (s : State α) (hh : s.halted = false)
    (he : (exec rodata i s).err = false) : PcOk i s (exec rodata i s) := by
  unfold PcOk
  cases i <;> simp only [exec, hh, Bool.false_eq_true, ↓reduceIte] at he ⊢
  all_goals (try simp only [withX, withMem, withSrc, withLoad, readG, binop, withStore, setFlagsSub, repBody] at he ⊢)
  all_goals (repeat' split)
  all_goals (try (simp only [State.fail] at he; exact absurd he (by decide)))
  all_goals (try simp only [State.storeWords, Option.ite_none_right_eq_some, Option.some.injEq] at *)
  all_goals (try subst_vars)
  all_goals (try (obtain ⟨_, rfl⟩ := ‹_ ∧ _›))
  all_goals (try (obtain ⟨_, rfl⟩ := ‹_ ∧ _›))
  all_goals first
    | (left; refine ⟨?_, ?_⟩ <;> simp_all [succsX, setFlagsNum, State.setV, next] <;> done)
    | (right; refine ⟨?_, ?_, fun D => rfl⟩ <;> simp_all <;> done)
    | (exfalso; simp_all [State.fail] <;> done)
    | (exfalso; (repeat' split at he) <;> simp_all [State.fail, next] <;> done)
    | (exfalso; simp only [*, ↓reduceIte, State.fail, Bool.true_eq_false, Bool.false_eq_true] at he)


/-- A consistent annotation (as a function of the instruction index). -/
def AnnOkX (prog : Array Instr) (ann : Nat → Dom) : Prop :=
  ∀ p, ctlOk (ann p) (prog.getD p .nop) = true ∧
    match succsX p (prog.getD p .nop) with
    | some l => ∀ q ∈ l, (ctlAfter (ann p) (prog.getD p .nop)).le (ann q) = true
    | none => ∀ q, (ctlAfter (ann p) (prog.getD p .nop)).le (ann q) = true

/-- **A run from any control state** (x86): with a consistent annotation, the run from the state with
the components dirty at its index overridden is the run up to the components dirty at the end. -/
theorem run_ovr_annX (rodata : Array (BitVec 64)) (prog : Array Instr) (ann : Nat → Dom) (hann : AnnOkX prog ann) :
    ∀ (n : Nat) (s : State α) (c : Ctl), (X86.isa.run rodata prog n s).err = false →
      ∃ c' : Ctl, X86.isa.run rodata prog n (ovr (ann s.pc) c s) =
        ovr (ann (X86.isa.run rodata prog n s).pc) c' (X86.isa.run rodata prog n s)
  | 0, s, c, _ => ⟨c, rfl⟩
  | n + 1, s, c, he => by
    cases hh : s.halted
    · have hs : ∀ t : State α, t.halted = false → X86.isa.run rodata prog (n + 1) t =
          X86.isa.run rodata prog n (exec rodata (prog.getD t.pc .nop) t) := by
        intro t ht; show (if t.halted then t else _) = _; rw [ht]; rfl
      rw [hs s hh] at he ⊢
      rw [hs _ (by rw [ovr_halted]; exact hh), ovr_pc]
      have he1 : (exec rodata (prog.getD s.pc .nop) s).err = false := by
        cases hc : (exec rodata (prog.getD s.pc .nop) s).err
        · rfl
        · rw [x86_run_err rodata prog n _ hc] at he; exact absurd he (by decide)
      obtain ⟨hok, hsucc⟩ := hann s.pc
      rw [exec_ovr rodata _ c _ s hok hh he1]
      rcases exec_pcX rodata _ s hh he1 with ⟨hh', hq⟩ | ⟨hh', hpc, hD⟩
      · have hle : (ctlAfter (ann s.pc) (prog.getD s.pc .nop)).le (ann (exec rodata (prog.getD s.pc .nop) s).pc) = true := by
          revert hsucc
          rcases hq with hq | ⟨l, hl, hm⟩
          · rw [hq]; intro h; exact h _
          · rw [hl]; intro h; exact h _ hm
        obtain ⟨c1, hc1⟩ := Arm.ovr_mono _ _ hle c (exec rodata (prog.getD s.pc .nop) s)
        rw [hc1]
        exact run_ovr_annX rodata prog ann hann n _ c1 he
      · rw [hD, Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh'), Isa.run_halted _ _ _ _ _ hh', hpc]
        exact ⟨c, rfl⟩
    · rw [Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh), Isa.run_halted _ _ _ _ _ hh]
      exact ⟨c, rfl⟩

/-! ## A three-valued annotation: the entry, one subroutine interval, the rest -/

/-- `Dom.all` at the entry (any control state), `Din` on `[lo, hi)` (e.g. a batch subroutine that
cleans a mask register first), `Dout` elsewhere. -/
def annIv (entry lo hi : Nat) (Din Dout : Dom) (p : Nat) : Dom :=
  if p = entry then Dom.all else if lo ≤ p ∧ p < hi then Din else Dout

/-- The kernel-checkable form of `AnnOkX (annIv …)`. -/
def annIvOk (prog : Array Instr) (entry lo hi : Nat) (Din Dout : Dom) : Bool :=
  Dout.le Dout &&
  (List.range (max prog.size (max hi (entry + 1)))).all fun p =>
    let i := prog.getD p .nop
    let D := annIv entry lo hi Din Dout p
    ctlOk D i &&
    match succsX p i with
    | some l => l.all fun q => (ctlAfter D i).le (annIv entry lo hi Din Dout q)
    | none => (ctlAfter D i).le Dom.all && (ctlAfter D i).le Din && (ctlAfter D i).le Dout

theorem annIvOk_sound (prog : Array Instr) (entry lo hi : Nat) (Din Dout : Dom)
    (h : annIvOk prog entry lo hi Din Dout = true) : AnnOkX prog (annIv entry lo hi Din Dout) := by
  simp only [annIvOk, Bool.and_eq_true] at h
  obtain ⟨hrefl, hall⟩ := h
  intro p
  by_cases hp : p < max prog.size (max hi (entry + 1))
  · have := List.all_eq_true.mp hall p (List.mem_range.mpr hp)
    simp only [Bool.and_eq_true] at this
    obtain ⟨hok, hs⟩ := this
    refine ⟨hok, ?_⟩
    revert hs
    cases hsx : succsX p (prog.getD p .nop) with
    | some l => intro hs q hq; exact List.all_eq_true.mp hs q hq
    | none =>
      intro hs q
      simp only [Bool.and_eq_true] at hs
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      have hq3 : annIv entry lo hi Din Dout q = Dom.all ∨ annIv entry lo hi Din Dout q = Din ∨
          annIv entry lo hi Din Dout q = Dout := by
        unfold annIv; split
        · exact Or.inl rfl
        · split
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
      rcases hq3 with e | e | e <;> rw [e] <;> assumption
  · have h1 : prog.getD p .nop = .nop := by
      simp only [Array.getD, show ¬ p < prog.size by omega, dite_false]
    have h2 : ∀ q, q ≥ max prog.size (max hi (entry + 1)) → annIv entry lo hi Din Dout q = Dout := by
      intro q hq; unfold annIv
      rw [if_neg (by omega), if_neg (by omega)]
    rw [h1, h2 p (by omega)]
    refine ⟨rfl, ?_⟩
    simp only [succsX, ctlAfter]
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    rw [h2 (p + 1) (by omega)]
    exact hrefl

end Keccaktree.Asm.X86

namespace Keccaktree.Asm.LibX86
open Keccaktree.Asm Keccaktree.Asm.X86

theorem annIv_entry (entry lo hi : Nat) (Din Dout : Dom) : annIv entry lo hi Din Dout entry = Dom.all := by
  simp [annIv]

/-- **An x86 kernel of the library** from its normalised all-count theorem, for kernels whose batch
subroutine `[lo, hi)` writes a mask register before its masked moves (the AVX-512 kernels): the
annotation `Dom.all` at the entry, `Din` on the batch, `Dom1` elsewhere is checked by the kernel. -/
def mkKernelAnn (name : String) (rank : Nat) (targets : List String) (rodata : Array (BitVec 64))
    (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat) (lo hi : Nat) (Din : Dom)
    (hann : annIvOk prog entry lo hi Din Dom1 = true)
    (h : NormThm rodata prog entry steps targets) : Library.KernelThm X86.isa EntryX86 Digest where
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
    obtain ⟨c', hc'⟩ := run_ovr_annX rodata prog (annIv entry lo hi Din Dom1)
      (annIvOk_sound prog entry lo hi Din Dom1 hann) (steps off count) (normCtl { S with pc := entry })
      (Ctl.of { S with pc := entry }) h0.2.1
    have hpc : (normCtl { S with pc := entry }).pc = entry := rfl
    rw [hpc, annIv_entry, ovr_normCtl] at hc'
    rw [hc']
    exact outcome_ovr targets off count input _ _ _ _ _ rfl h0

end Keccaktree.Asm.LibX86
