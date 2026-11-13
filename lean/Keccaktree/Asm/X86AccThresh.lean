import Keccaktree.Asm.X86AccFr
import Keccaktree.Asm.X86Thresh
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The access condition under every value of a runtime threshold

avx2_x4 and avx2_x10 run under the image `setWord rodata 112 v` (`X86Thresh`); their segments are proved
for the default image and never load word 112 (`pathW`, per slice).  The access condition of a run only
depends on the states along it, so it carries over when the two runs agree at every prefix
(`accessRun_of_runs`); a chain of slices that never load the word agrees at every prefix
(`chain_agree`, from `pathW_run` on the prefixes of each slice's path).  `seg_accV`: a segment's access
condition under the image, from its summaries.
-/
namespace Keccaktree.Asm.X86K
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86

/-- The access condition depends only on the states of the run. -/
theorem accessRun_of_runs {r1 r2 : Array (BitVec 64)} {prog : Array Instr} :
    ∀ (n : Nat) (B Bf : Int) (S : State (BitVec 64)),
      (∀ j, j ≤ n → X86.isa.run r2 prog j S = X86.isa.run r1 prog j S) →
      AccessRun r1 prog n B Bf S → AccessRun r2 prog n B Bf S := by
  intro n
  induction n with
  | zero => intro B Bf S _ h; exact h
  | succ n ih =>
    intro B Bf S hj hA
    cases hh : S.halted
    · simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte] at hA ⊢
      obtain ⟨hne, hok, hrest⟩ := hA
      have e1 : exec r2 (prog.getD S.pc .nop) S = exec r1 (prog.getD S.pc .nop) S := by
        have := hj 1 (by omega)
        rwa [X86.run_one r2 prog S hh, X86.run_one r1 prog S hh] at this
      rw [e1]
      refine ⟨hne, hok, ih _ _ _ (fun j hjn => ?_) hrest⟩
      have := hj (j + 1) (by omega)
      rw [x86_run_succ r2 prog j S hh, x86_run_succ r1 prog j S hh, e1] at this
      exact this
    · simp only [AccessRun, hh, ↓reduceIte] at hA ⊢; exact hA

theorem pathW_take {rodata : Array (BitVec 64)} {prog : Array Instr} {w : Nat} :
    ∀ (idx : List Nat) (t : State E) (j : Nat), pathW rodata prog w idx t = true →
      pathW rodata prog w (idx.take j) t = true
  | [], t, j, h => by simpa using h
  | p :: rest, t, 0, h => by
    simp only [List.take_zero, pathW, Bool.not_eq_true']
    exact pathW_err rodata prog w _ t h
  | p :: rest, t, j + 1, h => by
    simp only [pathW, Bool.and_eq_true, List.take_succ_cons] at h ⊢
    exact ⟨h.1, pathW_take rest _ j h.2⟩

/-- **A slice that never loads word `w` runs the same under both images at every prefix.** -/
theorem SliceCert.runs_agree {rodata r2 : Array (BitVec 64)} {prog : Array Instr} {B : Int} {w : Nat}
    (C : SliceCert X86.isa X86.isaReloc rodata prog B) (hr : AgreeExcept rodata r2 w)
    (hW : pathW rodata prog w C.idx (cutOf C.ctl C.sc) = true)
    (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S : State (BitVec 64))
    (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) (hs : SliceCert.Ok S) :
    ∀ j, j ≤ C.idx.length → X86.isa.run r2 prog j S = X86.isa.run rodata prog j S := by
  intro j hj
  have hok := C.dec_ok ρ hρ hw
  have hW' := pathW_reloc ρ hρ rodata prog w C.idx (cutOf C.ctl C.sc) hW (fun e he => hok e he)
  have he : mapState (E.eval (envOf S)) (relocState ρ (cutOf C.ctl C.sc)) = S := by
    rw [hc]; exact eval_cutOf C.ctl S hs
  have := pathW_run hr prog (C.idx.take j) _ (pathW_take _ _ j hW') (envOf S)
  rw [he, List.length_take, Nat.min_eq_left hj] at this
  exact this

/-- A chain of such slices (a segment) at every prefix. -/
theorem chain_agree {rodata r2 : Array (BitVec 64)} {prog : Array Instr} {B : Int} {w : Nat}
    (hr : AgreeExcept rodata r2 w) (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) :
    ∀ (L : List (SliceCert X86.isa X86.isaReloc rodata prog B)) (S : State (BitVec 64)),
      ChainOk L → (∀ C ∈ L.head?, relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) → SliceCert.Ok S →
      (∀ C ∈ L, pathW rodata prog w C.idx (cutOf C.ctl C.sc) = true) →
      ∀ j, j ≤ (L.map fun C => C.idx.length).sum → X86.isa.run r2 prog j S = X86.isa.run rodata prog j S := by
  intro L
  induction L with
  | nil => intro S _ _ _ _ j hj; simp at hj; subst hj; rfl
  | cons C L ih =>
    intro S hch hc hs hW j hj
    have hc' := hc C rfl
    have hC := SliceCert.runs_agree C hr (hW C List.mem_cons_self) ρ hρ hw S hc' hs
    by_cases hjC : j ≤ C.idx.length
    · exact hC j hjC
    · have st := C.step ρ hρ hw S hc' hs
      have e : X86.isa.run r2 prog C.idx.length S = X86.isa.run rodata prog C.idx.length S := hC _ (Nat.le_refl _)
      rw [show j = C.idx.length + (j - C.idx.length) by omega, Isa.run_add, Isa.run_add, e]
      simp only [List.map_cons, List.sum_cons] at hj
      rw [st.1]
      cases L with
      | nil => exfalso; simp at hj; omega
      | cons D L =>
        obtain ⟨h1, h2, hch'⟩ := hch
        apply ih _ hch' _ st.2.2.1 (fun D' hD' => hW D' (List.mem_cons_of_mem _ hD')) _ (by omega)
        intro D' hD'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hD'
        subst hD'
        rw [← h1, ← h2]; exact st.2.2.2

/-- **A segment's access condition at node `m` under an image differing only in word `w`**, from its
summaries and the slices' `pathW`. -/
theorem seg_accV {rodata r2 : Array (BitVec 64)} {prog : Array Instr} {B : Int} {w : Nat}
    (hr : AgreeExcept rodata r2 w) (F : SegFacts rodata prog)
    (L : List (SliceCert X86.isa X86.isaReloc rodata prog B))
    (hL : (L.map fun C => C.idx.length).sum = F.len) (hch : ChainOk L)
    (hhd : ∀ C ∈ L.head?, C.ctl = F.ctl0 ∧ C.sc = F.sc0)
    (hW : ∀ C ∈ L, pathW rodata prog w C.idx (cutOf C.ctl C.sc) = true)
    (m : Nat) (hw : (rho m).within B) (S : State (BitVec 64))
    (hcut : relocState (rho m) (cutOf F.ctl0 F.sc0) = cutOf F.ctl0 S) (hs : SliceCert.Ok S) (b bf : Int)
    (hsum : SummOk (8 * (m : Int)) (4 * (m : Int)) b bf (L.map fun C => summ (traceCells rodata prog C.idx C.cut))) :
    AccessRun r2 prog F.len b bf S := by
  have h1 := seg_acc F L hL hch hhd m hw S hcut hs b bf hsum
  apply accessRun_of_runs _ _ _ _ _ h1
  intro j hj
  apply chain_agree hr (rho m) (rho_ok m) hw L S hch
    (by intro C hC; obtain ⟨h1, h2⟩ := hhd C hC; rw [h1, h2]; exact hcut) hs hW j (by rw [hL]; exact hj)

end Keccaktree.Asm.X86K
