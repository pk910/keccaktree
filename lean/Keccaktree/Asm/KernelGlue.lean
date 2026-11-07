import Keccaktree.Asm.Glue
import Keccaktree.Asm.X86Steps
import Keccaktree.Asm.Final
import Keccaktree.Asm.Node
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Gluing segment runs into a kernel run

A kernel's run is a chain of segment runs (generated `Seg` files, each at a
relocated position) and concrete count steps (`X86Steps`).  Each hand-over
needs the next segment's start cut, relocated, to be the cut of the concrete
state: `cut_transfer` gets it from the previous segment's end cut when the
concrete steps in between kept the control words, and the two closed control
states agree on them (after relocating by `σ` for a loop's back edge).
-/
namespace Keccaktree.Asm
open X86

theorem cutVar_eq_of_env (L L' : List Nat) (S U : State (BitVec 64)) (i : Nat) (hi : i ∈ L') (hin : i ∈ L)
    (h : envOf U i = envOf S i) : cutVar L' U i = cutVar L S i := by
  simp only [cutVar, List.contains_iff_mem.mpr hi, List.contains_iff_mem.mpr hin, ↓reduceIte, h]

/-- **Hand-over between segments.** From the end cut of a segment (`ρ`, control words `L`,
closed state `sc`) to the start cut of the next one (`ρ'`, `L'`, `sc'`) at a concrete state `U`
that has the control words of `S` and the control part of `sc'`. -/
theorem cut_transfer (ρ ρ' : Reloc) (hρ : ρ.ok) (hρ' : ρ'.ok) (L L' : List Nat) (sc sc' S U : State (BitVec 64))
    (h : relocState ρ (cutOf L sc) = cutOf L S)
    (hL : ∀ i ∈ L', i ∈ L ∧ (i < 288 ∨ memVarRegion i = rStack))
    (henv : ∀ i ∈ L', envOf U i = envOf S i)
    (hval : ∀ i ∈ L', E.reloc ρ (cutVar L sc i) = E.reloc ρ' (cutVar L' sc' i))
    (hc : U.g = sc'.g ∧ U.k = sc'.k ∧ U.zf = sc'.zf ∧ U.cf = sc'.cf ∧ U.nf = sc'.nf ∧ U.vf = sc'.vf ∧
      U.vl = sc'.vl ∧ U.pc = sc'.pc ∧ U.depth = sc'.depth) :
    relocState ρ' (cutOf L' sc') = cutOf L' U := by
  apply relocState_cutOf ρ' L' sc' U
  · intro i hi
    obtain ⟨hin, hcell⟩ := hL i hi
    rw [cutVar_eq_of_env L L' S U i hi hin (henv i hi), cut_word ρ hρ L sc S h i hcell, hval i hi]
  · intro i hi h288
    rcases (hL i hi).2 with h' | h'
    · omega
    · rw [h']; simp only [Reloc.wshift, hρ'.2.1]; rfl
  · exact hc

/-- The value condition of `cut_transfer` for the same relocation: the closed states agree. -/
theorem hval_same (ρ : Reloc) (L L' : List Nat) (sc sc' : State (BitVec 64))
    (h : (L'.all fun i => cutVar L sc i == cutVar L' sc' i) = true) :
    ∀ i ∈ L', E.reloc ρ (cutVar L sc i) = E.reloc ρ (cutVar L' sc' i) := by
  intro i hi
  have := List.all_eq_true.mp h i hi
  rw [beq_iff_eq] at this
  rw [this]

/-- The value condition of `cut_transfer` for a loop's back edge: the end state is the start state
moved by `σ` (one iteration), and the next iteration runs at `ρ + σ`. -/
theorem hval_succ (ρ σ : Reloc) (hρ : ρ.ok) (hσ : σ.ok) (L L' : List Nat) (sc sc' : State (BitVec 64))
    (h : (L'.all fun i => cutVar L sc i == E.reloc σ (cutVar L' sc' i)) = true) :
    ∀ i ∈ L', E.reloc ρ (cutVar L sc i) = E.reloc (ρ.add σ) (cutVar L' sc' i) := by
  intro i hi
  have := List.all_eq_true.mp h i hi
  rw [beq_iff_eq] at this
  rw [this, E.reloc_add ρ σ hρ hσ]

/-- The control-word side conditions of `cut_transfer` (decidable form). -/
theorem hL_dec (L L' : List Nat)
    (h : (L'.all fun i => L.contains i && (decide (i < 288) || memVarRegion i == rStack)) = true) :
    ∀ i ∈ L', i ∈ L ∧ (i < 288 ∨ memVarRegion i = rStack) := by
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at this
  exact this

/-- A pointer control word of a concrete state. -/
theorem cutVar_ptr_of (ctl : List Nat) (S : State (BitVec 64)) (i : Nat) (a : Addr) (hi : i ∈ ctl)
    (h : envOf S i = gprWord a) (hwf : a.wf) (hr : a.region ≠ 0) : cutVar ctl S i = .ptr a := by
  simp only [cutVar, List.contains_iff_mem.mpr hi, ↓reduceIte, h, wordGpr_gprWord a hwf]
  simp [hr]

/-- One fetch-execute step of a running state. -/
theorem X86.run_one (rodata : Array (BitVec 64)) (prog : Array X86.Instr) (S : State (BitVec 64))
    (hh : S.halted = false) : X86.isa.run rodata prog 1 S = X86.exec rodata (prog.getD S.pc .nop) S := by
  show (if S.halted then S else X86.isa.run rodata prog 0 (X86.isa.exec rodata (prog.getD S.pc X86.isa.nop) S)) = _
  rw [hh]; rfl

/-- A general register as a cut variable. -/
theorem envOf_gdVar (S : State (BitVec 64)) (n : Nat) (hn : n < 32) :
    envOf S (256 + n) = S.getGD n := by
  have h := envOf_gd S ⟨n, hn⟩
  simp only [gdVar] at h
  rw [h]
  simp only [State.getGD, Vector.getD]
  simp [Array.getD, hn]

theorem getGD_eq (S : State (BitVec 64)) (n : Nat) : S.getGD n = S.gd.getD n 0 := rfl

theorem memStore_same (m : Region → Int → BitVec 64) (r : Region) (q : Int) (v : BitVec 64) :
    memStore m r q v r q = v := by simp [memStore]

theorem memStore_other (m : Region → Int → BitVec 64) (r r' : Region) (q q' : Int) (v : BitVec 64)
    (h : r' ≠ r ∨ q' ≠ q) : memStore m r q v r' q' = m r' q' := by
  simp only [memStore]
  rw [if_neg (by rintro ⟨h1, h2⟩; rcases h with h | h <;> contradiction)]

end Keccaktree.Asm
