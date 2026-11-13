import Keccaktree.Asm.AliasBase
import Keccaktree.Asm.Reloc
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Footprint cells: relocation shifts, the access condition on base cells, summaries

What the in-place access proofs need of read/write cells, independent of the instruction set
(`AliasTrace.lean` for x86, `AliasIsa.lean` for any `AlIsa`): `shiftCell` (a relocated cell),
`accessCells` (the access condition on base cells, shifted), the per-slice summaries `summ` with
`summ_access`, and the chain conditions `nextB`/`SummOk`.
-/
namespace Keccaktree.Asm
open X86
namespace X86
variable {α β : Type} [LaneOps α] [LaneOps β]

/-- A relocated cell. -/
def shiftCell (ρ : Reloc) (c : Region × Int) : Region × Int := (c.1, c.2 + ρ.wshift c.1)

theorem storeCells_addr (ρ : Reloc) (hρ : ρ.ok) (a : Addr) (n : Nat) :
    storeCells (ρ.addr a) n = (storeCells a n).map (shiftCell ρ) := by
  simp only [storeCells, List.map_map, Function.comp_def, shiftCell, Reloc.addr_region, Reloc.addr_div8 ρ hρ]
  congr 1; funext i; congr 1; omega

theorem storeCells_addr_sub (ρ : Reloc) (hρ : ρ.ok) (a : Addr) (d : Int) (n : Nat) :
    storeCells { region := a.region, off := (ρ.addr a).off - d } n =
      (storeCells { region := a.region, off := a.off - d } n).map (shiftCell ρ) := by
  rw [← storeCells_addr ρ hρ]
  congr 1
  simp only [Reloc.addr, Addr.mk.injEq, true_and]; omega

abbrev Cells := List (Region × Int)

/-- The bound after a step's (base) writes, output cells shifted by `δ2`. -/
def bumpC (δ2 b : Int) (w : Cells) : Int := w.foldl (fun b c => if c.1 = rOutput then max b (c.2 + δ2 + 1) else b) b

/-- The access condition on base cells shifted by `δ1` (input) and `δ2` (output). -/
def accessCells (δ1 δ2 : Int) : Int → Int → List (Cells × Cells) → Prop
  | b, bf, [] => b ≤ bf
  | b, bf, (r, w) :: l => (∀ c ∈ r, c.1 = rInput → b ≤ c.2 + δ1) ∧ (∀ c ∈ w, c.1 ≠ rInput) ∧
      accessCells δ1 δ2 (bumpC δ2 b w) bf l

theorem fold_shift (ρ : Reloc) (W : Cells) : ∀ b : Int,
    (W.map (shiftCell ρ)).foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) b =
      bumpC (ρ.wshift rOutput) b W := by
  induction W with
  | nil => intro b; rfl
  | cons c W ih =>
    intro b
    simp only [List.map_cons, List.foldl_cons, bumpC] at ih ⊢
    rw [← ih]
    congr 1
    by_cases h : c.1 = rOutput
    · simp only [shiftCell, h, ↓reduceIte]; (try congr 1); (try omega)
    · simp only [shiftCell, h, ↓reduceIte]

end X86
end Keccaktree.Asm

/-! ## Summaries of base cells, splitting and composing -/
namespace Keccaktree.Asm
open X86
namespace X86

/-- What the access condition needs from a list of base step cells: the lowest input word read, the
highest output word written, the smallest distance (read index − write index) of an input read after an
output write, and whether an input word is written. -/
structure Summ where
  loR : Option Int
  hiW : Option Int
  gap : Option Int
  inW : Bool
  deriving DecidableEq, Repr

def minO : Option Int → Option Int → Option Int
  | some a, some b => some (min a b) | some a, none => some a | none, b => b
def maxO : Option Int → Option Int → Option Int
  | some a, some b => some (max a b) | some a, none => some a | none, b => b
def subO : Option Int → Option Int → Option Int
  | some a, some b => some (a - b) | _, _ => none

def loIn (r : Cells) : Option Int := r.foldl (fun o c => if c.1 = rInput then minO o (some c.2) else o) none
def hiOut (w : Cells) : Option Int := w.foldl (fun o c => if c.1 = rOutput then maxO o (some c.2) else o) none

def summ : List (Cells × Cells) → Summ
  | [] => ⟨none, none, none, false⟩
  | (r, w) :: l =>
    let t := summ l
    ⟨minO (loIn r) t.loR, maxO (hiOut w) t.hiW, minO t.gap (subO t.loR (hiOut w)),
      w.any (fun c => c.1 = rInput) || t.inW⟩

theorem minO_left (a : Int) (o : Option Int) : ∃ y, minO (some a) o = some y ∧ y ≤ a := by
  cases o <;> simp [minO] <;> omega
theorem minO_right (a : Int) (o : Option Int) : ∃ y, minO o (some a) = some y ∧ y ≤ a := by
  cases o <;> simp [minO] <;> omega
theorem maxO_left (a : Int) (o : Option Int) : ∃ y, maxO (some a) o = some y ∧ a ≤ y := by
  cases o <;> simp [maxO] <;> omega
theorem maxO_right (a : Int) (o : Option Int) : ∃ y, maxO o (some a) = some y ∧ a ≤ y := by
  cases o <;> simp [maxO] <;> omega

theorem foldMin_some (l : Cells) : ∀ (x : Int) (o : Option Int), o = some x →
    ∃ lo, l.foldl (fun o c => if c.1 = rInput then minO o (some c.2) else o) o = some lo ∧ lo ≤ x := by
  induction l with
  | nil => intro x o h; exact ⟨x, h, Int.le_refl _⟩
  | cons e l ih =>
    intro x o h; subst h
    simp only [List.foldl_cons]
    split
    · obtain ⟨y, hy, hle⟩ := minO_right e.2 (some x)
      obtain ⟨lo, h1, h2⟩ := ih y _ hy
      refine ⟨lo, h1, ?_⟩
      simp [minO] at hy; omega
    · exact ih x _ rfl

theorem foldMax_some (l : Cells) : ∀ (x : Int) (o : Option Int), o = some x →
    ∃ hi, l.foldl (fun o c => if c.1 = rOutput then maxO o (some c.2) else o) o = some hi ∧ x ≤ hi := by
  induction l with
  | nil => intro x o h; exact ⟨x, h, Int.le_refl _⟩
  | cons e l ih =>
    intro x o h; subst h
    simp only [List.foldl_cons]
    split
    · obtain ⟨y, hy, hle⟩ := maxO_right e.2 (some x)
      obtain ⟨hi, h1, h2⟩ := ih y _ hy
      refine ⟨hi, h1, ?_⟩
      simp [maxO] at hy; omega
    · exact ih x _ rfl

theorem loIn_le (r : Cells) (c : Region × Int) (hc : c ∈ r) (h1 : c.1 = rInput) :
    ∃ lo, loIn r = some lo ∧ lo ≤ c.2 := by
  suffices ∀ o, ∃ lo, r.foldl (fun o c => if c.1 = rInput then minO o (some c.2) else o) o = some lo ∧ lo ≤ c.2 by
    exact this none
  induction r with
  | nil => simp at hc
  | cons d r ih =>
    intro o
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [if_pos h1]
      obtain ⟨y, hy, hle⟩ := minO_right c.2 o
      obtain ⟨lo, h2, h3⟩ := foldMin_some r y _ hy
      exact ⟨lo, h2, by omega⟩
    · exact ih hc' _

theorem hiOut_ge (w : Cells) (c : Region × Int) (hc : c ∈ w) (h1 : c.1 = rOutput) :
    ∃ hi, hiOut w = some hi ∧ c.2 ≤ hi := by
  suffices ∀ o, ∃ hi, w.foldl (fun o c => if c.1 = rOutput then maxO o (some c.2) else o) o = some hi ∧ c.2 ≤ hi by
    exact this none
  induction w with
  | nil => simp at hc
  | cons d w ih =>
    intro o
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [if_pos h1]
      obtain ⟨y, hy, hle⟩ := maxO_right c.2 o
      obtain ⟨hi, h2, h3⟩ := foldMax_some w y _ hy
      exact ⟨hi, h2, by omega⟩
    · exact ih hc' _

/-- The bound after writes stays below the highest written output word (shifted), or unchanged. -/
theorem bumpC_le (δ2 b bf : Int) (w : Cells) (hb : b ≤ bf) (hw : ∀ hi, hiOut w = some hi → hi + δ2 + 1 ≤ bf) :
    bumpC δ2 b w ≤ bf := by
  unfold bumpC
  suffices ∀ (b' : Int), b' ≤ bf → ∀ (l : Cells), (∀ c ∈ l, c.1 = rOutput → c.2 + δ2 + 1 ≤ bf) →
      l.foldl (fun b c => if c.1 = rOutput then max b (c.2 + δ2 + 1) else b) b' ≤ bf by
    apply this b hb w
    intro c hc h1
    obtain ⟨hi, h2, h3⟩ := hiOut_ge w c hc h1
    have := hw hi h2; omega
  intro b' hb' l
  induction l generalizing b' with
  | nil => intro _; exact hb'
  | cons c l ih =>
    intro hl
    simp only [List.foldl_cons]
    apply ih _ _ (fun d hd => hl d (List.mem_cons_of_mem _ hd))
    split
    · rename_i h; have := hl c (List.mem_cons_self) h; omega
    · exact hb'

/-- **The access condition from a summary** (linear conditions on the shifts and bounds). -/
theorem summ_access (δ1 δ2 : Int) : ∀ (l : List (Cells × Cells)) (b bf : Int),
    (∀ lo, (summ l).loR = some lo → b ≤ lo + δ1) →
    (∀ g, (summ l).gap = some g → δ2 + 1 ≤ g + δ1) →
    b ≤ bf → (∀ hi, (summ l).hiW = some hi → hi + δ2 + 1 ≤ bf) →
    (summ l).inW = false → accessCells δ1 δ2 b bf l := by
  intro l
  induction l with
  | nil => intro b bf _ _ hb _ _; exact hb
  | cons rw l ih =>
    obtain ⟨r, w⟩ := rw
    intro b bf hlo hgap hb hhi hin
    simp only [summ, Bool.or_eq_false_iff, List.any_eq_false] at hlo hgap hhi hin
    refine ⟨fun c hc h1 => ?_, fun c hc h1 => ?_, ?_⟩
    · obtain ⟨lo, h2, h3⟩ := loIn_le r c hc h1
      rw [h2] at hlo
      obtain ⟨y, hy, hle⟩ := minO_left lo (summ l).loR
      have := hlo y hy; omega
    · have := hin.1 c hc; simp [h1] at this
    · apply ih
      · intro lo hlo'
        rw [hlo'] at hlo hgap
        obtain ⟨y, hy, hle⟩ := minO_right lo (loIn r)
        have hb2 : b ≤ lo + δ1 := by have := hlo y hy; omega
        unfold bumpC
        suffices ∀ (b' : Int), b' ≤ lo + δ1 → ∀ (l' : Cells), (∀ c ∈ l', c ∈ w) →
            l'.foldl (fun b c => if c.1 = rOutput then max b (c.2 + δ2 + 1) else b) b' ≤ lo + δ1 by
          exact this b hb2 w (fun c hc => hc)
        intro b' hb' l'
        induction l' generalizing b' with
        | nil => intro _; exact hb'
        | cons c l' ih2 =>
          intro hsub
          simp only [List.foldl_cons]
          apply ih2 _ _ (fun d hd => hsub d (List.mem_cons_of_mem _ hd))
          split
          · rename_i h
            obtain ⟨hi, hhi1, hhi2⟩ := hiOut_ge w c (hsub c List.mem_cons_self) h
            rw [hhi1] at hgap
            obtain ⟨y2, hy2, hle2⟩ := minO_right (lo - hi) (summ l).gap
            have : δ2 + 1 ≤ y2 + δ1 := hgap y2 (by simpa only [subO] using hy2)
            omega
          · exact hb'
      · intro g hg'
        rw [hg'] at hgap
        obtain ⟨y, hy, hle⟩ := minO_left g (subO (summ l).loR (hiOut w))
        have := hgap y hy; omega
      · apply bumpC_le δ2 b bf w hb
        intro hi h
        rw [h] at hhi
        obtain ⟨y, hy, hle⟩ := maxO_left hi (summ l).hiW
        have := hhi y hy; omega
      · intro hi h
        rw [h] at hhi
        obtain ⟨y, hy, hle⟩ := maxO_right hi (hiOut w)
        have := hhi y hy; omega
      · exact hin.2

end X86
end Keccaktree.Asm

namespace Keccaktree.Asm
open X86
namespace X86
variable {α β : Type} [LaneOps α] [LaneOps β]

/-- The bound after a slice with summary `s`. -/
def nextB (δ2 b : Int) (s : Summ) : Int :=
  match s.hiW with
  | some hi => max b (hi + δ2 + 1)
  | none => b

/-- The per-slice conditions along a chain of summaries. -/
def SummOk (δ1 δ2 : Int) : Int → Int → List Summ → Prop
  | b, bf, [] => b ≤ bf
  | b, bf, s :: l => (∀ lo, s.loR = some lo → b ≤ lo + δ1) ∧ (∀ g, s.gap = some g → δ2 + 1 ≤ g + δ1) ∧
      s.inW = false ∧ SummOk δ1 δ2 (nextB δ2 b s) bf l

theorem view_map (f : α → β) (t : State α) :
    ({ mapState f t with mem := joinMem (mapState f t).mem } : State β) = mapState f { t with mem := joinMem t.mem } := by
  simp only [mapState, State.mk.injEq, and_true, true_and]
  funext r q; simp only [joinMem]; split <;> rfl


end X86
end Keccaktree.Asm
