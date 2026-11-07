import Keccaktree.Asm.Footprint
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# In-place hashing: aliased input and output (x86 core lemmas)

`keccaktree_hash(out, in, count)` may be called with `out == in`.  The model keeps the input and
the output in two regions; on the machine, with `out == in`, region-2 offset `o` and region-1
offset `o` are the same bytes.

* `reads s i`: the memory cells an instruction loads (from the state before it), the
  counterpart of `Footprint.writes`.
* **`exec_local`**: an instruction depends on memory only through the cells it reads: run on a
  state whose memory differs elsewhere, it computes the same registers, flags and stored words,
  and leaves the other cells as they were.
-/
namespace Keccaktree.Asm
open X86

variable {α : Type} [LaneOps α]

namespace X86

/-- The cells of a memory operand of `n` words. -/
def memCells (s : State α) (m : MemOp) (n : Nat) : List (Region × Int) :=
  match memAddr? s m with
  | some a => storeCells a n
  | none => []

/-- The cells a vector source operand loads. -/
def srcCells (s : State α) (lanes : Nat) : Src → List (Region × Int)
  | .reg _ => []
  | .mem m => memCells s m lanes
  | .bcst m => memCells s m 1

def gsrcCells (s : State α) : GSrc → List (Region × Int)
  | .mem m => memCells s m 1
  | _ => []

/-- The cells an x86 instruction loads (from the state before it). -/
def reads (s : State α) : Instr → List (Region × Int)
  | .vmov lanes _ src _ => srcCells s lanes src
  | .vpxor lanes _ _ b | .vpand lanes _ _ b | .vpandn lanes _ _ b | .vpor lanes _ _ b | .vpaddq lanes _ _ b
  | .vpsllvq lanes _ _ b | .vpsrlvq lanes _ _ b | .vpternlogq lanes _ _ b _ | .vpshufb lanes _ _ b
  | .vpblendd lanes _ _ b _ | .vpalignr lanes _ _ b _ | .vpunpcklqdq lanes _ _ b | .vpunpckhqdq lanes _ _ b
  | .vshufi64x2 lanes _ _ b _ | .vpermt2q lanes _ _ b => srcCells s lanes b
  | .vperm2i128 _ _ b _ => srcCells s 4 b
  | .vinserti128 _ _ b _ => srcCells s 2 b
  | .kmovw _ m | .cmpm m _ | .cmprm _ m | .xorm m _ | .addm m _ | .decm m | .loadq _ m => memCells s m 1
  | .alu _ _ b | .andn _ _ b | .rorx _ b _ => gsrcCells s b
  | .ret => if s.depth = 0 then [] else match gx s 4 with
    | some sp => storeCells sp 1
    | none => []
  | .pop _ => match gx s 4 with
    | some sp => storeCells sp 1
    | none => []
  | .repmovsb => match gx s 1, gx s 6 with
    | some n, some src => storeCells src (n.off.toNat / 8)
    | _, _ => []
  | _ => []

/-- `s` with memory `m'` at the cells outside `W` (the cells of `W` keep `s`'s words). -/
def rebase (W : List (Region × Int)) (m' : Region → Int → α) (s : State α) : State α :=
  { s with mem := fun r q => if (r, q) ∈ W then s.mem r q else m' r q }

section local_
variable (rodata : Array (BitVec 64)) (m' : Region → Int → α)

/-- Memory `m'` agrees with `s` on the cells `C`. -/
def Agree (C : List (Region × Int)) (s : State α) : Prop := ∀ c ∈ C, m' c.1 c.2 = s.mem c.1 c.2

theorem read_loc (s : State α) (r : Region) (q : Int) (h : r ≠ rRodata → m' r q = s.mem r q) :
    ({ s with mem := m' } : State α).read rodata r q = s.read rodata r q := by
  simp only [State.read]; split
  · rfl
  · rename_i hr; exact h hr

theorem loadWords_loc (s : State α) (a : Addr) (n : Nat) (h : Agree m' (storeCells a n) s) :
    ({ s with mem := m' } : State α).loadWords rodata a n = s.loadWords rodata a n := by
  simp only [State.loadWords]; split
  · congr 1
    apply List.map_congr_left
    intro i hi
    apply read_loc
    intro _
    exact h (a.region, a.off / 8 + Int.ofNat i) (by simp only [storeCells, List.mem_map, List.mem_range]; exact ⟨i, by simpa using hi, rfl⟩)
  · rfl

theorem memAddr?_loc (s : State α) (m : MemOp) : memAddr? ({ s with mem := m' } : State α) m = memAddr? s m := rfl
theorem gx_loc (s : State α) (n : Nat) : gx ({ s with mem := m' } : State α) n = gx s n := rfl

theorem readSrc_loc (s : State α) (lanes : Nat) (b : Src) (h : Agree m' (srcCells s lanes b) s) :
    readSrc rodata ({ s with mem := m' } : State α) lanes b = readSrc rodata s lanes b := by
  cases b with
  | reg n => rfl
  | mem m =>
    simp only [readSrc, memAddr?_loc]
    rcases hm : memAddr? s m with _ | a
    · rfl
    · simp only [Option.bind_some]; exact loadWords_loc rodata m' s a lanes (by simpa [srcCells, memCells, hm] using h)
  | bcst m =>
    simp only [readSrc, memAddr?_loc]
    rcases hm : memAddr? s m with _ | a
    · rfl
    · simp only [Option.bind_some]; rw [loadWords_loc rodata m' s a 1 (by simpa [srcCells, memCells, hm] using h)]

theorem memStoreFrom_in (m1 m2 : Region → Int → α) (r : Region) (q0 : Int) (vs : List α) (r' : Region) (q' : Int)
    (h : ∃ i : Nat, i < vs.length ∧ r' = r ∧ q' = q0 + (i : Int)) :
    memStoreFrom m1 r q0 vs r' q' = memStoreFrom m2 r q0 vs r' q' := by
  induction vs generalizing m1 m2 q0 with
  | nil => obtain ⟨i, hi, _⟩ := h; simp at hi
  | cons v vs ih =>
    simp only [memStoreFrom]
    by_cases ht : ∃ i : Nat, i < vs.length ∧ r' = r ∧ q' = q0 + 1 + (i : Int)
    · exact ih _ _ _ ht
    · have hf : ∀ i : Nat, i < vs.length → ¬ (r' = r ∧ q' = q0 + 1 + (i : Int)) := fun i hi hc => ht ⟨i, hi, hc⟩
      rw [memStoreFrom_frame _ _ _ _ _ _ hf, memStoreFrom_frame _ _ _ _ _ _ hf]
      obtain ⟨i, hi, hr, hq⟩ := h
      rcases i with _ | i
      · simp only [memStore, hr, true_and, show q' = q0 by omega, ↓reduceIte]
      · exact absurd ⟨i, by simp at hi; omega, hr, by omega⟩ ht

theorem memStoreFrom_loc (m1 m2 : Region → Int → α) (r : Region) (q0 : Int) (vs : List α) (r' : Region) (q' : Int) :
    memStoreFrom m1 r q0 vs r' q' =
      if (r', q') ∈ (List.range vs.length).map (fun (i : Nat) => (r, q0 + (i : Int))) then memStoreFrom m2 r q0 vs r' q'
      else m1 r' q' := by
  split
  · rename_i h
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
    obtain ⟨i, hi, hr, hq⟩ := h
    exact memStoreFrom_in _ _ _ _ _ _ _ ⟨i, hi, hr.symm, hq.symm⟩
  · rename_i h
    apply memStoreFrom_frame
    intro i hi hc
    exact h (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, by rw [hc.1, hc.2]⟩)

theorem storeWords_loc (s : State α) (a : Addr) (vs : List α) :
    ({ s with mem := m' } : State α).storeWords a vs =
      (s.storeWords a vs).map (rebase (storeCells a vs.length) m') := by
  simp only [State.storeWords]; split
  · simp only [Option.map_some, rebase, Option.some.injEq]
    congr 1; funext r q
    rw [memStoreFrom_loc m' s.mem a.region (a.off / 8) vs r q]
    simp only [storeCells]
    split
    · rename_i h; simp only [h, ↓reduceIte]
    · rename_i h; simp only [h, ↓reduceIte]
  · rfl

theorem rebase_nil (X : State α) : rebase [] m' X = { X with mem := m' } := by simp [rebase]
@[simp] theorem err_rebase (W) (X : State α) : (rebase W m' X).err = X.err := rfl
theorem next_rebase (W) (X : State α) : next (rebase W m' X) = rebase W m' (next X) := rfl

theorem withMem_loc (s : State α) (m : MemOp) (W : List (Region × Int)) (k k' : Addr → State α)
    (hne : (withMem s m k).err = false)
    (hk : ∀ a, memAddr? s m = some a → (k a).err = false → k' a = rebase W m' (k a)) :
    withMem ({ s with mem := m' } : State α) m k' = rebase W m' (withMem s m k) := by
  simp only [withMem, memAddr?_loc] at hne ⊢
  rcases hx : memAddr? s m with _ | a
  · simp only [hx, fail_err] at hne; simp [State.fail] at hne
  · simp only [hx] at hne ⊢; exact hk a hx hne

theorem withX_loc (s : State α) (n : Nat) (W : List (Region × Int)) (k k' : Addr → State α)
    (hne : (withX s n k).err = false)
    (hk : ∀ a, gx s n = some a → (k a).err = false → k' a = rebase W m' (k a)) :
    withX ({ s with mem := m' } : State α) n k' = rebase W m' (withX s n k) := by
  simp only [withX, gx_loc] at hne ⊢
  rcases hx : gx s n with _ | a
  · simp only [hx, fail_err] at hne; simp [State.fail] at hne
  · simp only [hx] at hne ⊢; exact hk a hx hne

theorem withLoad_loc (s : State α) (a : Addr) (n : Nat) (W : List (Region × Int)) (k k' : List α → State α)
    (hag : Agree m' (storeCells a n) s) (hne : (withLoad rodata s a n k).err = false)
    (hk : ∀ ws, s.loadWords rodata a n = some ws → (k ws).err = false → k' ws = rebase W m' (k ws)) :
    withLoad rodata ({ s with mem := m' } : State α) a n k' = rebase W m' (withLoad rodata s a n k) := by
  simp only [withLoad, loadWords_loc rodata m' s a n hag] at hne ⊢
  rcases hx : s.loadWords rodata a n with _ | ws
  · simp only [hx, fail_err] at hne; simp [State.fail] at hne
  · simp only [hx] at hne ⊢; exact hk ws hx hne

theorem withSrc_loc (s : State α) (lanes : Nat) (b : Src) (W : List (Region × Int)) (k k' : List α → State α)
    (hag : Agree m' (srcCells s lanes b) s) (hne : (withSrc rodata s lanes b k).err = false)
    (hk : ∀ bs, readSrc rodata s lanes b = some bs → (k bs).err = false → k' bs = rebase W m' (k bs)) :
    withSrc rodata ({ s with mem := m' } : State α) lanes b k' = rebase W m' (withSrc rodata s lanes b k) := by
  simp only [withSrc, readSrc_loc rodata m' s lanes b hag] at hne ⊢
  rcases hx : readSrc rodata s lanes b with _ | bs
  · simp only [hx, fail_err] at hne; simp [State.fail] at hne
  · simp only [hx] at hne ⊢; exact hk bs hx hne

theorem withStore_loc (s : State α) (a : Addr) (vs : List α) (W : List (Region × Int)) (k k' : State α → State α)
    (hne : (withStore s a vs k).err = false)
    (hk : ∀ s', s.storeWords a vs = some s' → (k s').err = false →
      k' (rebase (storeCells a vs.length) m' s') = rebase W m' (k s')) :
    withStore ({ s with mem := m' } : State α) a vs k' = rebase W m' (withStore s a vs k) := by
  simp only [withStore, storeWords_loc m' s a vs] at hne ⊢
  rcases hx : s.storeWords a vs with _ | s'
  · simp only [hx, fail_err] at hne; simp [State.fail] at hne
  · simp only [hx, Option.map_some] at hne ⊢; exact hk s' hx hne

theorem readG_loc (s : State α) (b : GSrc) (W : List (Region × Int)) (k k' : α → State α)
    (hag : Agree m' (gsrcCells s b) s) (hne : (readG rodata s b k).err = false)
    (hk : ∀ y, (k y).err = false → k' y = rebase W m' (k y)) :
    readG rodata ({ s with mem := m' } : State α) b k' = rebase W m' (readG rodata s b k) := by
  cases b with
  | reg g => exact hk _ hne
  | imm i => exact hk _ hne
  | mem m =>
    simp only [readG] at hne ⊢
    apply withMem_loc m' s m W _ _ hne
    intro a ha hne2
    apply withLoad_loc rodata m' s a 1 W _ _ (by simpa [gsrcCells, memCells, ha] using hag) hne2
    intro ws _ hne3; exact hk _ hne3


end local_

@[simp] theorem getV_wm (s : State α) (m' : Region → Int → α) (n : Nat) :
    State.getV ({ s with mem := m' } : State α) n = s.getV n := rfl
@[simp] theorem getGD_wm (s : State α) (m' : Region → Int → α) (n : Nat) :
    State.getGD ({ s with mem := m' } : State α) n = s.getGD n := rfl

@[simp] theorem condHolds_wm (s : State α) (m' : Region → Int → α) (c : Cond) :
    condHolds ({ s with mem := m' } : State α) c = condHolds s c := rfl
@[simp] theorem k_wm (s : State α) (m' : Region → Int → α) :
    ({ s with mem := m' } : State α).k = s.k := rfl

syntax "wm_close" : tactic
macro_rules
  | `(tactic| wm_close) => `(tactic| first
    | rfl
    | (split <;> rename_i h <;> (try simp only [h, ↓reduceIte]) <;> wm_close)
    | (simp only [setFlagsSub] <;> wm_close)
    | (simp only [getV_wm, getGD_wm, condHolds_wm, k_wm] <;> wm_close))

section exec_local
variable (rodata : Array (BitVec 64)) (m' : Region → Int → α)

set_option maxHeartbeats 8000000 in
/-- **Memory locality of a step**: run on a state whose memory `m'` agrees with `s` on the cells the
instruction reads, a non-failing step computes the same registers, flags and stored words, and the
cells it does not store to keep `m'`. -/
theorem exec_local (i : Instr) (s : State α) (hh : s.halted = false) (hne : (exec rodata i s).err = false)
    (hag : Agree m' (reads s i) s) :
    exec rodata i ({ s with mem := m' } : State α) = rebase (writes s i) m' (exec rodata i s) := by
  have hT : (s.halted = true) = False := by simp [hh]
  cases i with
  | vmov lanes dst src mask =>
    cases mask <;> (
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes src [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close)
  | vstore lanes m src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withStore_loc m' s ad _ _ _ _ hne2; intro _ _ _
      simp only [List.length_take]; rfl
  | vpxor lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpand lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpandn lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpor lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpaddq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpsllq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | vpsrlq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | vprolq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | vpsllvq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpsrlvq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpternlogq lanes d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpshufb lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpshufd lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | vpblendd lanes d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpalignr lanes d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpunpcklqdq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpunpckhqdq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vperm2i128 d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s 4 b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vinserti128 d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s 2 b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vextracti128 m a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withStore_loc m' s ad _ _ _ _ hne2; intro _ _ _
      simp only [lane128, List.length_cons, List.length_nil]; rfl
  | vshufi64x2 lanes d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpermt2q lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | kmovw k m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro ad had hne2
    rw [read_loc rodata m' s ad.region (ad.off / 8) (fun _ => by
      have := hag (ad.region, ad.off / 8 + ((0 : Nat) : Int)) (by simp [reads, memCells, had, storeCells])
      simpa using this)]
    rw [rebase_nil]; wm_close
  | vzeroupper =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | mov d src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | xchg a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | movi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | lea d m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | add d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | sub d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | andi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | shl d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | dec d =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | xorz d =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | cmpi a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s a [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | cmpr a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s a [] _ _ hne; intro _ _ hne2
    apply withX_loc m' s b [] _ _ hne2; intro _ _ _; rw [rebase_nil]; wm_close
  | cmpm m b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro ad had hne2
    apply withLoad_loc rodata m' s ad 1 [] _ _ (by simpa [reads, memCells, had] using hag) hne2
    intro ws _ hne3
    split
    · rename_i v hv
      simp only [hv] at hne3
      apply withX_loc m' s b [] _ _ hne3; intro _ _ _; rw [rebase_nil]; wm_close
    · rename_i hv; simp only [hv] at hne3; simp [State.fail] at hne3
  | cmprm a m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro ad had hne2
    apply withLoad_loc rodata m' s ad 1 [] _ _ (by simpa [reads, memCells, had] using hag) hne2
    intro ws _ hne3
    split
    · rename_i v hv
      simp only [hv] at hne3
      apply withX_loc m' s a [] _ _ hne3; intro _ _ _; rw [rebase_nil]; wm_close
    · rename_i hv; simp only [hv] at hne3; simp [State.fail] at hne3
  | test a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s a [] _ _ hne; intro _ _ hne2
    apply withX_loc m' s b [] _ _ hne2; intro _ _ _; rw [rebase_nil]; wm_close
  | bt a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    show (match LaneOps.asConst (s.getGD a) with | some w => withX ({ s with mem := m' } : State α) b _ | none => _) = _
    rcases hc : LaneOps.asConst (s.getGD a) with _ | w
    · simp only [hc] at hne; simp [State.fail] at hne
    · simp only [hc] at hne ⊢
      apply withX_loc m' s b [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | btc a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | alu op d b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply readG_loc rodata m' s b [] _ _ hag hne; intro _ _; rw [rebase_nil]; wm_close
  | andn d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply readG_loc rodata m' s b [] _ _ hag hne; intro _ _; rw [rebase_nil]; wm_close
  | rorx d b imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply readG_loc rodata m' s b [] _ _ hag hne; intro _ _; rw [rebase_nil]; wm_close
  | xorm m src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withLoad_loc rodata m' s ad 1 _ _ _ (by simpa [reads, memCells, hm] using hag) hne2; intro ws _ hne3
      apply withStore_loc m' s ad _ _ _ _ hne3 <;> intro _ _ _ <;> rfl
  | storeqi m imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withStore_loc m' s ad _ _ _ _ hne2 <;> intro _ _ _ <;> rfl
  | addm m imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withLoad_loc rodata m' s ad 1 _ _ _ (by simpa [reads, memCells, hm] using hag) hne2; intro ws _ hne3
      apply withStore_loc m' s ad _ _ _ _ hne3 <;> intro _ _ _ <;> rfl
  | decm m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withLoad_loc rodata m' s ad 1 _ _ _ (by simpa [reads, memCells, hm] using hag) hne2; intro ws _ hne3
      split
      · rename_i v hv
        simp only [hv] at hne3
        split
        · rename_i hr; simp only [hr, ↓reduceIte] at hne3 ⊢
          apply withStore_loc m' s ad _ _ _ _ hne3 <;> intro _ _ _ <;> rfl
        · rename_i hr; simp only [hr, ↓reduceIte] at hne3; simp [State.fail] at hne3
      · rename_i hv; simp only [hv] at hne3; simp [State.fail] at hne3
  | jcc c t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | jmp t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | jcct c name =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | call t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hsp : gx s 4 with _ | sp
    · simp only [withX, gx_loc, hsp, fail_err] at hne; simp [State.fail] at hne
    · simp only [hsp]
      apply withX_loc m' s 4 _ _ _ hne; intro sp' hsp' hne2
      rw [hsp] at hsp'; cases hsp'
      apply withStore_loc m' s _ _ _ _ _ hne2 <;> intro _ _ _ <;> rfl
  | ret =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    by_cases hd : s.depth = 0
    · simp only [hd, ↓reduceIte] at hne ⊢ <;> rw [rebase_nil] <;> rfl
    · simp only [show ({ s with mem := m' } : State α).depth = s.depth from rfl, hd, ↓reduceIte] at hne ⊢
      apply withX_loc m' s 4 [] _ _ hne; intro sp hsp hne2
      apply withLoad_loc rodata m' s sp 1 [] _ _ (by simpa [reads, hd, hsp] using hag) hne2
      intro ws _ hne3; rw [rebase_nil]; wm_close
  | push src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hsp : gx s 4 with _ | sp
    · simp only [withX, gx_loc, hsp, fail_err] at hne; simp [State.fail] at hne
    · simp only [hsp]
      apply withX_loc m' s 4 _ _ _ hne; intro sp' hsp' hne2
      rw [hsp] at hsp'; cases hsp'
      apply withStore_loc m' s _ _ _ _ _ hne2 <;> intro _ _ _ <;> rfl
  | pop d =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s 4 [] _ _ hne; intro sp hsp hne2
    apply withLoad_loc rodata m' s sp 1 [] _ _ (by simpa [reads, hsp] using hag) hne2
    intro _ _ _; rw [rebase_nil]; wm_close
  | storeq m src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withStore_loc m' s ad _ _ _ _ hne2 <;> intro _ _ _ <;> rfl
  | loadq d m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro ad had hne2
    apply withLoad_loc rodata m' s ad 1 [] _ _ (by simpa [reads, memCells, had] using hag) hne2
    intro _ _ _; rw [rebase_nil]; wm_close
  | repmovsb =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hn : gx s 1 with _ | n
    · simp only [withX, gx_loc, hn, fail_err] at hne; simp [State.fail] at hne
    rcases hsrc : gx s 6 with _ | src
    · simp only [withX, gx_loc, hn, hsrc, fail_err] at hne; simp [State.fail] at hne
    rcases hdst : gx s 7 with _ | dst
    · simp only [withX, gx_loc, hn, hsrc, hdst, fail_err] at hne; simp [State.fail] at hne
    simp only [withX, gx_loc, hn, hsrc, hdst] at hne ⊢
    simp only [repBody] at hne ⊢
    split
    · rename_i hc
      simp only [hc, and_self, ↓reduceIte] at hne
      apply withLoad_loc rodata m' s src _ _ _ _ (by simpa [reads, hn, hsrc] using hag) hne; intro vs hvs hne3
      have hlen : vs.length = n.off.toNat / 8 := by
        simp only [State.loadWords] at hvs; split at hvs
        · cases hvs; simp
        · cases hvs
      apply withStore_loc m' s dst vs _ _ _ hne3; intro _ _ _; rw [hlen]; rfl
    · rename_i hc; simp only [hc, ↓reduceIte] at hne; simp [State.fail] at hne
  | tailcall name =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | nop =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close

end exec_local

end X86
end Keccaktree.Asm

/-! ## The aliased machine and the simulation -/
namespace Keccaktree.Asm
open X86
namespace X86
variable {α : Type} [LaneOps α]

/-- The memory as an aliased machine sees it: region 2 (output) is a view of region 1 (input),
offsets coinciding (`out == in`). -/
def joinMem (m : Region → Int → α) : Region → Int → α :=
  fun r q => if r = rOutput then m rInput q else m r q

/-- **One step of the aliased machine** (`keccaktree_hash(buf, buf, n)`): the step runs on the joined
view (loads through either pointer see the storage, region 1), and the words it stores through the
output pointer land in the storage. -/
def execAl (rodata : Array (BitVec 64)) (i : Instr) (t : State α) : State α :=
  if t.halted then t else
  let s := { t with mem := joinMem t.mem }
  let s' := exec rodata i s
  { s' with mem := fun r q => if r = rInput ∧ (rOutput, q) ∈ writes s i then s'.mem rOutput q else s'.mem r q }

/-- The aliased machine's fetch-execute loop. -/
def runAl (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → State α → State α
  | 0, t => t
  | n + 1, t => if t.halted then t else runAl rodata prog n (execAl rodata (prog.getD t.pc .nop) t)

/-- The aliased state `t` corresponds to the separate-region state `s`: same registers and control,
the storage (region 1 of `t`) holds what `s` has in its output region, the other regions agree
(region 2 of `t` is never read: `execAl` reads through the joined view). -/
def Sim (s t : State α) : Prop :=
  t.v = s.v ∧ t.g = s.g ∧ t.gd = s.gd ∧ t.k = s.k ∧ t.zf = s.zf ∧ t.cf = s.cf ∧ t.nf = s.nf ∧ t.vf = s.vf ∧
  t.vl = s.vl ∧ t.pc = s.pc ∧ t.depth = s.depth ∧ t.err = s.err ∧ t.halted = s.halted ∧ t.tail = s.tail ∧
  (∀ q, t.mem rInput q = s.mem rOutput q) ∧ (∀ r q, r ≠ rInput → r ≠ rOutput → t.mem r q = s.mem r q)

/-- Above `B` the output region of `s` still holds the input (nothing stored there yet). -/
def Clean (B : Int) (s : State α) : Prop := ∀ q, B ≤ q → s.mem rOutput q = s.mem rInput q

/-- What a step of the separate-region run must respect for the aliased run to follow it: it loads
input words only at or above `B` (where the storage still holds the input), and stores no input word. -/
def AccessOk (B : Int) (s : State α) (i : Instr) : Prop :=
  (∀ c ∈ reads s i, c.1 = rInput → B ≤ c.2) ∧ (∀ c ∈ writes s i, c.1 ≠ rInput)

/-- The bound after a step: above every output word stored so far. -/
def bumpB (B : Int) (s : State α) (i : Instr) : Int :=
  (writes s i).foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) B

theorem foldB_ge (l : List (Region × Int)) (B : Int) :
    B ≤ l.foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) B := by
  induction l generalizing B with
  | nil => exact Int.le_refl _
  | cons c l ih =>
    simp only [List.foldl_cons]
    refine Int.le_trans ?_ (ih _)
    split <;> omega

theorem bumpB_ge (B : Int) (s : State α) (i : Instr) : B ≤ bumpB B s i := foldB_ge _ _

theorem foldB_out (l : List (Region × Int)) (B q : Int) (hq : (rOutput, q) ∈ l) :
    q < l.foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) B := by
  induction l generalizing B with
  | nil => simp at hq
  | cons c l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hq with h | h
    · subst h
      have h1 := foldB_ge l (max B (q + 1))
      have h2 : (if (rOutput, q).1 = rOutput then max B ((rOutput, q).2 + 1) else B) = max B (q + 1) := by simp
      rw [h2]
      omega
    · exact ih _ h

theorem bumpB_out (B : Int) (s : State α) (i : Instr) (q : Int) (hq : (rOutput, q) ∈ writes s i) : q < bumpB B s i :=
  foldB_out _ _ _ hq

theorem writes_wm (s : State α) (m' : Region → Int → α) (i : Instr) :
    writes ({ s with mem := m' } : State α) i = writes s i := by
  cases i <;> rfl

theorem joined_eq (s t : State α) (h : Sim s t) :
    ({ t with mem := joinMem t.mem } : State α) = { s with mem := joinMem t.mem } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -⟩ := h
  cases t; cases s; simp_all

theorem execAl_eq (rodata : Array (BitVec 64)) (i : Instr) (t : State α) (hth : t.halted = false) :
    execAl rodata i t =
      { exec rodata i ({ t with mem := joinMem t.mem } : State α) with
        mem := fun r q => if r = rInput ∧ (rOutput, q) ∈ writes ({ t with mem := joinMem t.mem } : State α) i
          then (exec rodata i ({ t with mem := joinMem t.mem } : State α)).mem rOutput q
          else (exec rodata i ({ t with mem := joinMem t.mem } : State α)).mem r q } := by
  simp only [execAl, hth, Bool.false_eq_true, ↓reduceIte]

set_option maxHeartbeats 4000000 in
/-- **One step of the simulation**: if the separate-region step loads input words only where the
output region still holds the input, the aliased step follows it. -/
theorem sim_step (rodata : Array (BitVec 64)) (i : Instr) (s t : State α) (B : Int)
    (hS : Sim s t) (hC : Clean B s) (hA : AccessOk B s i) (hh : s.halted = false)
    (hne : (exec rodata i s).err = false) :
    Sim (exec rodata i s) (execAl rodata i t) ∧ Clean (bumpB B s i) (exec rodata i s) := by
  have hth : t.halted = false := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hh
  have hmIn := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmOt := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hag : Agree (joinMem t.mem) (reads s i) s := by
    rintro ⟨r, q⟩ hc
    simp only [joinMem]
    by_cases h2 : r = rOutput
    · subst h2; simp only [↓reduceIte]; exact hmIn q
    · simp only [h2, ↓reduceIte]
      by_cases h1 : r = rInput
      · subst h1; rw [hmIn q]; exact hC q (hA.1 _ hc rfl)
      · exact hmOt r q h1 h2
  have hloc := exec_local rodata (joinMem t.mem) i s hh hne hag
  have hfr := exec_frame rodata i s hne
  rw [execAl_eq rodata i t hth, joined_eq s t hS, writes_wm, hloc]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -⟩ := hS
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
  · intro q
    simp only [rebase, true_and]
    split
    · rename_i hw; simp only [hw, ↓reduceIte]
    · rename_i hw
      have hw1 : (rInput, q) ∉ writes s i := fun h => hA.2 _ h rfl
      simp only [hw1, ↓reduceIte, joinMem, show rInput ≠ rOutput by decide]
      rw [hmIn q, hfr rOutput q hw]
  · intro r q hr1 hr2
    simp only [rebase, hr1, false_and, ↓reduceIte]
    split
    · rfl
    · rename_i hw; simp only [joinMem, hr2, ↓reduceIte]; rw [hmOt r q hr1 hr2, hfr r q hw]
  · intro q hq
    have hw2 : (rOutput, q) ∉ writes s i := fun h => by have := bumpB_out B s i q h; omega
    have hw1 : (rInput, q) ∉ writes s i := fun h => hA.2 _ h rfl
    rw [hfr _ _ hw2, hfr _ _ hw1]
    exact hC q (Int.le_trans (bumpB_ge B s i) hq)

/-- The access condition along a separate-region run of `n` steps from `s`, starting at bound `B`;
when the run stops (halted, or `n` steps done) the bound is at most `Bf`. -/
def AccessRun (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → Int → Int → State α → Prop
  | 0, B, Bf, _ => B ≤ Bf
  | n + 1, B, Bf, s => if s.halted then B ≤ Bf else
      ((exec rodata (prog.getD s.pc .nop) s).err = false ∧ AccessOk B s (prog.getD s.pc .nop) ∧
        AccessRun rodata prog n (bumpB B s (prog.getD s.pc .nop)) Bf (exec rodata (prog.getD s.pc .nop) s))

theorem clean_mono (B B' : Int) (s : State α) (h : B ≤ B') (hC : Clean B s) : Clean B' s :=
  fun q hq => hC q (Int.le_trans h hq)

/-- **The simulation along a run**: the aliased run follows the separate-region run, and at the end
the output region of the latter still holds the input above `Bf`. -/
theorem sim_run (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (B Bf : Int) (s t : State α), AccessRun rodata prog n B Bf s → Sim s t → Clean B s →
      Sim (X86.isa.run rodata prog n s) (runAl rodata prog n t) ∧ Clean Bf (X86.isa.run rodata prog n s) ∧
      ∀ q, (X86.isa.run rodata prog n s).mem rInput q = s.mem rInput q := by
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
      have hst := sim_step rodata (prog.getD s.pc .nop) s t B hS hC hok hh hne
      show Sim (if s.halted then s else X86.isa.run rodata prog n (X86.exec rodata (prog.getD s.pc .nop) s))
        (if t.halted then t else runAl rodata prog n (execAl rodata (prog.getD t.pc .nop) t)) ∧
        Clean Bf (if s.halted then s else X86.isa.run rodata prog n (X86.exec rodata (prog.getD s.pc .nop) s)) ∧
        ∀ q, (if s.halted then s else X86.isa.run rodata prog n (X86.exec rodata (prog.getD s.pc .nop) s)).mem rInput q =
          s.mem rInput q
      rw [hth, hh, htpc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ hA hst.1 hst.2
      refine ⟨h1, h2, fun q => (h3 q).trans ?_⟩
      exact exec_frame rodata _ s hne rInput q (fun hw => hok.2 _ hw rfl)
    · simp only [AccessRun, hh, ↓reduceIte] at hA
      rw [Isa.run_halted _ _ _ _ _ hh]
      simp only [runAl, hth, hh, ↓reduceIte]; exact ⟨hS, clean_mono _ _ _ hA hC, fun _ => trivial⟩

/-- The separate-region state an aliased state starts from: the output region holds the storage too. -/
def dupState (t : State α) : State α :=
  { t with mem := fun r q => if r = rOutput then t.mem rInput q else t.mem r q }

theorem sim_dup (t : State α) : Sim (dupState t) t := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_, fun r q h1 h2 => ?_⟩
  · simp [dupState]
  · simp [dupState, h2]

theorem clean_dup (t : State α) (B : Int) : Clean B (dupState t) := by
  intro q _; simp [dupState, show rInput ≠ rOutput by decide]

theorem bumpB_mono (B B' : Int) (s : State α) (i : Instr) (h : B' ≤ B) : bumpB B' s i ≤ bumpB B s i := by
  unfold bumpB
  generalize writes s i = l
  induction l generalizing B B' with
  | nil => exact h
  | cons c l ih2 => simp only [List.foldl_cons]; apply ih2; split <;> omega

theorem accessRun_mono (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (B B' Bf : Int) (s : State α), B' ≤ B → AccessRun rodata prog n B Bf s → AccessRun rodata prog n B' Bf s := by
  intro n
  induction n with
  | zero => intro B B' Bf s hB hA; exact Int.le_trans hB hA
  | succ n ih =>
    intro B B' Bf s hB hA
    cases hh : s.halted
    · simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte] at hA ⊢
      obtain ⟨hne, hok, hA⟩ := hA
      exact ⟨hne, ⟨fun c hc hr => Int.le_trans hB (hok.1 c hc hr), hok.2⟩, ih _ _ _ _ (bumpB_mono _ _ _ _ hB) hA⟩
    · simp only [AccessRun, hh, ↓reduceIte] at hA ⊢
      exact Int.le_trans hB hA

end X86
end Keccaktree.Asm

/-! ## A checker for the access condition (concrete runs) -/
namespace Keccaktree.Asm
open X86
namespace X86

/-- `AccessRun` as a Boolean function on concrete states. -/
def accessCheck (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → Int → Int → State (BitVec 64) → Bool
  | 0, B, Bf, _ => decide (B ≤ Bf)
  | n + 1, B, Bf, s => if s.halted then decide (B ≤ Bf) else
      !(exec rodata (prog.getD s.pc .nop) s).err &&
      (reads s (prog.getD s.pc .nop)).all (fun c => c.1 != rInput || decide (B ≤ c.2)) &&
      (writes s (prog.getD s.pc .nop)).all (fun c => c.1 != rInput) &&
      accessCheck rodata prog n (bumpB B s (prog.getD s.pc .nop)) Bf (exec rodata (prog.getD s.pc .nop) s)

theorem accessCheck_sound (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (B Bf : Int) (s : State (BitVec 64)), accessCheck rodata prog n B Bf s = true →
      AccessRun rodata prog n B Bf s := by
  intro n
  induction n with
  | zero => intro B Bf s h; simp only [accessCheck, decide_eq_true_eq] at h; exact h
  | succ n ih =>
    intro B Bf s h
    cases hh : s.halted
    · simp only [accessCheck, hh, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true',
        List.all_eq_true] at h
      obtain ⟨⟨⟨he, hr⟩, hw⟩, hA⟩ := h
      simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte]
      refine ⟨he, ⟨fun c hc hrc => ?_, fun c hc hrc => ?_⟩, ih _ _ _ hA⟩
      · have := hr c hc; simp only [hrc, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at this; exact this
      · have := hw c hc; simp [hrc] at this
    · simp only [accessCheck, hh, ↓reduceIte, decide_eq_true_eq] at h
      simp only [AccessRun, hh, ↓reduceIte]; exact h

end X86
end Keccaktree.Asm
