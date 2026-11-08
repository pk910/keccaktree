import Keccaktree.Asm.Footprint
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# In-place hashing: aliased input and output (base definitions)

`keccaktree_hash(out, in, count)` may be called with `out == in`.  The model keeps the input and
the output in two regions; on the machine, with `out == in`, region-2 offset `o` and region-1
offset `o` are the same bytes.

* `reads s i`: the memory cells an instruction loads (from the state before it), the
  counterpart of `Footprint.writes`.
* **`exec_local`**: an instruction depends on memory only through the cells it reads: run on a
  state whose memory differs elsewhere, it computes the same registers, flags and stored words,
  and leaves the other cells as they were.

This file holds what does not depend on the x86 step function (`rebase`, `Agree`, the locality
lemmas of the state operations, the joined view `joinMem`, `Sim`, `Clean`, `Mirror`, `dupState`):
the AArch64/RISC-V development (`AliasGen.lean`, `AliasIsa.lean`) builds on it alone.  `Alias.lean`:
the x86 step (`exec_local`), the x86 aliased machine and access condition.
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


/-! ## The aliased machine: views and the simulation relation -/
/-- The memory as an aliased machine sees it: region 2 (output) is a view of region 1 (input),
offsets coinciding (`out == in`). -/
def joinMem (m : Region → Int → α) : Region → Int → α :=
  fun r q => if r = rOutput then m rInput q else m r q

/-- The aliased state `t` corresponds to the separate-region state `s`: same registers and control,
the storage (regions 1 and 2 of `t`, one buffer) holds what `s` has in its output region, the other
regions agree. -/
def Sim (s t : State α) : Prop :=
  t.v = s.v ∧ t.g = s.g ∧ t.gd = s.gd ∧ t.k = s.k ∧ t.zf = s.zf ∧ t.cf = s.cf ∧ t.nf = s.nf ∧ t.vf = s.vf ∧
  t.vl = s.vl ∧ t.pc = s.pc ∧ t.depth = s.depth ∧ t.err = s.err ∧ t.halted = s.halted ∧ t.tail = s.tail ∧
  (∀ q, t.mem rInput q = s.mem rOutput q) ∧ (∀ q, t.mem rOutput q = s.mem rOutput q) ∧
  (∀ r q, r ≠ rInput → r ≠ rOutput → t.mem r q = s.mem r q)

/-- Above `B` the output region of `s` still holds the input (nothing stored there yet). -/
def Clean (B : Int) (s : State α) : Prop := ∀ q, B ≤ q → s.mem rOutput q = s.mem rInput q

theorem foldB_ge (l : List (Region × Int)) (B : Int) :
    B ≤ l.foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) B := by
  induction l generalizing B with
  | nil => exact Int.le_refl _
  | cons c l ih =>
    simp only [List.foldl_cons]
    refine Int.le_trans ?_ (ih _)
    split <;> omega

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

theorem joined_eq (s t : State α) (h : Sim s t) :
    ({ t with mem := joinMem t.mem } : State α) = { s with mem := joinMem t.mem } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -⟩ := h
  cases t; cases s; simp_all

theorem clean_mono (B B' : Int) (s : State α) (h : B ≤ B') (hC : Clean B s) : Clean B' s :=
  fun q hq => hC q (Int.le_trans h hq)

/-- The separate-region state an aliased state starts from: the output region holds the storage too. -/
def dupState (t : State α) : State α :=
  { t with mem := fun r q => if r = rOutput then t.mem rInput q else t.mem r q }

/-- The two views of an aliased state agree (one buffer). -/
def Mirror (t : State α) : Prop := ∀ q, t.mem rOutput q = t.mem rInput q

theorem sim_dup (t : State α) (hm : Mirror t) : Sim (dupState t) t := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_, fun q => ?_, fun r q h1 h2 => ?_⟩
  · simp [dupState]
  · simp [dupState]; exact hm q
  · simp [dupState, h2]

theorem clean_dup (t : State α) (B : Int) : Clean B (dupState t) := by
  intro q _; simp [dupState, show rInput ≠ rOutput by decide]

end X86
end Keccaktree.Asm
