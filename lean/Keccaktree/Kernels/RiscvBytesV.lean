import Keccaktree.Kernels.RiscvBytes
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Byte vectors on concrete states (groundwork for the RVV bounce paths)

`vle8`/`vse8` move `vl` bytes between memory and a register group.  On a concrete state:

* `loadBytes_conc`: the `n` words of a byte-vector load at byte address `a` are the words at the byte
  addresses `a + 8j` (`wordAt`), aligned or not;
* `groupWord_setGroup`: word `j` of the register group after the load is the loaded word `j`.
(Still missing for the RVV bounce paths: the bytes written by a misaligned `vse8`, from `splitWords`.)
-/
namespace Keccaktree.Kernels.RiscvBytes
open Keccaktree.Asm Keccaktree.Asm.X86
open Keccaktree.Asm.Riscv (wordOf byteOf loadBytes joinWords splitWords setGroup setLanes groupWord lane)

theorem read_conc (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (r : Region) (hr : r ≠ rRodata) (q : Int) :
    S.read rodata r q = S.mem r q := by
  simp only [State.read, hr, ↓reduceIte]

/-- **The words of a byte-vector load**, at any byte address of a writable region. -/
theorem loadBytes_conc (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (a : Addr) (hr : a.region ≠ rRodata) (n : Nat) :
    loadBytes rodata S a n = some ((List.range n).map fun (j : Nat) => wordAt (S.mem a.region) (a.off + 8 * (j : Int))) := by
  unfold loadBytes
  by_cases hk : byteOf a = 0
  · have h0 : a.off % 8 = 0 := by unfold byteOf at hk; omega
    rw [if_pos hk, State.loadWords, if_pos h0]
    congr 1
    apply List.map_congr_left
    intro j _
    rw [read_conc rodata S _ hr]
    unfold wordAt
    rw [if_pos (by omega)]
    exact congrArg _ (by simp only [Int.ofNat_eq_natCast]; omega)
  · have h0 : a.off % 8 ≠ 0 := by unfold byteOf at hk; omega
    have h1 : (wordOf a).off % 8 = 0 := by simp only [wordOf]; omega
    rw [if_neg hk, State.loadWords, if_pos h1]
    simp only [Option.map_some, Option.some.injEq]
    unfold joinWords
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    have e0 : ∀ i, i < n + 1 → ((List.range (n + 1)).map fun (i : Nat) =>
        S.read rodata (wordOf a).region ((wordOf a).off / 8 + Int.ofNat i)).getD i (LaneOps.const 0) =
        S.mem a.region (a.off / 8 + i) := by
      intro i hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      simp only [Option.map_some, Option.getD_some]
      rw [show (wordOf a).region = a.region from rfl, read_conc rodata S _ hr]
      exact congrArg _ (by simp only [wordOf, Int.ofNat_eq_natCast]; omega)
    rw [e0 j (by omega), e0 (j + 1) (by omega)]
    unfold wordAt
    rw [if_neg (by omega)]
    have e1 : (a.off + 8 * (j : Int)) / 8 = a.off / 8 + j := by omega
    have e2 : ((a.off + 8 * (j : Int)) % 8).toNat = byteOf a := by unfold byteOf; omega
    rw [e1, e2, show a.off / 8 + ((j + 1 : Nat) : Int) = a.off / 8 + (j : Int) + 1 by push_cast; omega]
    rfl

theorem vgetD_eq {β : Type} {n : Nat} (v : Vector β n) (i : Nat) (d : β) : v.getD i d = v[i]?.getD d := by
  show v.toArray.getD i d = _
  rw [Array.getD_eq_getD_getElem?]
  simp

/-- A lane of a register after `setLanes` of another register is unchanged. -/
theorem lane_setLanes_other (s : State (BitVec 64)) (d c : Nat) (f : Nat → BitVec 64) (r l : Nat) (h : r ≠ d) :
    lane (setLanes s d c f) r l = lane s r l := by
  unfold lane setLanes State.getV State.setV
  rw [vgetD_eq, vgetD_eq s.v, Vector.getElem?_setIfInBounds, if_neg (Ne.symm h)]

theorem lane_setLanes_same (s : State (BitVec 64)) (d c : Nat) (f : Nat → BitVec 64) (l : Nat) (hd : d < 32) (hl : l < 8)
    (hc : l < c) : lane (setLanes s d c f) d l = f l := by
  unfold lane setLanes State.getV State.setV
  rw [vgetD_eq, Vector.getElem?_setIfInBounds, if_pos rfl, if_pos hd]
  simp [hl, hc]

theorem lane_foldl_setLanes (vlmax : Nat) (d : Nat) (ws : List (BitVec 64)) (n : Nat) (rr : Nat) :
    ∀ (L : List Nat) (s : State (BitVec 64)), rr ∉ L → ∀ l,
      lane (L.foldl (fun s' r => setLanes s' (d + r) (min vlmax (n - r * vlmax)) fun l =>
        ws.getD (r * vlmax + l) (LaneOps.const 0)) s) (d + rr) l = lane s (d + rr) l
  | [], s, _, l => rfl
  | x :: L, s, h, l => by
    simp only [List.foldl_cons]
    rw [lane_foldl_setLanes vlmax d ws n rr L _ (fun hm => h (List.mem_cons_of_mem _ hm)) l,
      lane_setLanes_other _ _ _ _ _ _ (by intro e; exact h (by simp only [List.mem_cons]; left; omega))]

theorem lane_foldl_setLanes_mem (vlmax : Nat) (d : Nat) (ws : List (BitVec 64)) (n : Nat) (rr l : Nat)
    (hd : d + rr < 32) (hl : l < 8) (hc : l < min vlmax (n - rr * vlmax)) :
    ∀ (L : List Nat) (s : State (BitVec 64)), L.Nodup → rr ∈ L →
      lane (L.foldl (fun s' r => setLanes s' (d + r) (min vlmax (n - r * vlmax)) fun l =>
        ws.getD (r * vlmax + l) (LaneOps.const 0)) s) (d + rr) l = ws.getD (rr * vlmax + l) (LaneOps.const 0)
  | [], s, _, hm => absurd hm List.not_mem_nil
  | x :: L, s, hnd, hm => by
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    by_cases hx : x = rr
    · subst hx
      rw [lane_foldl_setLanes vlmax d ws n x L _ hnd.1 l, lane_setLanes_same _ _ _ _ _ hd hl hc]
    · have hm' : rr ∈ L := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm hx
        · exact h
      exact lane_foldl_setLanes_mem vlmax d ws n rr l hd hl hc L _ hnd.2 hm'

/-- **The register group after a byte-vector load holds the loaded words.** -/
theorem groupWord_setGroup (vlmax : Nat) (hv : 0 < vlmax) (hv8 : vlmax ≤ 8) (s : State (BitVec 64)) (d : Nat)
    (ws : List (BitVec 64)) (n : Nat) (hd : d + (n + vlmax - 1) / vlmax ≤ 32) (j : Nat) (hj : j < n) :
    groupWord vlmax (setGroup vlmax s d ws n) d j = ws.getD j (LaneOps.const 0) := by
  have hm := Nat.mod_lt j hv
  have hdm := Nat.div_add_mod j vlmax
  have hr : j / vlmax < (n + vlmax - 1) / vlmax := by
    apply (Nat.lt_div_iff_mul_lt hv).mpr
    have := Nat.div_mul_le_self j vlmax
    omega
  unfold groupWord setGroup
  rw [lane_foldl_setLanes_mem vlmax d ws n (j / vlmax) (j % vlmax) (by omega) (by omega) ?_ _ s (List.nodup_range)
    (List.mem_range.mpr hr)]
  · rw [show j / vlmax * vlmax + j % vlmax = j by rw [Nat.mul_comm]; omega]
  · simp only [Nat.lt_min]
    refine ⟨hm, ?_⟩
    have : j / vlmax * vlmax + j % vlmax = j := by rw [Nat.mul_comm]; omega
    omega

end Keccaktree.Kernels.RiscvBytes
