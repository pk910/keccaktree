import Keccaktree.Kernels.RiscvBytes
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Byte vectors on concrete states (groundwork for the RVV bounce paths)

`vle8`/`vse8` move `vl` bytes between memory and a register group.  On a concrete state:

* `loadBytes_conc`: the `n` words of a byte-vector load at byte address `a` are the words at the byte
  addresses `a + 8j` (`wordAt`), aligned or not;
* `groupWord_setGroup`: word `j` of the register group after the load is the loaded word `j`;
* `byteAt_vstoreMem`: a byte-vector store (`vstoreMem`, aligned or straddling words: `splitWords`)
  writes exactly its `8 n` bytes;
* concrete steps `exec_vsetvlie8_num`, `exec_vle8_conc`, `exec_vse8_conc`, `exec_vsseg_conc`.
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


/-! ## Byte-vector stores -/

theorem memStoreFrom_get (M : Region → Int → BitVec 64) (r : Region) (q0 : Int) (L : List (BitVec 64)) (r' : Region) (q : Int) :
    memStoreFrom M r q0 L r' q = if r' = r ∧ q0 ≤ q ∧ q < q0 + L.length then L.getD (q - q0).toNat 0 else M r' q := by
  induction L generalizing M q0 with
  | nil => simp [memStoreFrom]; intro _ _ _; omega
  | cons v L ih =>
    simp only [memStoreFrom]
    rw [ih]
    simp only [List.length_cons]
    by_cases h1 : r' = r ∧ q0 + 1 ≤ q ∧ q < q0 + 1 + L.length
    · rw [if_pos h1, if_pos ⟨h1.1, by omega, by push_cast; omega⟩]
      rw [show (q - q0).toNat = (q - (q0 + 1)).toNat + 1 by omega, List.getD_cons_succ]
    · rw [if_neg h1]
      unfold memStore
      by_cases h2 : r' = r ∧ q = q0
      · rw [if_pos h2, if_pos ⟨h2.1, by omega, by push_cast; omega⟩, show (q - q0).toNat = 0 by omega, List.getD_cons_zero]
      · rw [if_neg h2, if_neg]
        rintro ⟨h3, h4, h5⟩
        push_cast at h5
        by_cases hq : q = q0
        · exact h2 ⟨h3, hq⟩
        · exact h1 ⟨h3, by omega, by omega⟩

theorem cases7 (k : Nat) (h1 : 0 < k) (h : k < 8) : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega

theorem mid_byte (x y : BitVec 64) (k t : Nat) (hk1 : 0 < k) (hk : k < 8) (ht : t < 8) :
    ((x >>> (64 - 8 * k)) ||| (y <<< (8 * k))).extractLsb' (8 * t) 8 =
      if t < k then x.extractLsb' (8 * (t + 8 - k)) 8 else y.extractLsb' (8 * (t - k)) 8 := by
  rcases cases7 k hk1 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cases8 t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> bv_decide

theorem lo_byte (lo y : BitVec 64) (k t : Nat) (hk1 : 0 < k) (hk : k < 8) (ht : t < 8) :
    ((lo &&& (BitVec.allOnes 64 >>> (64 - 8 * k))) ||| (y <<< (8 * k))).extractLsb' (8 * t) 8 =
      if t < k then lo.extractLsb' (8 * t) 8 else y.extractLsb' (8 * (t - k)) 8 := by
  rcases cases7 k hk1 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cases8 t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> bv_decide

theorem hi_byte (x hi : BitVec 64) (k t : Nat) (hk1 : 0 < k) (hk : k < 8) (ht : t < 8) :
    ((x >>> (64 - 8 * k)) ||| (hi &&& ~~~(BitVec.allOnes 64 >>> (64 - 8 * k)))).extractLsb' (8 * t) 8 =
      if t < k then x.extractLsb' (8 * (t + 8 - k)) 8 else hi.extractLsb' (8 * t) 8 := by
  rcases cases7 k hk1 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cases8 t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> bv_decide

theorem splitWords_getD (k : Nat) (lo hi : BitVec 64) (vs : List (BitVec 64)) (n i : Nat) (hi' : i ≤ n) :
    (splitWords k lo hi vs n).getD i 0 =
      (if i = 0 then lo &&& (BitVec.allOnes 64 >>> (64 - 8 * k)) else vs.getD (i - 1) 0 >>> (64 - 8 * k)) |||
      (if i = n then hi &&& ~~~(BitVec.allOnes 64 >>> (64 - 8 * k)) else vs.getD i 0 <<< (8 * k)) := by
  unfold splitWords
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  rfl

/-- The memory after a byte-vector store of the `n` words `vs` at byte address `a`. -/
def vstoreMem (M : Region → Int → BitVec 64) (a : Addr) (vs : List (BitVec 64)) (n : Nat) : Region → Int → BitVec 64 :=
  if byteOf a = 0 then memStoreFrom M a.region (a.off / 8) vs
  else memStoreFrom M a.region (a.off / 8) (splitWords (byteOf a) (M a.region (a.off / 8)) (M a.region (a.off / 8 + n)) vs n)

set_option maxHeartbeats 4000000 in
/-- **A byte-vector store writes exactly its `8 n` bytes**, at any byte address. -/
theorem byteAt_vstoreMem (M : Region → Int → BitVec 64) (a : Addr) (vs : List (BitVec 64)) (n : Nat) (hn : vs.length = n)
    (hn1 : 1 ≤ n) (r' : Region) (b : Int) :
    byteAt (vstoreMem M a vs n r') b = if r' = a.region ∧ a.off ≤ b ∧ b < a.off + 8 * n then
      (vs.getD ((b - a.off) / 8).toNat 0).extractLsb' (8 * ((b - a.off) % 8).toNat) 8 else byteAt (M r') b := by
  unfold byteAt vstoreMem
  by_cases hk : byteOf a = 0
  · have h0 : a.off % 8 = 0 := by unfold byteOf at hk; omega
    rw [if_pos hk, memStoreFrom_get, hn]
    by_cases hin : r' = a.region ∧ a.off ≤ b ∧ b < a.off + 8 * n
    · rw [if_pos ⟨hin.1, by omega, by omega⟩, if_pos hin]
      rw [show (b / 8 - a.off / 8).toNat = ((b - a.off) / 8).toNat by omega,
        show (b % 8).toNat = ((b - a.off) % 8).toNat by omega]
    · rw [if_neg hin, if_neg]
      rintro ⟨h1, h2, h3⟩
      exact hin ⟨h1, by omega, by omega⟩
  · have hk8 : byteOf a < 8 := by unfold byteOf; omega
    have hk1 : 0 < byteOf a := by omega
    have hka : (a.off % 8).toNat = byteOf a := rfl
    rw [if_neg hk, memStoreFrom_get]
    simp only [splitWords, List.length_map, List.length_range]
    by_cases hr : r' = a.region
    · subst hr
      by_cases hq : a.off / 8 ≤ b / 8 ∧ b / 8 < a.off / 8 + ((n + 1 : Nat) : Int)
      · rw [if_pos ⟨rfl, hq⟩]
        have hgd := splitWords_getD (byteOf a) (M a.region (a.off / 8)) (M a.region (a.off / 8 + n)) vs n
          (b / 8 - a.off / 8).toNat (by omega)
        unfold splitWords at hgd
        rw [hgd]
        have ht8 : (b % 8).toNat < 8 := by omega
        generalize hi : (b / 8 - a.off / 8).toNat = i at *
        by_cases hi0 : i = 0
        · rw [if_pos hi0, if_neg (by omega), lo_byte _ _ _ _ hk1 hk8 ht8]
          by_cases ht : (b % 8).toNat < byteOf a
          · rw [if_pos ht, if_neg (by omega)]
            congr 2; omega
          · rw [if_neg ht, if_pos (show a.region = a.region ∧ a.off ≤ b ∧ b < a.off + 8 * (n : Int) from ⟨rfl, by omega, by omega⟩), hi0]
            rw [show ((b - a.off) / 8).toNat = 0 by omega, show ((b - a.off) % 8).toNat = (b % 8).toNat - byteOf a by omega]
        · by_cases hin : i = n
          · rw [if_neg hi0, if_pos hin, hi_byte _ _ _ _ hk1 hk8 ht8]
            by_cases ht : (b % 8).toNat < byteOf a
            · rw [if_pos ht, if_pos (show a.region = a.region ∧ a.off ≤ b ∧ b < a.off + 8 * (n : Int) from ⟨rfl, by omega, by omega⟩),
                show ((b - a.off) / 8).toNat = i - 1 by omega,
                show ((b - a.off) % 8).toNat = (b % 8).toNat + 8 - byteOf a by omega]
            · rw [if_neg ht, if_neg (by omega)]
              rw [show a.off / 8 + (n : Int) = b / 8 by omega]
          · rw [if_neg hi0, if_neg hin, mid_byte _ _ _ _ hk1 hk8 ht8, if_pos (show a.region = a.region ∧ a.off ≤ b ∧ b < a.off + 8 * (n : Int) from ⟨rfl, by omega, by omega⟩)]
            by_cases ht : (b % 8).toNat < byteOf a
            · rw [if_pos ht, show ((b - a.off) / 8).toNat = i - 1 by omega,
                show ((b - a.off) % 8).toNat = (b % 8).toNat + 8 - byteOf a by omega]
            · rw [if_neg ht, show ((b - a.off) / 8).toNat = i by omega,
                show ((b - a.off) % 8).toNat = (b % 8).toNat - byteOf a by omega]
      · rw [if_neg (fun h => hq h.2), if_neg]
        rintro ⟨-, h2, h3⟩
        apply hq; push_cast; omega
    · rw [if_neg (fun h => hr h.1), if_neg (fun h => hr h.1)]

/-! ## Concrete steps of the byte-vector instructions -/

theorem exec_vsetvlie8_num (V : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d a lmul : Nat) (r : Int)
    (hh : S.halted = false) (ha : Riscv.getR S a = gprWord ⟨0, r⟩) (h0 : 0 ≤ r) (h1 : r < 2 ^ 55)
    (hle : r.toNat ≤ 8 * V * lmul) :
    Riscv.exec V rodata (.vsetvlie8 d a lmul) S =
      Riscv.next { Riscv.setR S d (BitVec.ofNat 64 r.toNat) with vl := r.toNat } := by
  simp only [Riscv.exec, hh, Bool.false_eq_true, ↓reduceIte, ha]
  show (if (gprWord ⟨0, r⟩).toNat ≤ 8 * V * lmul then Riscv.next { Riscv.setR S d (BitVec.ofNat 64 (gprWord ⟨0, r⟩).toNat) with
    vl := (gprWord ⟨0, r⟩).toNat } else S.fail) = _
  rw [Riscv.gprWord_num_toNat r h0 h1, if_pos hle]

theorem exec_vle8_conc (V : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d b : Nat) (a : Addr)
    (hh : S.halted = false) (hb : S.getGD b = gprWord a) (hwf : a.wf) (hr : a.region ≠ rRodata) (hv8 : S.vl % 8 = 0)
    (hV : 0 < V) :
    Riscv.exec V rodata (.vle8 d b) S = Riscv.next (setGroup V S d ((List.range (S.vl / 8)).map fun (j : Nat) =>
      wordAt (S.mem a.region) (a.off + 8 * (j : Int))) (S.vl / 8)) := by
  simp only [Riscv.exec, hh, Bool.false_eq_true, ↓reduceIte, Arm.withAddr, addr_zero S b a hb hwf, if_pos (And.intro hv8 hV),
    loadBytes_conc rodata S a hr]

theorem loadWords_hi (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (a : Addr) (hr : a.region ≠ rRodata) (n : Nat) :
    S.loadWords rodata ⟨a.region, (wordOf a).off + 8 * n⟩ 1 = some [S.mem a.region (a.off / 8 + n)] := by
  have h1 : ((⟨a.region, (wordOf a).off + 8 * n⟩ : Addr).off) % 8 = 0 := by simp only [wordOf]; omega
  rw [State.loadWords, if_pos h1]
  simp only [List.range_one, List.map_cons, List.map_nil]
  show some [S.read rodata a.region (((wordOf a).off + 8 * n) / 8 + Int.ofNat 0)] = _
  rw [read_conc rodata S _ hr]
  exact congrArg (fun q => some [S.mem a.region q]) (by simp only [wordOf, Int.ofNat_eq_natCast, Int.natCast_zero]; omega)

theorem exec_vse8_conc (V : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (src b : Nat) (a : Addr)
    (hh : S.halted = false) (hb : S.getGD b = gprWord a) (hwf : a.wf) (hr : a.region ≠ rRodata) (hv8 : S.vl % 8 = 0)
    (hV : 0 < V) (hn : S.vl ≠ 0) :
    Riscv.exec V rodata (.vse8 src b) S =
      Riscv.next { S with mem := (vstoreMem S.mem a ((List.range (S.vl / 8)).map fun j => groupWord V S src j) (S.vl / 8)) } := by
  simp only [Riscv.exec, hh, Bool.false_eq_true, ↓reduceIte, Arm.withAddr, addr_zero S b a hb hwf, if_pos (And.intro hv8 hV),
    if_neg hn]
  unfold Riscv.storeBytes vstoreMem
  by_cases hk : byteOf a = 0
  · have h0 : a.off % 8 = 0 := by unfold byteOf at hk; omega
    simp only [if_pos hk, State.storeWords, if_pos (And.intro h0 hr)]
    rw [hh]
  · rw [if_neg hk, if_neg hk, loadWords_wordOf rodata S a hr, loadWords_hi rodata S a hr]
    simp only
    have h1 : (wordOf a).off % 8 = 0 ∧ (wordOf a).region ≠ rRodata := ⟨by simp only [wordOf]; omega, hr⟩
    rw [State.storeWords, if_pos h1]
    simp only
    rw [show (wordOf a).off / 8 = a.off / 8 by simp only [wordOf]; omega, hh]
    rfl

theorem exec_vsseg_conc (V : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (src b nf : Nat) (a : Addr)
    (hh : S.halted = false) (hb : S.getGD b = gprWord a) (hwf : a.wf) (hr : a.region ≠ rRodata) (h0 : a.off % 8 = 0) :
    Riscv.exec V rodata (.vsseg src b nf) S =
      Riscv.next { S with mem := (memStoreFrom S.mem a.region (a.off / 8) ((List.range (nf * S.vl)).map fun q => lane S (src + q % nf) (q / nf))) } := by
  simp only [Riscv.exec, hh, Bool.false_eq_true, ↓reduceIte, Arm.withAddr, addr_zero S b a hb hwf, State.storeWords,
    if_pos (And.intro h0 hr)]

end Keccaktree.Kernels.RiscvBytes
