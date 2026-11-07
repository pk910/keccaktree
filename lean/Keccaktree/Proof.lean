import Std.Tactic.BVDecide
import Keccaktree.Spec
import Keccaktree.Generic
import Keccaktree.Asm.RoundLanes
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# keccaktree's portable kernels compute keccak256

`Keccaktree.Generic` (the C `keccak256_generic.c` and the Go
`keccak256_1_generic.go`, transcribed statement by statement) is proved equal
to the FIPS 202 specification `Keccak.Spec` on every input.  Both kernels
keep the lanes 1, 2, 8, 12, 17 and 20 inverted ("lane complementing"), so
the invariant relating them to the standard is `toS a = toState (uncompl a)`.

* `roundC_spec`: the C round macro, on a complemented state and the round
  constant of round `r`, is the standard's `Rnd(A, r)` on the uncomplemented
  state.  Lane by lane: the spec side is unfolded by `round_lane_k`, the
  macro by its `let`s, and `bv_decide` decides the 64-bit identity.
* `nodeC_spec`: round 0 on the sparse initial state, the loop of two-round
  bodies, round 23 and the un-inversion of lanes 1 and 2 at the output give
  `keccak256` of the 64-byte node, byte for byte.
* `nodeGo_spec`: the Go kernel's hand-folded round 0 and its row-0-only
  round 23 compute the same (`round0Go_eq`, `round23Go_eq`, `bv_decide`
  and `rfl`), so it is `keccak256` as well.
-/

namespace Keccaktree.Proof
open Keccaktree.Generic
open Keccak
open Keccak.Spec (State)
open Keccaktree.Asm.X86 (L)

/-- The lane array as a spec state: lane `i = x + 5y` is `A[x][y]`. -/
def toState (a : Lanes) : State := ⟨fun x y => a[x.val + 5 * y.val]⟩

/-- The complemented lanes: 1, 2, 8, 12, 17 and 20 are stored inverted. -/
def complLane (k : Nat) : Bool := k = 1 || k = 2 || k = 8 || k = 12 || k = 17 || k = 20

/-- The state the kernel represents: the complemented lanes inverted back. -/
def uncompl (a : Lanes) : Lanes := Vector.ofFn fun i : Fin 25 => if complLane i.val then ~~~a[i.val] else a[i.val]

/-- The spec state a kernel state represents. -/
def toS (a : Lanes) : State := toState (uncompl a)

theorem L_toState (a : Lanes) (k : Nat) (hk : k < 25) : L (toState a) k = a[k] := by
  simp only [L, toState]
  congr 1; omega

/-- Equality of states, lane by lane (`L A k` for `k = 0 … 24`). -/
theorem ext_L (A B : State) (h : ∀ k, k < 25 → L A k = L B k) : A = B := by
  apply State.ext; intro x y
  have := h (x.val + 5 * y.val) (by omega)
  simp only [L] at this
  have hx : (⟨(x.val + 5 * y.val) % 5, by omega⟩ : Fin 5) = x := Fin.ext (by show (x.val + 5 * y.val) % 5 = x.val; omega)
  have hy : (⟨(x.val + 5 * y.val) / 5 % 5, by omega⟩ : Fin 5) = y := Fin.ext (by show (x.val + 5 * y.val) / 5 % 5 = y.val; omega)
  rw [hx, hy] at this
  exact this

theorem ext25 (A B : State)
    (h : L A 0 = L B 0 ∧ L A 1 = L B 1 ∧ L A 2 = L B 2 ∧ L A 3 = L B 3 ∧ L A 4 = L B 4 ∧
      L A 5 = L B 5 ∧ L A 6 = L B 6 ∧ L A 7 = L B 7 ∧ L A 8 = L B 8 ∧ L A 9 = L B 9 ∧
      L A 10 = L B 10 ∧ L A 11 = L B 11 ∧ L A 12 = L B 12 ∧ L A 13 = L B 13 ∧ L A 14 = L B 14 ∧
      L A 15 = L B 15 ∧ L A 16 = L B 16 ∧ L A 17 = L B 17 ∧ L A 18 = L B 18 ∧ L A 19 = L B 19 ∧
      L A 20 = L B 20 ∧ L A 21 = L B 21 ∧ L A 22 = L B 22 ∧ L A 23 = L B 23 ∧ L A 24 = L B 24) :
    A = B := by
  apply ext_L; intro k hk
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24⟩ := h
  match k with
  | 0 => exact h0 | 1 => exact h1 | 2 => exact h2 | 3 => exact h3 | 4 => exact h4
  | 5 => exact h5 | 6 => exact h6 | 7 => exact h7 | 8 => exact h8 | 9 => exact h9
  | 10 => exact h10 | 11 => exact h11 | 12 => exact h12 | 13 => exact h13 | 14 => exact h14
  | 15 => exact h15 | 16 => exact h16 | 17 => exact h17 | 18 => exact h18 | 19 => exact h19
  | 20 => exact h20 | 21 => exact h21 | 22 => exact h22 | 23 => exact h23 | 24 => exact h24
  | n + 25 => omega

/-- The implementation's and the specification's round constant tables agree. -/
theorem RC_eq (r : Nat) (hr : r < 24) : Generic.RC r = Spec.RC r := by
  match r with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl
  | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl
  | n + 24 => omega

/-- `a[i]` with its bound proof as the proof-free `a[i]!`: `bv_decide`
identifies atoms syntactically, and the same lane reached through different
index computations carries different proof terms. -/
theorem Vector.getElem_eq_getElem! {α n} [Inhabited α] (a : Vector α n) (i : Nat) (h : i < n) :
    a[i] = a[i]! := (getElem!_pos a i h).symm

/-- Unfold the lane reads of `toS` and of the kernel functions down to the
input lanes `a[i]`; the remaining goal is a 64-bit identity for `bv_decide`. -/
macro "lane_unfold" args:(Lean.Parser.Tactic.simpLemma),* : tactic =>
  `(tactic| simp (config := {decide := true}) only [toS, L_toState] <;>
    simp (config := {decide := true}) only [$args,*, uncompl, complLane, Generic.ROL,
      Vector.getElem_ofFn, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, Fin.isValue, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceSub, Nat.reduceLT, Bool.or_eq_true, decide_eq_true_eq, ↓reduceIte, Bool.false_or, Bool.true_or,
      Bool.or_false, Bool.or_true])

macro "lane_atoms" : tactic => `(tactic| try simp only [Vector.getElem_eq_getElem!])

/-! ## One round -/

set_option maxHeartbeats 4000000 in
/-- **The round macro is `Rnd` of FIPS 202** on the represented state, for
every round `r` and every (complemented) state. -/
theorem roundC_spec (r : Nat) (a : Lanes) :
    toS (roundC a (Spec.RC r)) = Spec.round r (toS a) := by
  apply ext25
  simp only [Keccaktree.Asm.X86.round_lane_0, Keccaktree.Asm.X86.round_lane_1,
    Keccaktree.Asm.X86.round_lane_2, Keccaktree.Asm.X86.round_lane_3, Keccaktree.Asm.X86.round_lane_4,
    Keccaktree.Asm.X86.round_lane_5, Keccaktree.Asm.X86.round_lane_6, Keccaktree.Asm.X86.round_lane_7,
    Keccaktree.Asm.X86.round_lane_8, Keccaktree.Asm.X86.round_lane_9, Keccaktree.Asm.X86.round_lane_10,
    Keccaktree.Asm.X86.round_lane_11, Keccaktree.Asm.X86.round_lane_12, Keccaktree.Asm.X86.round_lane_13,
    Keccaktree.Asm.X86.round_lane_14, Keccaktree.Asm.X86.round_lane_15, Keccaktree.Asm.X86.round_lane_16,
    Keccaktree.Asm.X86.round_lane_17, Keccaktree.Asm.X86.round_lane_18, Keccaktree.Asm.X86.round_lane_19,
    Keccaktree.Asm.X86.round_lane_20, Keccaktree.Asm.X86.round_lane_21, Keccaktree.Asm.X86.round_lane_22,
    Keccaktree.Asm.X86.round_lane_23, Keccaktree.Asm.X86.round_lane_24]
  lane_unfold roundC
  lane_atoms
  repeat' apply And.intro
  all_goals bv_decide

/-! ## The permutation -/

theorem loopC_spec (k : Nat) : ∀ (r : Nat) (e : Lanes) (A : State), toS e = Spec.rounds r A → r + 2 * k ≤ 24 →
    toS (loopC r e k) = Spec.rounds (r + 2 * k) A := by
  induction k with
  | zero => intro r e A h _; simp only [loopC, Nat.mul_zero, Nat.add_zero]; exact h
  | succ k ih =>
    intro r e A h hk
    simp only [loopC]
    have h2 : toS (roundC (roundC e (Generic.RC r)) (Generic.RC (r + 1))) = Spec.rounds (r + 2) A := by
      rw [RC_eq r (by omega), RC_eq (r + 1) (by omega), roundC_spec, roundC_spec, h]
      simp only [Spec.rounds, Spec.memo_eq]
    rw [ih (r + 2) _ A h2 (by omega)]
    congr 1; omega

/-- The 24 rounds of `keccak256_node`: round 0, the loop, round 23. -/
theorem permC_spec (a : Lanes) :
    toS (roundC (loopC 1 (roundC a (Generic.RC 0)) 11) (Generic.RC 23)) = Spec.keccakF (toS a) := by
  have h0 : toS (roundC a (Generic.RC 0)) = Spec.rounds 1 (toS a) := by
    rw [RC_eq 0 (by omega), roundC_spec]; simp only [Spec.rounds, Spec.memo_eq]
  rw [RC_eq 23 (by omega), roundC_spec, loopC_spec 11 1 _ _ h0 (by omega)]
  simp only [Spec.keccakF, Spec.rounds, Spec.memo_eq]

/-! ## The sponge around it -/

theorem absorbC_spec (input : Nat → BitVec 8) :
    toS (absorbC input) = Spec.absorb ⟨fun _ _ => 0#64⟩ (fun i => Spec.padded 64 input (136 * 0 + i)) := by
  apply ext25
  lane_unfold absorbC, Generic.ld64, Spec.absorb, Spec.padded, Spec.paddedLen, Spec.ld64, L
  repeat' apply And.intro
  all_goals bv_decide

theorem st64_eq (v : W) (i : Nat) : st64 v i = v.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [st64, BitVec.extractLsb', BitVec.toNat_ushiftRight]

/-- The digest bytes of `nodeC` are the little-endian bytes of lanes 0..3 of the represented state. -/
theorem nodeC_eq (input : Nat → BitVec 8) (j : Fin 32) :
    (nodeC input)[j] = st64 ((uncompl (roundC (loopC 1 (roundC (absorbC input) (Generic.RC 0)) 11) (Generic.RC 23)))[j.val / 8]'(by omega)) (j.val % 8) := by
  simp only [nodeC, Fin.getElem_fin, Vector.getElem_ofFn]
  generalize roundC (loopC 1 (roundC (absorbC input) (Generic.RC 0)) 11) (Generic.RC 23) = a
  rcases j with ⟨j, hj⟩
  simp only [uncompl, Vector.getElem_ofFn, complLane]
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ => rfl
  | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ => rfl
  | _ + 32, h => exact absurd h (by omega)

theorem toState_lane (a : Lanes) (k : Nat) (h : k < 25) :
    a[k] = toState a ⟨k % 5, by omega⟩ ⟨k / 5 % 5, by omega⟩ := by
  have e : k % 5 + 5 * (k / 5 % 5) = k := by omega
  simp only [toState, e]

/-- **The C node path is keccak256.**  For every 64-byte node and every digest
byte `j < 32`, `keccaktree_keccak256_generic` stores byte `j` of `keccak256(node)`. -/
theorem nodeC_spec (input : Nat → BitVec 8) (j : Fin 32) :
    (nodeC input)[j] = Spec.keccak256 64 input j := by
  rw [nodeC_eq, toState_lane _ (j.val / 8) (by omega), st64_eq]
  have h1 := permC_spec (absorbC input)
  have h2 := absorbC_spec input
  simp only [toS] at h1 h2
  rw [h1, h2]
  simp only [Spec.keccak256, Spec.paddedLen, Spec.absorbBlocks, Spec.squeezeByte,
    Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul]

/-- **The C batch contract.**  `keccaktree_keccak256_generic(output, input, count)`
writes, for every `k < count`, `keccak256(input[64k … 64k+63])` to `output[32k … 32k+31]`. -/
theorem hashC_spec (input : Nat → BitVec 8) (k : Nat) (j : Fin 32) :
    (hashC input k)[j] = Spec.keccak256 64 (fun i => input (64 * k + i)) j :=
  nodeC_spec _ j

/-! ## The Go kernel -/

/-- The node of a chunk pair as one 64-byte input. -/
def pairInput (l r : Nat → BitVec 8) (i : Nat) : BitVec 8 := if i < 32 then l i else r (i - 32)

/-- Pick lane `i < 25` of a `#v[…]` literal and the `let`s of the kernel functions. -/
macro "lane_cases" i:ident hi:ident : tactic =>
  `(tactic| (match $i:ident, $hi:ident with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _
    | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ =>
      simp only [roundC, roundGoEA, roundGoAE, round0Go, round23Go, absorbGo, absorbC, pairInput, Generic.ROL,
        Generic.RC, Generic.ld64, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceIte] <;> bv_decide
    | _ + 25, h => exact absurd h (by omega)))

set_option maxHeartbeats 4000000 in
/-- The two halves of the Go loop body are the round macro. -/
theorem roundGoEA_eq (e : Lanes) (rc : W) : roundGoEA e rc = roundC e rc := by
  apply Vector.ext; intro i hi; lane_cases i hi
set_option maxHeartbeats 4000000 in
theorem roundGoAE_eq (a : Lanes) (rc : W) : roundGoAE a rc = roundC a rc := by
  apply Vector.ext; intro i hi; lane_cases i hi

theorem loopGo_eq (k : Nat) : ∀ r e, loopGo r e k = loopC r e k := by
  induction k with
  | zero => intros; rfl
  | succ k ih => intro r e; simp only [loopGo, loopC, roundGoEA_eq, roundGoAE_eq, ih]

set_option maxHeartbeats 4000000 in
/-- Round 0 as the Go source folds it on the sparse state is the macro on the absorbed state. -/
theorem round0Go_eq (l r : Nat → BitVec 8) :
    round0Go (absorbGo l r) = roundC (absorbC (pairInput l r)) (Generic.RC 0) := by
  apply Vector.ext; intro i hi; lane_cases i hi

/-- Round 23 as the Go source writes it (row 0 only) is row 0 of the macro. -/
theorem round23Go_eq (e : Lanes) (i : Nat) (hi : i < 5) :
    (round23Go e)[i] = (roundC e (Generic.RC 23))[i]'(by omega) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp only [roundC, round23Go, Generic.ROL, Generic.RC, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] <;> bv_decide
  | _ + 5, h => exact absurd h (by omega)

/-- **The Go node path is keccak256.** -/
theorem nodeGo_spec (l r : Nat → BitVec 8) (j : Fin 32) :
    (nodeGo l r)[j] = Spec.keccak256 64 (pairInput l r) j := by
  rw [← nodeC_spec]
  simp only [nodeGo, nodeC, Fin.getElem_fin, Vector.getElem_ofFn, round0Go_eq, loopGo_eq,
    round23Go_eq _ 0 (by omega), round23Go_eq _ 1 (by omega), round23Go_eq _ 2 (by omega),
    round23Go_eq _ 3 (by omega)]

/-- **The Go batch contract.**  `keccak256_1_generic(digests, chunks)`: digest `i` is
`keccak256(chunks[2i] || chunks[2i+1])`. -/
theorem hashGo_spec (chunks : Nat → Nat → BitVec 8) (i : Nat) (j : Fin 32) :
    (hashGo chunks i)[j] = Spec.keccak256 64 (pairInput (chunks (2 * i)) (chunks (2 * i + 1))) j :=
  nodeGo_spec _ _ j

end Keccaktree.Proof
