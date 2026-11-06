import Std.Tactic.BVDecide
import Keccaktree.Spec
import Keccaktree.Generic
/-!
# keccaktree's portable kernel computes keccak256

`Keccaktree.Generic` (the transliterated `keccak256_generic.c` /
`keccak256_1_generic.go`) is proved equal to the FIPS 202 specification
`Keccak.Spec` on every input:

* `round_spec`: one iteration of the C round loop is the standard's
  `Rnd(A, i) = ι(χ(π(ρ(θ(A)))), i)`, for every round index and every state.
  Both sides are unfolded to straight-line bit-vector terms and decided by
  `bv_decide` (bit-blasting + SAT, with a kernel-checked LRAT certificate).
* `keccakF_spec`: the 24-round loop is Keccak-f[1600] (induction).
* `node_spec`: the 64-byte node path — little-endian loads, the padding
  lanes `a[8] = 0x01`, `a[16] = 1 << 63`, the permutation, and the
  little-endian stores of lanes `0 … 3` — is `keccak256` of those 64 bytes,
  byte for byte.
* `hash_spec`: the batch contract `digest[k] = keccak256(input[64k … 64k+63])`.
-/

namespace Keccaktree.Proof
open Keccaktree.Generic
open Keccak
open Keccak.Spec (State)

/-- The C lane array as a spec state: lane `i = x + 5y` is `A[x][y]`. -/
def _root_.Keccaktree.Generic.Lanes.toState (a : Lanes) : State :=
  ⟨fun x y => a[x.val + 5 * y.val]⟩

/-- Equality of states, lane by lane. -/
theorem State.ext25 (A B : State) : A = B ↔
    (A 0 0 = B 0 0 ∧
    A 1 0 = B 1 0 ∧
    A 2 0 = B 2 0 ∧
    A 3 0 = B 3 0 ∧
    A 4 0 = B 4 0 ∧
    A 0 1 = B 0 1 ∧
    A 1 1 = B 1 1 ∧
    A 2 1 = B 2 1 ∧
    A 3 1 = B 3 1 ∧
    A 4 1 = B 4 1 ∧
    A 0 2 = B 0 2 ∧
    A 1 2 = B 1 2 ∧
    A 2 2 = B 2 2 ∧
    A 3 2 = B 3 2 ∧
    A 4 2 = B 4 2 ∧
    A 0 3 = B 0 3 ∧
    A 1 3 = B 1 3 ∧
    A 2 3 = B 2 3 ∧
    A 3 3 = B 3 3 ∧
    A 4 3 = B 4 3 ∧
    A 0 4 = B 0 4 ∧
    A 1 4 = B 1 4 ∧
    A 2 4 = B 2 4 ∧
    A 3 4 = B 3 4 ∧
    A 4 4 = B 4 4) := by
  constructor
  · intro h; subst h; simp
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ := h
    apply State.ext; intro x y
    match x, y with
    | ⟨0, _⟩, ⟨0, _⟩ => exact h0
    | ⟨1, _⟩, ⟨0, _⟩ => exact h1
    | ⟨2, _⟩, ⟨0, _⟩ => exact h2
    | ⟨3, _⟩, ⟨0, _⟩ => exact h3
    | ⟨4, _⟩, ⟨0, _⟩ => exact h4
    | ⟨0, _⟩, ⟨1, _⟩ => exact h5
    | ⟨1, _⟩, ⟨1, _⟩ => exact h6
    | ⟨2, _⟩, ⟨1, _⟩ => exact h7
    | ⟨3, _⟩, ⟨1, _⟩ => exact h8
    | ⟨4, _⟩, ⟨1, _⟩ => exact h9
    | ⟨0, _⟩, ⟨2, _⟩ => exact h10
    | ⟨1, _⟩, ⟨2, _⟩ => exact h11
    | ⟨2, _⟩, ⟨2, _⟩ => exact h12
    | ⟨3, _⟩, ⟨2, _⟩ => exact h13
    | ⟨4, _⟩, ⟨2, _⟩ => exact h14
    | ⟨0, _⟩, ⟨3, _⟩ => exact h15
    | ⟨1, _⟩, ⟨3, _⟩ => exact h16
    | ⟨2, _⟩, ⟨3, _⟩ => exact h17
    | ⟨3, _⟩, ⟨3, _⟩ => exact h18
    | ⟨4, _⟩, ⟨3, _⟩ => exact h19
    | ⟨0, _⟩, ⟨4, _⟩ => exact h20
    | ⟨1, _⟩, ⟨4, _⟩ => exact h21
    | ⟨2, _⟩, ⟨4, _⟩ => exact h22
    | ⟨3, _⟩, ⟨4, _⟩ => exact h23
    | ⟨4, _⟩, ⟨4, _⟩ => exact h24
    | ⟨_ + 5, hx⟩, _ => exact absurd hx (by omega)
    | _, ⟨_ + 5, hy⟩ => exact absurd hy (by omega)

/-- The implementation's and the specification's round constant tables agree. -/
theorem RC_eq (r : Nat) : Generic.RC r = Spec.RC r := by
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | 16 => rfl
  | 17 => rfl
  | 18 => rfl
  | 19 => rfl
  | 20 => rfl
  | 21 => rfl
  | 22 => rfl
  | 23 => rfl
  | _ + 24 => rfl

/-- `Fin 5` literals as naturals (core `simp` has no general lemma for this). -/
theorem Fin.val_lit0 : ((0 : Fin 5)).val = 0 := rfl
theorem Fin.val_lit1 : ((1 : Fin 5)).val = 1 := rfl
theorem Fin.val_lit2 : ((2 : Fin 5)).val = 2 := rfl
theorem Fin.val_lit3 : ((3 : Fin 5)).val = 3 := rfl
theorem Fin.val_lit4 : ((4 : Fin 5)).val = 4 := rfl

/-! ## One round -/

/-- `a[i]` with its bound proof as the proof-free `a[i]!`: `bv_decide`
identifies atoms syntactically, and the same lane reached through different
index computations carries different proof terms. -/
theorem Vector.getElem_eq_getElem! {α n} [Inhabited α] (a : Vector α n) (i : Nat) (h : i < n) :
    a[i] = a[i]! := (getElem!_pos a i h).symm

/-- Shared `simp` set: unfold one step of the C code and of the spec to
lane expressions, resolve all the literal indices, then drop the bound proofs. -/
macro "lane_simp" args:(Lean.Parser.Tactic.simpLemma),* : tactic =>
  `(tactic| simp (config := {decide := true}) only [$args,*, Lanes.toState, Generic.ROL,
      Vector.getElem_ofFn, Vector.getElem_set_self, Vector.getElem_set_ne,
      Fin.isValue, Fin.reduceAdd, Fin.reduceMul, Fin.reduceSub,
      Fin.val_lit0, Fin.val_lit1, Fin.val_lit2, Fin.val_lit3, Fin.val_lit4,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv])

/-- Drop the bound proofs of the remaining lane reads (see `Vector.getElem_eq_getElem!`). -/
macro "lane_atoms" : tactic => `(tactic| try simp only [Vector.getElem_eq_getElem!])

theorem theta_spec (a : Lanes) : (theta a).toState = Spec.theta a.toState := by
  rw [State.ext25]
  lane_simp Generic.theta, Spec.theta
  all_goals (lane_atoms; bv_decide)

/-! ### rho and pi: the in-place walk along the cycle, by reflection

Unrolling the 24 in-place updates symbolically with `simp` is exponential
(the carried temporary duplicates the update chain), so the loop is run on
symbolic lanes instead: `E` names a lane of the input or a rotation of one,
`loopE` is `rhoPiLoop` on `E`, `loop_eval` (one induction, for any number
of iterations) says that running the C loop on the evaluated lanes is the
same as evaluating the symbolic result, and the kernel computes the
symbolic result of all 24 iterations (`loopE_0 … loopE_24`, each `rfl`):
the lane permutation and rotation the walk implements. -/

namespace RhoPi

inductive E where
  | lane (k : Nat)
  | rol (e : E) (n : Nat)

def E.eval (a : Lanes) : E → W
  | .lane k => a[k]!
  | .rol e n => ROL (e.eval a) n

/-- `rhoPiLoop` on symbolic lanes. -/
def loopE (s : Vector E 25) (t : E) : Nat → Vector E 25
  | 0 => s
  | n + 1 =>
    let i := 24 - (n + 1)
    loopE (s.set (PI i) (.rol t (RHO i)) (PI_lt i)) (s[PI i]'(PI_lt i)) n

/-- The input lanes, symbolically. -/
def sym0 : Vector E 25 := Vector.ofFn fun i => .lane i.val

theorem loop_eval (a : Lanes) (n : Nat) (s : Vector E 25) (t : E) :
    rhoPiLoop (s.map (E.eval a)) (t.eval a) n = (loopE s t n).map (E.eval a) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
    simp only [rhoPiLoop, loopE]
    rw [show ROL (t.eval a) (RHO (24 - (n + 1))) = (E.rol t (RHO (24 - (n + 1)))).eval a from rfl,
      ← Vector.map_set, Vector.getElem_map, ih]

theorem map_sym0 (a : Lanes) : sym0.map (E.eval a) = a := by
  apply Vector.ext; intro i hi
  simp only [sym0, Vector.getElem_map, Vector.getElem_ofFn, E.eval]
  exact getElem!_pos a i hi

theorem rhoPi_eq (a : Lanes) : rhoPi a = (loopE sym0 (.lane 1) 24).map (E.eval a) := by
  have h := loop_eval a 24 sym0 (.lane 1)
  rw [map_sym0] at h
  rw [rhoPi, ← h]
  simp only [E.eval]
  rw [getElem!_pos a 1 (by decide)]

theorem loopE_0 : (loopE sym0 (.lane 1) 24)[0] = .lane 0 := rfl
theorem loopE_1 : (loopE sym0 (.lane 1) 24)[1] = .rol (.lane 6) 44 := rfl
theorem loopE_2 : (loopE sym0 (.lane 1) 24)[2] = .rol (.lane 12) 43 := rfl
theorem loopE_3 : (loopE sym0 (.lane 1) 24)[3] = .rol (.lane 18) 21 := rfl
theorem loopE_4 : (loopE sym0 (.lane 1) 24)[4] = .rol (.lane 24) 14 := rfl
theorem loopE_5 : (loopE sym0 (.lane 1) 24)[5] = .rol (.lane 3) 28 := rfl
theorem loopE_6 : (loopE sym0 (.lane 1) 24)[6] = .rol (.lane 9) 20 := rfl
theorem loopE_7 : (loopE sym0 (.lane 1) 24)[7] = .rol (.lane 10) 3 := rfl
theorem loopE_8 : (loopE sym0 (.lane 1) 24)[8] = .rol (.lane 16) 45 := rfl
theorem loopE_9 : (loopE sym0 (.lane 1) 24)[9] = .rol (.lane 22) 61 := rfl
theorem loopE_10 : (loopE sym0 (.lane 1) 24)[10] = .rol (.lane 1) 1 := rfl
theorem loopE_11 : (loopE sym0 (.lane 1) 24)[11] = .rol (.lane 7) 6 := rfl
theorem loopE_12 : (loopE sym0 (.lane 1) 24)[12] = .rol (.lane 13) 25 := rfl
theorem loopE_13 : (loopE sym0 (.lane 1) 24)[13] = .rol (.lane 19) 8 := rfl
theorem loopE_14 : (loopE sym0 (.lane 1) 24)[14] = .rol (.lane 20) 18 := rfl
theorem loopE_15 : (loopE sym0 (.lane 1) 24)[15] = .rol (.lane 4) 27 := rfl
theorem loopE_16 : (loopE sym0 (.lane 1) 24)[16] = .rol (.lane 5) 36 := rfl
theorem loopE_17 : (loopE sym0 (.lane 1) 24)[17] = .rol (.lane 11) 10 := rfl
theorem loopE_18 : (loopE sym0 (.lane 1) 24)[18] = .rol (.lane 17) 15 := rfl
theorem loopE_19 : (loopE sym0 (.lane 1) 24)[19] = .rol (.lane 23) 56 := rfl
theorem loopE_20 : (loopE sym0 (.lane 1) 24)[20] = .rol (.lane 2) 62 := rfl
theorem loopE_21 : (loopE sym0 (.lane 1) 24)[21] = .rol (.lane 8) 55 := rfl
theorem loopE_22 : (loopE sym0 (.lane 1) 24)[22] = .rol (.lane 14) 39 := rfl
theorem loopE_23 : (loopE sym0 (.lane 1) 24)[23] = .rol (.lane 15) 41 := rfl
theorem loopE_24 : (loopE sym0 (.lane 1) 24)[24] = .rol (.lane 21) 2 := rfl

end RhoPi

/-- The C macro `ROL(x, n) = (x << n) | (x >> (64 - n))` is `BitVec.rotateLeft`
for `n < 64` (`rotateLeft` is defined as `x <<< (n % w) ||| x >>> (w - n % w)`);
stated with the right shift amount as its own variable, since `simp` has
already evaluated `64 - n` when this is used. -/
theorem shifts_eq_rotateLeft (x : W) (n m : Nat) (hn : n < 64) (hm : m + n = 64) :
    x <<< n ||| x >>> m = x.rotateLeft n := by
  have : m = 64 - n := by omega
  subst this
  simp only [BitVec.rotateLeft, BitVec.rotateLeftAux, Nat.mod_eq_of_lt hn]

theorem rotateLeft_zero (x : W) : x.rotateLeft 0 = x := by
  simp only [BitVec.rotateLeft, BitVec.rotateLeftAux, Nat.zero_mod, BitVec.shiftLeft_zero, Nat.sub_zero]
  rw [BitVec.ushiftRight_eq_zero (by omega)]; simp

open RhoPi in
/-- The in-place walk along pi's cycle is rho followed by pi. -/
theorem rhoPi_spec (a : Lanes) : (rhoPi a).toState = Spec.pi (Spec.rho a.toState) := by
  rw [State.ext25]
  simp only [rhoPi_eq, Lanes.toState, Vector.getElem_map,
    Fin.val_lit0, Fin.val_lit1, Fin.val_lit2, Fin.val_lit3, Fin.val_lit4,
    Nat.reduceMul, Nat.reduceAdd, loopE_0, loopE_1, loopE_2, loopE_3, loopE_4, loopE_5, loopE_6, loopE_7, loopE_8, loopE_9, loopE_10, loopE_11, loopE_12, loopE_13, loopE_14, loopE_15, loopE_16, loopE_17, loopE_18, loopE_19, loopE_20, loopE_21, loopE_22, loopE_23, loopE_24, E.eval]
  lane_simp Spec.pi, Spec.rho, Spec.rhoOffset
  lane_atoms
  simp (config := {decide := true}) only [shifts_eq_rotateLeft, rotateLeft_zero, and_self]

theorem chi_spec (a : Lanes) : (chi a).toState = Spec.chi a.toState := by
  rw [State.ext25]
  lane_simp Generic.chi, Spec.chi
  all_goals (lane_atoms; bv_decide)

theorem iota_spec (r : Nat) (a : Lanes) : (iota r a).toState = Spec.iota r a.toState := by
  rw [State.ext25]
  lane_simp Generic.iota, Spec.iota, RC_eq
  all_goals (lane_atoms; bv_decide)

/-- **One round of the C loop is `Rnd` of FIPS 202**, for every round index
and every state. -/
theorem round_spec (r : Nat) (a : Lanes) :
    (Generic.round r a).toState = Spec.round r a.toState := by
  rw [Generic.round, Spec.round, iota_spec, chi_spec, rhoPi_spec, theta_spec]

/-! ## The permutation -/

theorem rounds_spec (a : Lanes) (n : Nat) :
    (Generic.rounds a n).toState = Spec.rounds n a.toState := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Generic.rounds, Spec.rounds, Spec.memo_eq, round_spec, ih]

theorem keccakF_spec (a : Lanes) : (keccakF1600 a).toState = Spec.keccakF a.toState :=
  rounds_spec a 24

/-! ## The sponge around it -/

/-- The state the C code builds before the permutation is the spec's state
after absorbing the padded 64-byte block into the all-zero state. -/
theorem init_spec (input : Nat → BitVec 8) :
    Lanes.toState (((loadLanes (Vector.replicate 25 0#64) input 8 (by decide)).set 8 0x01#64).set 16
        0x8000000000000000#64)
      = Spec.absorb ⟨fun _ _ => 0#64⟩ (fun i => Spec.padded 64 input (136 * 0 + i)) := by
  rw [State.ext25]
  lane_simp Generic.loadLanes, Generic.ld64, Generic.ld64Loop, Spec.absorb, Spec.padded,
    Spec.paddedLen, Spec.ld64, Vector.getElem_replicate
  all_goals (lane_atoms; bv_decide)

theorem toState_lane (a : Lanes) (k : Nat) (h : k < 25) :
    a[k] = a.toState ⟨k % 5, by omega⟩ ⟨k / 5 % 5, by omega⟩ := by
  have e : k % 5 + 5 * (k / 5 % 5) = k := by omega
  simp only [Lanes.toState, e]

theorem st64_eq (v : W) (i : Nat) : st64 v i = v.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [st64, BitVec.extractLsb', BitVec.toNat_ushiftRight]

/-- **The node path is keccak256.**  For every 64-byte node and every digest
byte `j < 32`, `keccaktree_keccak256_generic` stores byte `j` of
`keccak256(node)`. -/
theorem node_spec (input : Nat → BitVec 8) (j : Fin 32) :
    (node input)[j] = Spec.keccak256 64 input j := by
  simp only [node, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [toState_lane _ (j.val / 8) (by omega), keccakF_spec, init_spec, st64_eq]
  simp only [Spec.keccak256, Spec.paddedLen, Spec.absorbBlocks, Spec.squeezeByte,
    Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul]

/-- **The batch contract.**  `keccaktree_keccak256_generic(output, input, count)`
writes, for every `k < count`, `keccak256(input[64k … 64k+63])` to
`output[32k … 32k+31]`. -/
theorem hash_spec (input : Nat → BitVec 8) (k : Nat) (j : Fin 32) :
    (hash input k)[j] = Spec.keccak256 64 (fun i => input (64 * k + i)) j :=
  node_spec _ j

end Keccaktree.Proof
