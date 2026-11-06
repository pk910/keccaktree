import Keccaktree.Asm.X86
import Keccaktree.Spec
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
Cut states: between two slices of a kernel's instruction stream, every
register lane and memory word is a fresh variable (`regVar`, `memVar`), so
that each slice can be executed symbolically on its own.
-/
namespace Keccaktree.Asm.X86

/-- Variable numbering of the symbolic cut states: register lanes `0 … 255`,
then one variable per memory word, through a bijection `(region, index) ↦ ℕ`. -/
def regVar (r l : Nat) : Nat := 8 * r + l
/-- The data view of general register `n`. -/
def gdVar (n : Nat) : Nat := 256 + n

/-- Integers as naturals: `q ≥ 0 ↦ 2q`, `q < 0 ↦ 2|q| - 1`. -/
def encInt (q : Int) : Nat := if 0 ≤ q then 2 * q.toNat else 2 * q.natAbs - 1
def decInt (n : Nat) : Int := if n % 2 = 0 then Int.ofNat (n / 2) else -Int.ofNat ((n + 1) / 2)

theorem decInt_encInt (q : Int) : decInt (encInt q) = q := by
  unfold encInt decInt
  split
  · simp only [Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_cancel_left _ (by decide : 0 < 2), Int.ofNat_eq_natCast]
    omega
  · have h1 : 1 ≤ q.natAbs := by omega
    have h2 : (2 * q.natAbs - 1) % 2 = 1 := by omega
    simp only [h2, Nat.one_ne_zero, ↓reduceIte, Int.ofNat_eq_natCast]
    omega

def memVar (region : Region) (q : Int) : Nat := 288 + 8 * encInt q + region.val
def memVarRegion (i : Nat) : Region := ⟨(i - 288) % 8, Nat.mod_lt _ (by decide)⟩
def memVarIndex (i : Nat) : Int := decInt ((i - 288) / 8)

theorem memVarRegion_memVar (r : Region) (q : Int) : memVarRegion (memVar r q) = r := by
  simp only [memVarRegion, memVar]
  apply Fin.ext; simp only
  omega
theorem memVarIndex_memVar (r : Region) (q : Int) : memVarIndex (memVar r q) = q := by
  simp only [memVarIndex, memVar]
  have : (288 + 8 * encInt q + r.val - 288) / 8 = encInt q := by omega
  rw [this, decInt_encInt]
theorem memVar_ge (r : Region) (q : Int) : 288 ≤ memVar r q := by simp only [memVar]; omega

/-- The memory of a cut state: every word a variable. -/
def cutMem : Region → Int → E := fun r q => .var (memVar r q)

/-- The symbolic lane held at a variable's location in a state. -/
def readVar (s : State E) (i : Nat) : E :=
  if i < 256 then (s.v.getD (i / 8) (Vector.replicate 8 (.const 0))).getD (i % 8) (.const 0)
  else if i < 288 then s.gd.getD (i - 256) (.const 0)
  else s.mem (memVarRegion i) (memVarIndex i)

/-- Lane `k = x + 5y` of a state, as one atom for `bv_decide` (the `Fin 5`
literals produced by different simp paths differ in their instance proofs,
which `bv_decide` would take for different atoms). -/
def L (A : Keccak.Spec.State) (k : Nat) : BitVec 64 := A ⟨k % 5, by omega⟩ ⟨k / 5 % 5, by omega⟩

theorem lane_0 (A : Keccak.Spec.State) : A 0 0 = L A 0 := rfl
theorem lane_1 (A : Keccak.Spec.State) : A 1 0 = L A 1 := rfl
theorem lane_2 (A : Keccak.Spec.State) : A 2 0 = L A 2 := rfl
theorem lane_3 (A : Keccak.Spec.State) : A 3 0 = L A 3 := rfl
theorem lane_4 (A : Keccak.Spec.State) : A 4 0 = L A 4 := rfl
theorem lane_5 (A : Keccak.Spec.State) : A 0 1 = L A 5 := rfl
theorem lane_6 (A : Keccak.Spec.State) : A 1 1 = L A 6 := rfl
theorem lane_7 (A : Keccak.Spec.State) : A 2 1 = L A 7 := rfl
theorem lane_8 (A : Keccak.Spec.State) : A 3 1 = L A 8 := rfl
theorem lane_9 (A : Keccak.Spec.State) : A 4 1 = L A 9 := rfl
theorem lane_10 (A : Keccak.Spec.State) : A 0 2 = L A 10 := rfl
theorem lane_11 (A : Keccak.Spec.State) : A 1 2 = L A 11 := rfl
theorem lane_12 (A : Keccak.Spec.State) : A 2 2 = L A 12 := rfl
theorem lane_13 (A : Keccak.Spec.State) : A 3 2 = L A 13 := rfl
theorem lane_14 (A : Keccak.Spec.State) : A 4 2 = L A 14 := rfl
theorem lane_15 (A : Keccak.Spec.State) : A 0 3 = L A 15 := rfl
theorem lane_16 (A : Keccak.Spec.State) : A 1 3 = L A 16 := rfl
theorem lane_17 (A : Keccak.Spec.State) : A 2 3 = L A 17 := rfl
theorem lane_18 (A : Keccak.Spec.State) : A 3 3 = L A 18 := rfl
theorem lane_19 (A : Keccak.Spec.State) : A 4 3 = L A 19 := rfl
theorem lane_20 (A : Keccak.Spec.State) : A 0 4 = L A 20 := rfl
theorem lane_21 (A : Keccak.Spec.State) : A 1 4 = L A 21 := rfl
theorem lane_22 (A : Keccak.Spec.State) : A 2 4 = L A 22 := rfl
theorem lane_23 (A : Keccak.Spec.State) : A 3 4 = L A 23 := rfl
theorem lane_24 (A : Keccak.Spec.State) : A 4 4 = L A 24 := rfl

/-- `L` of a state produced by a round unfolds (the input-state atoms `L (A n) k` stay opaque). -/
theorem L_round (i : Nat) (A : Keccak.Spec.State) (k : Nat) :
    L (Keccak.Spec.round i A) k = (Keccak.Spec.round i A) ⟨k % 5, by omega⟩ ⟨k / 5 % 5, by omega⟩ := rfl

/-- `L` of a state given by its lane function unfolds (`simp` unfolds the spec
round to such a literal first); `L (A n) k` for an abstract state stays opaque. -/
theorem L_mk (f : Fin 5 → Fin 5 → BitVec 64) (k : Nat) :
    L ⟨f⟩ k = f ⟨k % 5, by omega⟩ ⟨k / 5 % 5, by omega⟩ := rfl

/-- The 75 quantities a location may hold: lanes 0..24 of a state, theta's
`D[x] = C[x-1] ^ rotl(C[x+1], 1)` (25..29), the column parities `C[x]`
(30..34), the partial parities over 2, 3, 4 rows (35..49) and theta's output
lanes (50..74). -/
def specQuantity (A : Keccak.Spec.State) (kind : Nat) : BitVec 64 :=
  match kind with
  | 0 => L A 0
  | 1 => L A 1
  | 2 => L A 2
  | 3 => L A 3
  | 4 => L A 4
  | 5 => L A 5
  | 6 => L A 6
  | 7 => L A 7
  | 8 => L A 8
  | 9 => L A 9
  | 10 => L A 10
  | 11 => L A 11
  | 12 => L A 12
  | 13 => L A 13
  | 14 => L A 14
  | 15 => L A 15
  | 16 => L A 16
  | 17 => L A 17
  | 18 => L A 18
  | 19 => L A 19
  | 20 => L A 20
  | 21 => L A 21
  | 22 => L A 22
  | 23 => L A 23
  | 24 => L A 24
  | 25 => (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21)).rotateLeft 1
  | 26 => (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22)).rotateLeft 1
  | 27 => (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23)).rotateLeft 1
  | 28 => (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24)).rotateLeft 1
  | 29 => (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20)).rotateLeft 1
  | 30 => (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20)
  | 31 => (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21)
  | 32 => (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22)
  | 33 => (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23)
  | 34 => (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24)
  -- partial column parities (lazily rotating scalar kernels keep them live across round boundaries)
  | 35 => L A 0 ^^^ L A 5
  | 36 => L A 1 ^^^ L A 6
  | 37 => L A 2 ^^^ L A 7
  | 38 => L A 3 ^^^ L A 8
  | 39 => L A 4 ^^^ L A 9
  | 40 => L A 0 ^^^ L A 5 ^^^ L A 10
  | 41 => L A 1 ^^^ L A 6 ^^^ L A 11
  | 42 => L A 2 ^^^ L A 7 ^^^ L A 12
  | 43 => L A 3 ^^^ L A 8 ^^^ L A 13
  | 44 => L A 4 ^^^ L A 9 ^^^ L A 14
  | 45 => L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15
  | 46 => L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16
  | 47 => L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17
  | 48 => L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18
  | 49 => L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19
  -- theta's output lanes `A[x,y] ^ D[x]`
  | 50 => L A 0 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)
  | 51 => L A 1 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)
  | 52 => L A 2 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)
  | 53 => L A 3 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)
  | 54 => L A 4 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)
  | 55 => L A 5 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)
  | 56 => L A 6 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)
  | 57 => L A 7 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)
  | 58 => L A 8 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)
  | 59 => L A 9 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)
  | 60 => L A 10 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)
  | 61 => L A 11 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)
  | 62 => L A 12 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)
  | 63 => L A 13 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)
  | 64 => L A 14 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)
  | 65 => L A 15 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)
  | 66 => L A 16 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)
  | 67 => L A 17 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)
  | 68 => L A 18 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)
  | 69 => L A 19 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)
  | 70 => L A 20 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)
  | 71 => L A 21 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)
  | 72 => L A 22 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)
  | 73 => L A 23 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)
  | 74 => L A 24 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)
  | _ => 0#64

/-- `Fin 5` indices built with `Fin.mk` as literals (for `bv_decide`'s atom matching). -/
theorem Fin.mk5_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
theorem Fin.mk5_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
theorem Fin.mk5_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
theorem Fin.mk5_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
theorem Fin.mk5_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl

end Keccaktree.Asm.X86
