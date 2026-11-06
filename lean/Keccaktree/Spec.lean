/-!
# Keccak-256 reference specification

An executable, independent specification of Keccak-f[1600] and the
keccak256 sponge (rate 1088, capacity 512, pad `0x01 … 0x80`, i.e. the
original Keccak padding used by Ethereum, not NIST SHA3-256's `0x06`).

It follows FIPS 202 (sections 3.2 and 3.3) step by step: theta, rho, pi,
chi and iota are written as the lane-level formulas of the standard, and
the rho offsets and the round constants are *derived* from the standard's
definitions (the `(t+1)(t+2)/2` triangular numbers along the `(x,y) ↦
(y, 2x+3y)` orbit, and the `rc(t)` LFSR of Algorithm 5).  Lemmas
`rhoOffset_eq` and `RC_eq` tie them to the literal tables that
implementations hard-code; both are checked by `decide`.

The state is `Fin 5 → Fin 5 → BitVec 64` indexed `A[x][y]`; lane `x + 5y`
of the byte-serialised state is `A[x][y]` (FIPS 202 section 3.1.2).

Nothing in this file is shared with `tools/gen_core.py`; it is the
specification the generated kernel core is proved against in
`Keccaktree/Proof.lean`.
-/

namespace Keccak.Spec

abbrev Lane := BitVec 64

/-- The 5×5 lane state `A[x][y]`.  A structure (rather than a bare function
type) so that the compiler does not eta-expand the round functions, which
would make executing the spec exponential in the number of rounds. -/
structure State where
  lane : Fin 5 → Fin 5 → Lane

instance : CoeFun State (fun _ => Fin 5 → Fin 5 → Lane) := ⟨State.lane⟩

@[ext] theorem State.ext {A B : State} (h : ∀ x y, A x y = B x y) : A = B := by
  cases A; cases B; simp only [State.mk.injEq]; funext x y; exact h x y

/-- Rotation offsets `r[x,y]` of rho (FIPS 202, Table 2), computed as the
standard defines them: walk `(x,y)` from `(1,0)` along `(x,y) ↦ (y, 2x+3y)`
and assign the triangular numbers `(t+1)(t+2)/2 mod 64`. -/
def rhoOffsetF (x y : Fin 5) : Nat :=
  -- walk the orbit for t = 0 .. 23 starting at (1,0); (0,0) is never visited
  -- and keeps offset 0.  `walk n` handles t = 24 - n, …, 23.
  let rec walk : Nat → Fin 5 × Fin 5 → Nat → Nat
    | 0, _, acc => acc
    | n + 1, (cx, cy), acc =>
        let t := 24 - (n + 1)
        let acc := if cx = x ∧ cy = y then (t + 1) * (t + 2) / 2 % 64 else acc
        walk n (cy, 2 * cx + 3 * cy) acc
  walk 24 (1, 0) 0

/-- The literal rho table (lane `x + 5y`), as implementations hard-code it. -/
def rhoOffset (x y : Fin 5) : Nat :=
  match x, y with
  | 0, 0 => 0  | 1, 0 => 1  | 2, 0 => 62 | 3, 0 => 28 | 4, 0 => 27
  | 0, 1 => 36 | 1, 1 => 44 | 2, 1 => 6  | 3, 1 => 55 | 4, 1 => 20
  | 0, 2 => 3  | 1, 2 => 10 | 2, 2 => 43 | 3, 2 => 25 | 4, 2 => 39
  | 0, 3 => 41 | 1, 3 => 45 | 2, 3 => 15 | 3, 3 => 21 | 4, 3 => 8
  | 0, 4 => 18 | 1, 4 => 2  | 2, 4 => 61 | 3, 4 => 56 | 4, 4 => 14

/-- The hard-coded rho table is the one FIPS 202 defines. -/
theorem rhoOffset_eq : ∀ x y, rhoOffset x y = rhoOffsetF x y := by decide +kernel

/-- One step of the `rc(t)` LFSR of FIPS 202 Algorithm 5 on an 8-bit state
`R` (bit `i` of the natural number is `R[i]`): `R ← 0 ‖ R`, then
`R[0], R[4], R[5], R[6] ^= R[8]`, then truncate to 8 bits. -/
def lfsrStep (r : Nat) : Nat :=
  let r := r <<< 1
  let b := (r >>> 8) &&& 1
  (r ^^^ (b * 0x71)) % 256   -- 0x71 = bits 0, 4, 5, 6

def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, r => r
  | n + 1, r => iterate f n (f r)

/-- `rc(t)` of FIPS 202 Algorithm 5: run the LFSR `t mod 255` times from
`R = 10000000` and return `R[0]`. -/
def rc (t : Nat) : Bool := (iterate lfsrStep (t % 255) 1) &&& 1 = 1

/-- Round constant `RC[i]` from Algorithm 6 step 3: `RC[2^j - 1] = rc(j + 7 i)`. -/
def RCF (i : Nat) : Lane :=
  (List.range 7).foldl (fun acc j => if rc (j + 7 * i) then acc ||| (1#64 <<< (2 ^ j - 1)) else acc) 0#64

/-- The literal round constant table, as implementations hard-code it. -/
def RC (i : Nat) : Lane :=
  match i with
  | 0  => 0x0000000000000001#64 | 1  => 0x0000000000008082#64
  | 2  => 0x800000000000808a#64 | 3  => 0x8000000080008000#64
  | 4  => 0x000000000000808b#64 | 5  => 0x0000000080000001#64
  | 6  => 0x8000000080008081#64 | 7  => 0x8000000000008009#64
  | 8  => 0x000000000000008a#64 | 9  => 0x0000000000000088#64
  | 10 => 0x0000000080008009#64 | 11 => 0x000000008000000a#64
  | 12 => 0x000000008000808b#64 | 13 => 0x800000000000008b#64
  | 14 => 0x8000000000008089#64 | 15 => 0x8000000000008003#64
  | 16 => 0x8000000000008002#64 | 17 => 0x8000000000000080#64
  | 18 => 0x000000000000800a#64 | 19 => 0x800000008000000a#64
  | 20 => 0x8000000080008081#64 | 21 => 0x8000000000008080#64
  | 22 => 0x0000000080000001#64 | 23 => 0x8000000080008008#64
  | _  => 0#64

/-- The hard-coded round constants are the ones FIPS 202 derives. -/
theorem RC_eq : ∀ i < 24, RC i = RCF i := by decide +kernel

/-- θ (FIPS 202 Algorithm 1). -/
def theta (A : State) : State :=
  let C : Fin 5 → Lane := fun x => A x 0 ^^^ A x 1 ^^^ A x 2 ^^^ A x 3 ^^^ A x 4
  let D : Fin 5 → Lane := fun x => C (x - 1) ^^^ (C (x + 1)).rotateLeft 1
  ⟨fun x y => A x y ^^^ D x⟩

/-- ρ (FIPS 202 Algorithm 2): rotate lane `(x,y)` by `rhoOffset x y`. -/
def rho (A : State) : State :=
  ⟨fun x y => (A x y).rotateLeft (rhoOffset x y)⟩

/-- π (FIPS 202 Algorithm 3): `A'[x,y] = A[(x + 3y) mod 5, x]`. -/
def pi (A : State) : State :=
  ⟨fun x y => A (x + 3 * y) x⟩

/-- χ (FIPS 202 Algorithm 4): `A'[x,y] = A[x,y] ⊕ (¬A[x+1,y] ∧ A[x+2,y])`. -/
def chi (A : State) : State :=
  ⟨fun x y => A x y ^^^ (~~~ A (x + 1) y &&& A (x + 2) y)⟩

/-- ι (FIPS 202 Algorithm 6): xor the round constant into lane `(0,0)`. -/
def iota (i : Nat) (A : State) : State :=
  ⟨fun x y => if x = 0 ∧ y = 0 then A x y ^^^ RC i else A x y⟩

/-- One round `Rnd(A, i) = ι(χ(π(ρ(θ(A)))), i)`. -/
def round (i : Nat) (A : State) : State :=
  iota i (chi (pi (rho (theta A))))

/-- Materialise a (lazily evaluated) functional state into a vector so that
executing the spec is not exponential in the round count.  Semantically the
identity (`memo_eq`); proofs erase it. -/
def memo (A : State) : State :=
  let v : Vector Lane 25 :=
    Vector.ofFn fun i : Fin 25 => A ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ ⟨i.val / 5, by omega⟩
  ⟨fun x y => v[x.val + 5 * y.val]'(by omega)⟩

theorem memo_eq (A : State) : memo A = A := by
  apply State.ext; intro x y
  simp only [memo, Vector.getElem_ofFn]
  have h1 : (x.val + 5 * y.val) % 5 = x.val := by omega
  have h2 : (x.val + 5 * y.val) / 5 = y.val := by omega
  congr 1 <;> exact Fin.ext (by simp only [h1, h2])

/-- Rounds `0 … n-1` applied in order. -/
def rounds : Nat → State → State
  | 0, A => A
  | n + 1, A => round n (memo (rounds n A))

/-- Keccak-f[1600] = 24 rounds. -/
def keccakF (A : State) : State := rounds 24 A

/-! ## The sponge -/

/-- Load a little-endian 64-bit lane from bytes `b off, …, b (off+7)`. -/
def ld64 (b : Nat → BitVec 8) (off : Nat) : Lane :=
  b (off + 7) ++ b (off + 6) ++ b (off + 5) ++ b (off + 4) ++
  b (off + 3) ++ b (off + 2) ++ b (off + 1) ++ b off

/-- Xor one 136-byte block into the 17 rate lanes (1088 bits); lanes 17 … 24
are the capacity and never take input. -/
def absorb (A : State) (block : Nat → BitVec 8) : State :=
  ⟨fun x y => if x.val + 5 * y.val < 17 then A x y ^^^ ld64 block (8 * (x.val + 5 * y.val)) else A x y⟩

/-- Keccak `pad10*1` with the keccak256 domain byte `0x01`: the padded message
as a function of the byte index.  Padded length is the next multiple of 136
strictly greater than `len`. -/
def paddedLen (len : Nat) : Nat := (len / 136 + 1) * 136

def padded (len : Nat) (m : Nat → BitVec 8) (i : Nat) : BitVec 8 :=
  if i < len then m i
  else (if i = len then 0x01#8 else 0#8) ||| (if i + 1 = paddedLen len then 0x80#8 else 0#8)

/-- Absorb `n` blocks of the padded message. -/
def absorbBlocks (p : Nat → BitVec 8) : Nat → State → State
  | 0, A => A
  | k + 1, A => keccakF (absorb (absorbBlocks p k A) fun i => p (136 * k + i))

/-- Byte `i` of the little-endian serialisation of the state (lane `x + 5y`). -/
def squeezeByte (A : State) (i : Nat) : BitVec 8 :=
  let lane := i / 8
  (A ⟨lane % 5, Nat.mod_lt _ (by decide)⟩ ⟨lane / 5 % 5, Nat.mod_lt _ (by decide)⟩).extractLsb' (8 * (i % 8)) 8

/-- keccak256 of the `len`-byte message `m` (bytes `m 0 … m (len-1)`), as a
function from the output byte index `0 … 31` to the byte. -/
def keccak256 (len : Nat) (m : Nat → BitVec 8) : Nat → BitVec 8 :=
  squeezeByte (absorbBlocks (padded len m) (paddedLen len / 136) ⟨fun _ _ => 0#64⟩)

/-! ### Executable wrappers (test vectors) -/

def keccak256List (m : List UInt8) : List UInt8 :=
  let f : Nat → BitVec 8 := fun i => (m.getD i 0).toBitVec
  (List.range 32).map fun i => UInt8.ofBitVec (keccak256 m.length f i)

def hex (l : List UInt8) : String :=
  String.join (l.map fun b =>
    let s := (Nat.toDigits 16 b.toNat)
    String.ofList (if s.length < 2 then '0' :: s else s))

end Keccak.Spec
