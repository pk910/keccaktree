/-!
# The portable keccaktree kernel, as a Lean program

A transliteration of `src/keccak256_generic.c` (and of its line-by-line
twin `keccak256_1_generic.go`): the hand-written Keccak-f[1600] round loop
over `uint64_t a[25]` and the single-block keccak256 sponge over one 64-byte
node.  The tables `RC`, `RHO`, `PI`, the loop shapes (in particular rho and
pi done in place along pi's 24-cycle with the carried temporary `t`) and
the byte loads/stores follow the C.  `for` loops over a fixed count are
written as structural recursion on the remaining iteration count; the
per-lane loops of theta and chi, whose iterations are independent, as
`Vector.ofFn`.

Nothing here refers to the specification (`Keccaktree/Spec.lean`); the
proof that this program computes keccak256 is in `Keccaktree/Proof.lean`.
-/

namespace Keccaktree.Generic

abbrev W := BitVec 64
/-- `uint64_t a[25]`, lane `i = x + 5y`. -/
abbrev Lanes := Vector W 25

/-- `static const uint64_t RC[24]` -/
def RC (r : Nat) : W :=
  match r with
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

/-- `static const unsigned RHO[24]`: rho offsets along pi's 24-cycle starting at lane 1. -/
def RHO (i : Nat) : Nat :=
  match i with
  | 0 => 1   | 1 => 3   | 2 => 6   | 3 => 10  | 4 => 15  | 5 => 21
  | 6 => 28  | 7 => 36  | 8 => 45  | 9 => 55  | 10 => 2  | 11 => 14
  | 12 => 27 | 13 => 41 | 14 => 56 | 15 => 8  | 16 => 25 | 17 => 43
  | 18 => 62 | 19 => 18 | 20 => 39 | 21 => 61 | 22 => 20 | 23 => 44
  | _ => 0

/-- `static const unsigned PI[24]`: pi destinations along that cycle. -/
def PI (i : Nat) : Nat :=
  match i with
  | 0 => 10  | 1 => 7   | 2 => 11  | 3 => 17  | 4 => 18  | 5 => 3
  | 6 => 5   | 7 => 16  | 8 => 8   | 9 => 21  | 10 => 24 | 11 => 4
  | 12 => 15 | 13 => 23 | 14 => 19 | 15 => 13 | 16 => 12 | 17 => 2
  | 18 => 20 | 19 => 14 | 20 => 22 | 21 => 9  | 22 => 6  | 23 => 1
  | _ => 0

theorem PI_lt (i : Nat) : PI i < 25 := by
  unfold PI; split <;> decide

/-- `#define ROL(a, n) (((a) << (n)) | ((a) >> (64 - (n))))` -/
def ROL (a : W) (n : Nat) : W := (a <<< n) ||| (a >>> (64 - n))

/-- theta: `c[x] = a[x] ^ a[x+5] ^ a[x+10] ^ a[x+15] ^ a[x+20]`, then for
each column `d = c[(x+4)%5] ^ ROL(c[(x+1)%5], 1)` and `a[y+x] ^= d`. -/
def theta (a : Lanes) : Lanes :=
  let c : Vector W 5 := Vector.ofFn fun x : Fin 5 =>
    a[x.val] ^^^ a[x.val + 5] ^^^ a[x.val + 10] ^^^ a[x.val + 15] ^^^ a[x.val + 20]
  Vector.ofFn fun i : Fin 25 =>
    let x := i.val % 5
    let d := c[(x + 4) % 5] ^^^ ROL c[(x + 1) % 5] 1
    a[i.val] ^^^ d

/-- rho and pi in place:
```
t = a[1];
for (int i = 0; i < 24; i++) { u = a[PI[i]]; a[PI[i]] = ROL(t, RHO[i]); t = u; }
```
`rhoPiLoop a t n` runs the remaining `n` iterations, `i = 24 - n … 23`. -/
def rhoPiLoop (a : Lanes) (t : W) : Nat → Lanes
  | 0 => a
  | n + 1 =>
    let i := 24 - (n + 1)
    let u := a[PI i]'(PI_lt i)
    rhoPiLoop (a.set (PI i) (ROL t (RHO i)) (PI_lt i)) u n

def rhoPi (a : Lanes) : Lanes := rhoPiLoop a a[1] 24

/-- chi, row by row: `c[x] = a[y+x]`, then `a[y+x] = c[x] ^ (~c[(x+1)%5] & c[(x+2)%5])`. -/
def chi (a : Lanes) : Lanes :=
  Vector.ofFn fun i : Fin 25 =>
    let y := i.val / 5 * 5
    let x := i.val % 5
    a[y + x] ^^^ (~~~ a[y + (x + 1) % 5] &&& a[y + (x + 2) % 5])

/-- iota: `a[0] ^= RC[r]`. -/
def iota (r : Nat) (a : Lanes) : Lanes := a.set 0 (a[0] ^^^ RC r)

/-- The body of `for (int r = 0; r < 24; r++)`. -/
def round (r : Nat) (a : Lanes) : Lanes := iota r (chi (rhoPi (theta a)))

/-- `rounds a n` = rounds `0 … n-1` in order. -/
def rounds (a : Lanes) : Nat → Lanes
  | 0 => a
  | n + 1 => round n (rounds a n)

/-- `static void keccak_f1600(uint64_t a[25])` -/
def keccakF1600 (a : Lanes) : Lanes := rounds a 24

/-! ## Bytes -/

/-- `ld64`: `v = 0; for (i = 7; i >= 0; i--) v = (v << 8) | p[i];` over the
bytes `p off … p (off+7)`.  `ld64Loop v n` runs the remaining `n`
iterations, `i = n-1 … 0`. -/
def ld64Loop (p : Nat → BitVec 8) (off : Nat) (v : W) : Nat → W
  | 0 => v
  | n + 1 => ld64Loop p off ((v <<< 8) ||| (p (off + n)).zeroExtend 64) n

def ld64 (p : Nat → BitVec 8) (off : Nat) : W := ld64Loop p off 0 8

/-- `st64`: byte `i` is `(unsigned char)(v >> (8 * i))`. -/
def st64 (v : W) (i : Nat) : BitVec 8 := (v >>> (8 * i)).truncate 8

/-- `for (i = 0; i < 8; i++) a[i] = ld64(input + 8 * i);` (`loadLanes a p n`
sets lanes `0 … n-1`). -/
def loadLanes (a : Lanes) (p : Nat → BitVec 8) : (n : Nat) → n ≤ 8 → Lanes
  | 0, _ => a
  | n + 1, h => (loadLanes a p n (by omega)).set n (ld64 p (8 * n)) (by omega)

/-- One iteration of the loop in `keccaktree_keccak256_generic`: the 64-byte
node `input 0 … input 63` to its 32 digest bytes. -/
def node (input : Nat → BitVec 8) : Vector (BitVec 8) 32 :=
  let a : Lanes := Vector.replicate 25 0#64
  let a := loadLanes a input 8 (by decide)
  let a := a.set 8 0x01#64
  let a := a.set 16 0x8000000000000000#64
  let a := keccakF1600 a
  Vector.ofFn fun j : Fin 32 => st64 a[j.val / 8] (j.val % 8)

/-- `keccaktree_keccak256_generic(output, input, count)`: digest `k` (for
`k < count`) is the hash of the node at `input + 64 k`. -/
def hash (input : Nat → BitVec 8) (k : Nat) : Vector (BitVec 8) 32 :=
  node fun i => input (64 * k + i)

end Keccaktree.Generic
