/-!
# A small machine model for the assembly kernels

Shared by the x86-64, AArch64 and RISC-V kernel models.  The machine is
polymorphic in the type `α` of 64-bit lane values: with `α := BitVec 64`
it is an executable interpreter (used to validate the instruction
semantics on test vectors), with `α := E` (symbolic expressions) the very
same `step` functions are a symbolic executor, whose results the kernel
computes and `bv_decide` compares with the specification.  Because both
are one function, their agreement is the single lemma that `step` commutes
with evaluation (`E.eval`), proved once per instruction.

Memory is modelled per *region* (input nodes, output digests, the kernel's
stack frame, the read-only constants): a general register holds a region
and an offset, so every address the kernels form is region-relative and
concrete.  Memory cells are 8-byte words (`(region, word index)`); the
kernels only load and store whole, 8-byte aligned words (checked, `err`
otherwise).  Distinct regions are assumed not to overlap.
-/

namespace Keccaktree.Asm

/-- The lane operations the kernels use, over some value type. -/
class LaneOps (α : Type) where
  const : BitVec 64 → α
  xor : α → α → α
  and : α → α → α
  or : α → α → α
  not : α → α
  shl : α → Nat → α
  shr : α → Nat → α
  rol : α → Nat → α
  add : α → α → α
  /-- the value if it is a known constant (masks, shuffle controls) -/
  asConst : α → Option (BitVec 64)

instance : LaneOps (BitVec 64) where
  const := id
  xor := (· ^^^ ·)
  and := (· &&& ·)
  or := (· ||| ·)
  not := (~~~ ·)
  shl := (· <<< ·)
  shr := (· >>> ·)
  rol := BitVec.rotateLeft
  add := (· + ·)
  asConst := some

/-- Symbolic 64-bit lane expressions. -/
inductive E where
  | var (i : Nat)
  | const (v : BitVec 64)
  | xor (a b : E)
  | and (a b : E)
  | or (a b : E)
  | not (a : E)
  | shl (a : E) (n : Nat)
  | shr (a : E) (n : Nat)
  | rol (a : E) (n : Nat)
  | add (a b : E)
  deriving Repr, DecidableEq, Inhabited

/-- The value of a closed expression (no variables): the symbolic executor's
`asConst`.  Pointers and counts computed from constants (`or a0, a1` for an
alignment check, `addi` on a saved pointer) stay decodable. -/
def E.closed : E → Option (BitVec 64)
  | .var _ => none
  | .const v => some v
  | .xor a b => match a.closed, b.closed with | some x, some y => some (x ^^^ y) | _, _ => none
  | .and a b => match a.closed, b.closed with | some x, some y => some (x &&& y) | _, _ => none
  | .or a b => match a.closed, b.closed with | some x, some y => some (x ||| y) | _, _ => none
  | .not a => match a.closed with | some x => some (~~~x) | none => none
  | .shl a n => match a.closed with | some x => some (x <<< n) | none => none
  | .shr a n => match a.closed with | some x => some (x >>> n) | none => none
  | .rol a n => match a.closed with | some x => some (x.rotateLeft n) | none => none
  | .add a b => match a.closed, b.closed with | some x, some y => some (x + y) | _, _ => none

instance : LaneOps E where
  const := .const
  xor := .xor
  and := .and
  or := .or
  not := .not
  shl := .shl
  shr := .shr
  rol := .rol
  add := .add
  asConst := E.closed

def E.eval (env : Nat → BitVec 64) : E → BitVec 64
  | .var i => env i
  | .const v => v
  | .xor a b => a.eval env ^^^ b.eval env
  | .and a b => a.eval env &&& b.eval env
  | .or a b => a.eval env ||| b.eval env
  | .not a => ~~~ a.eval env
  | .shl a n => a.eval env <<< n
  | .shr a n => a.eval env >>> n
  | .rol a n => (a.eval env).rotateLeft n
  | .add a b => a.eval env + b.eval env

/-- Memory regions: 0 = no region (a plain number), 1 input, 2 output,
3 stack, 4 read-only constants; at most 8. -/
abbrev Region := Fin 8

/-- A general-register value: an offset into a region. -/
structure Addr where
  region : Region
  off : Int
  deriving Repr, DecidableEq, Inhabited

def Addr.num (n : Int) : Addr := ⟨0, n⟩

end Keccaktree.Asm
