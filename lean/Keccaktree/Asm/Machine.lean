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

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Keccaktree.Asm

/-- `vpternlogq imm`: bit-wise `imm[a b c]`, the sum of the minterms the
immediate selects (a native lane operation: expanding it into its minterms
in the symbolic executor multiplies the expression trees out). -/
def ternlogW (imm : Nat) (a b c : BitVec 64) : BitVec 64 :=
  let lit (x : BitVec 64) (bit : Bool) := if bit then x else ~~~ x
  (List.range 8).foldl (fun acc i =>
    if imm.testBit i then
      acc ||| (lit a (i.testBit 2) &&& (lit b (i.testBit 1) &&& lit c (i.testBit 0)))
    else acc) 0#64

/-- Memory regions: 0 = no region (a plain number), 1 input, 2 output,
3 stack, 4 read-only constants; at most 8. -/
abbrev Region := Fin 8

/-- A general-register value: an offset into a region. -/
structure Addr where
  region : Region
  off : Int
  deriving Repr, DecidableEq, Inhabited

def Addr.num (n : Int) : Addr := ⟨0, n⟩

/-- Addresses the 64-bit encoding represents faithfully (`wordGpr_gprWord`). -/
def Addr.wf (a : Addr) : Prop := 0 ≤ a.off ∧ a.off < 2 ^ 55
instance : DecidablePred Addr.wf := fun a => inferInstanceAs (Decidable (0 ≤ a.off ∧ a.off < 2 ^ 55))

/-- A general register as a stored word: a number as is, a pointer as
`(region << 56) | offset` (offsets wrap in two's complement, like the machine). -/
def gprWord (a : Addr) : BitVec 64 :=
  if a.region = 0 then BitVec.ofInt 64 a.off else (BitVec.ofNat 64 a.region.val <<< 56) + BitVec.ofInt 64 a.off

/-- A word as a register value: region tag in the top byte, else a number. -/
def wordGpr (v : BitVec 64) : Addr :=
  let r := (v >>> 56).toNat
  if r = 0 then ⟨0, v.toInt⟩ else ⟨⟨r % 8, Nat.mod_lt _ (by decide)⟩, ((v &&& 0x00ffffffffffffff#64).toNat : Int)⟩

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
  ternlog : Nat → α → α → α → α
  /-- the value if it is a known constant (masks, shuffle controls) -/
  asConst : α → Option (BitVec 64)
  /-- a pointer or count as a lane value -/
  ptr : Addr → α
  /-- the lane as an address (a pointer or a count), if it is one -/
  asAddr : α → Option Addr

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
  ternlog := ternlogW
  asConst := some
  ptr := gprWord
  asAddr := fun w => some (wordGpr w)

/-- Symbolic 64-bit lane expressions.  `ptr a` is a pointer (or count) the
cut knows: it is kept apart from data constants so that a batch's symbolic
run can be relocated (`Keccaktree.Asm.Reloc`). -/
inductive E where
  | var (i : Nat)
  | const (v : BitVec 64)
  | ptr (a : Addr)
  | xor (a b : E)
  | and (a b : E)
  | or (a b : E)
  | not (a : E)
  | shl (a : E) (n : Nat)
  | shr (a : E) (n : Nat)
  | rol (a : E) (n : Nat)
  | add (a b : E)
  | ternlog (imm : Nat) (a b c : E)
  deriving Repr, DecidableEq, Inhabited

/-- A word whose low 3 bits are those of the expression, if they are determined
(the kernels test the alignment of their pointers with `(a | b) & 7`). -/
def E.low3 : E → Option (BitVec 64)
  | .var _ => none
  | .const v => some v
  | .ptr a => some (BitVec.ofInt 64 a.off)
  | .xor a b => match a.low3, b.low3 with | some x, some y => some (x ^^^ y) | _, _ => none
  | .and a b => match a.low3, b.low3 with | some x, some y => some (x &&& y) | _, _ => none
  | .or a b => match a.low3, b.low3 with | some x, some y => some (x ||| y) | _, _ => none
  | .not a => match a.low3 with | some x => some (~~~x) | none => none
  | .shl _ _ => none
  | .shr _ _ => none
  | .rol _ _ => none
  | .add a b => match a.low3, b.low3 with | some x, some y => some (x + y) | _, _ => none
  | .ternlog _ _ _ _ => none

/-- The value of a closed expression (no variables, no pointers): the symbolic
executor's `asConst`.  Counts computed from constants stay decodable. -/
def E.closed : E → Option (BitVec 64)
  | .var _ => none
  | .const v => some v
  | .ptr a => if a.region = 0 then some (BitVec.ofInt 64 a.off) else none   -- a count is data too
  | .xor a b => match a.closed, b.closed with | some x, some y => some (x ^^^ y) | _, _ => none
  | .and a b => match a.closed, b.closed with | some x, some y => some (x &&& y) | _, _ => none
  | .or a b => match a.closed, b.closed with | some x, some y => some (x ||| y) | _, _ => none
  | .not a => match a.closed with | some x => some (~~~x) | none => none
  | .shl a n => match a.closed with | some x => some (x <<< n) | none => none
  | .shr a n => match a.closed with | some x => some (x >>> n) | none => none
  | .rol a n => match a.closed with | some x => some (x.rotateLeft n) | none => none
  | .add a b => match a.closed, b.closed with | some x, some y => some (x + y) | _, _ => none
  | .ternlog imm a b c => match a.closed, b.closed, c.closed with
    | some x, some y, some z => some (ternlogW imm x y z) | _, _, _ => none

/-- A pointer plus a (signed) constant word, if the sum stays a representable
pointer of the same region. -/
def addrPlus (p : Addr) (y : BitVec 64) : Option Addr :=
  if p.region ≠ 0 ∧ p.wf ∧ (⟨p.region, p.off + y.toInt⟩ : Addr).wf then some ⟨p.region, p.off + y.toInt⟩ else none

/-- A pointer-shaped expression's address: a known pointer, a pointer plus a
number (`addi` on a pointer register), or a pointer masked to its low 3 bits
(an alignment test). -/
def E.addrP : E → Option Addr
  | .ptr a => if a.wf then some a else none
  | .add a b =>
    match a.closed, b.closed with
    | none, some y => (a.addrP).bind fun p => addrPlus p y
    | some x, none => (b.addrP).bind fun p => addrPlus p x
    | _, _ => none
  | .and a (.const m) =>
    if m &&& ~~~7#64 = 0 then (a.low3).map fun l => Addr.num ((l &&& m).toNat : Int) else none
  | _ => none

/-- The address an expression denotes: a (representable) number if it is
closed, else its pointer shape. -/
def E.addr (e : E) : Option Addr :=
  match e.closed with
  | some v => if v >>> 56 = 0#64 ∧ (wordGpr v).wf then some (wordGpr v) else none
  | none => e.addrP

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
  ternlog := .ternlog
  asConst := E.closed
  ptr := .ptr
  asAddr := E.addr

def E.eval (env : Nat → BitVec 64) : E → BitVec 64
  | .var i => env i
  | .const v => v
  | .ptr a => gprWord a
  | .xor a b => a.eval env ^^^ b.eval env
  | .and a b => a.eval env &&& b.eval env
  | .or a b => a.eval env ||| b.eval env
  | .not a => ~~~ a.eval env
  | .shl a n => a.eval env <<< n
  | .shr a n => a.eval env >>> n
  | .rol a n => (a.eval env).rotateLeft n
  | .add a b => a.eval env + b.eval env
  | .ternlog imm a b c => ternlogW imm (a.eval env) (b.eval env) (c.eval env)

end Keccaktree.Asm
