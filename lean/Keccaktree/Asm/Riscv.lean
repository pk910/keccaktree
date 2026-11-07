import Keccaktree.Asm.Arm
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# RISC-V kernel semantics

The instruction subset of `src/keccak256_{rv64_x1,zbb_x1,rvv,rvv_zvkb}.S` on
the shared machine state.  The general registers `x0..x31` are data words in
`gd` (`x0` reads as zero; pointers and counts are constants in the `gprWord`
encoding, decoded by `Arm.gx`); the vector registers `v0..v31` hold
`vlmax = VLEN/64` lanes (`vlmax ≤ 8`), of which the first `vl` are active.
Vector operations leave the tail lanes undisturbed (one of the behaviours
`ta` allows; the tail never feeds an active lane).  Only `e64, m1` vector
configurations are modelled; the byte-copy paths for unaligned buffers
(`lbu/sb`, `vle8/vse8`) are `unsupported` and fail.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next wordGpr
open Keccaktree.Asm.Arm (gx setX withX addr withAddr)
open LaneOps

inductive Op2 where
  | xor | or | and | add | sub | andn
  deriving Repr, DecidableEq
inductive OpI where
  | xori | ori | andi | addi | slli | srli | rori
  deriving Repr, DecidableEq
inductive VOp where
  | xor | and | or | andn
  deriving Repr, DecidableEq
inductive VSh where
  | sll | srl | ror
  deriving Repr, DecidableEq
inductive BCond where
  | eq | ne | geu
  deriving Repr, DecidableEq

inductive Instr where
  -- scalar
  | op (d a b : Nat) (k : Op2)
  | opi (d a : Nat) (k : OpI) (imm : BitVec 64)
  | li (d : Nat) (imm : BitVec 64)
  | mv (d a : Nat)
  | not (d a : Nat)
  | lea (d : Nat) (a : Addr)                -- `auipc` resolved to the constant table
  | ld (d base : Nat) (off : Int)
  | sd (src base : Nat) (off : Int)
  | br (c : BCond) (a b : Nat) (target : Nat)
  | j (target : Nat)
  | ret
  | nop
  | unsupported (name : String)
  -- vector (`e64, m1`)
  | vsetvli (d a : Nat)
  | vop (d a b : Nat) (k : VOp)
  | vnot (d a : Nat)
  | vshifti (d a : Nat) (k : VSh) (imm : Nat)
  | vshiftx (d a : Nat) (k : VSh) (x : Nat)
  | vxorx (d a x : Nat)
  | vmvi (d : Nat) (imm : BitVec 64)
  | vmvx (d x : Nat)
  | vmvv (d a : Nat)
  | vlseg (d base nf : Nat)
  | vsseg (src base nf : Nat)
  deriving Repr, DecidableEq

variable {α : Type} [LaneOps α]

/-- Read a general register (`x0` is zero). -/
def getR (s : State α) (n : Nat) : α := if n = 0 then const 0 else s.getGD n
/-- Write a general register (writes to `x0` are dropped). -/
def setR (s : State α) (n : Nat) (x : α) : State α := if n = 0 then s else s.setGD n x

def rotr (x : α) (n : Nat) : α := rol x ((64 - n % 64) % 64)
def sub (a b : α) : α := add a (add (not b) (const 1))

def op2 : Op2 → α → α → α
  | .xor, a, b => xor a b
  | .or, a, b => or a b
  | .and, a, b => and a b
  | .add, a, b => add a b
  | .sub, a, b => sub a b
  | .andn, a, b => and a (not b)

def opi : OpI → α → BitVec 64 → α
  | .xori, a, i => xor a (const i)
  | .ori, a, i => or a (const i)
  | .andi, a, i => and a (const i)
  | .addi, a, i => add a (const i)
  | .slli, a, i => shl a i.toNat
  | .srli, a, i => shr a i.toNat
  | .rori, a, i => rotr a i.toNat

def vop : VOp → α → α → α
  | .xor, a, b => xor a b
  | .and, a, b => and a b
  | .or, a, b => or a b
  | .andn, a, b => and a (not b)

def vsh : VSh → α → Nat → α
  | .sll, a, n => if n < 64 then shl a n else const 0
  | .srl, a, n => if n < 64 then shr a n else const 0
  | .ror, a, n => rotr a n

/-- Lane `l` of vector register `n`. -/
def lane (s : State α) (n l : Nat) : α := (s.getV n).getD l (const 0)

/-- Write the active lanes of a vector register from a lane function; the tail stays. -/
def setActive (s : State α) (d : Nat) (f : Nat → α) : State α :=
  s.setV d (Vector.ofFn fun i : Fin 8 => if i.val < s.vl then f i.val else lane s d i.val)

def next (s : State α) : State α := { s with pc := s.pc + 1 }

/-- Branch condition on two constant words. -/
def brHolds : BCond → BitVec 64 → BitVec 64 → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .geu, x, y => y ≤ x

def exec (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (s : State α) : State α :=
  if s.halted then s else
  match i with
  | .op d a b k => next (setR s d (op2 k (getR s a) (getR s b)))
  | .opi d a k imm => next (setR s d (opi k (getR s a) imm))
  | .li d imm => next (setR s d (const imm))
  | .mv d a => next (setR s d (getR s a))
  | .not d a => next (setR s d (not (getR s a)))
  | .lea d a => next (setX s d a)
  | .ld d base off => withAddr s base off fun a =>
    match s.loadWords rodata a 1 with
    | some [w] => next (setR s d w)
    | _ => s.fail
  | .sd src base off => withAddr s base off fun a =>
    match s.storeWords a [getR s src] with
    | some s' => next s'
    | none => s.fail
  | .br c a b t =>
    match asConst (getR s a), asConst (getR s b) with
    | some x, some y => { s with pc := if brHolds c x y then t else s.pc + 1 }
    | _, _ => s.fail
  | .j t => { s with pc := t }
  | .ret => { s with halted := true }
  | .nop => next s
  | .unsupported _ => s.fail
  | .vsetvli d a =>
    match asConst (getR s a) with
    | some avl =>
      let vl := min avl.toNat vlmax
      next { setR s d (const (BitVec.ofNat 64 vl)) with vl := vl }
    | none => s.fail
  | .vop d a b k => next (setActive s d fun l => vop k (lane s a l) (lane s b l))
  | .vnot d a => next (setActive s d fun l => not (lane s a l))
  | .vshifti d a k imm => next (setActive s d fun l => vsh k (lane s a l) imm)
  | .vshiftx d a k x =>
    match asConst (getR s x) with
    | some n => next (setActive s d fun l => vsh k (lane s a l) n.toNat)
    | none => s.fail
  | .vxorx d a x => next (setActive s d fun l => xor (lane s a l) (getR s x))
  | .vmvi d imm => next (setActive s d fun _ => const imm)
  | .vmvx d x => next (setActive s d fun _ => getR s x)
  | .vmvv d a => next (setActive s d fun l => lane s a l)
  | .vlseg d base nf => withAddr s base 0 fun a =>
    match s.loadWords rodata a (nf * s.vl) with
    | some ws =>
      let s' := (List.range nf).foldl (fun s' f => setActive s' (d + f) fun l => ws.getD (nf * l + f) (const 0)) s
      next s'
    | none => s.fail
  | .vsseg src base nf => withAddr s base 0 fun a =>
    let ws := (List.range (nf * s.vl)).map fun q => lane s (src + q % nf) (q / nf)
    match s.storeWords a ws with
    | some s' => next s'
    | none => s.fail

def step (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) (s : State α) : State α :=
  exec vlmax rodata (prog.getD s.pc .nop) s

def run (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → State α → State α × List Instr
  | 0, s => (s, [])
  | n + 1, s =>
    if s.halted then (s, []) else
    let i := prog.getD s.pc .nop
    let (s', tr) := run vlmax rodata prog n (exec vlmax rodata i s)
    (s', i :: tr)

def execTrace (vlmax : Nat) (rodata : Array (BitVec 64)) (l : List Instr) (s : State α) : State α :=
  l.foldl (fun s i => exec vlmax rodata i s) s

/-! ## Executable harness -/

/-- The state at entry of `name(output, input, count)` (RISC-V ABI): `a0`, `a1`, `a2`, `sp = x2`. -/
def initState (input : Int → α) (zero : α) (count : Nat) (entry : Nat) : State α :=
  let g := ((((Vector.replicate 32 (⟨0, 0⟩ : Addr)).set 10 ⟨rOutput, 0⟩).set 11 ⟨rInput, 0⟩).set 12 ⟨0, count⟩).set 2 ⟨rStack, 1 <<< 20⟩
  { v := Vector.replicate 32 (Vector.replicate 8 (const 0#64))
    g := Vector.replicate 32 ⟨0, 0⟩, gd := Vector.ofFn fun n : Fin 32 => const (X86.gprWord g[n])
    k := Vector.replicate 8 0
    zf := false, cf := false, nf := false, vf := false, vl := 0
    mem := initMem input zero
    pc := entry, depth := 0, err := false, halted := false, tail := none }

/-- Run the kernel on `count` nodes of the test message; `(ok, err, instructions)`. -/
def check (vlmax : Nat) (prog : Array Instr) (rodata : Array (BitVec 64)) (entry : Nat) (count : Nat) :
    Bool × Bool × Nat :=
  let s0 : State (BitVec 64) := initState seqWord 0 count entry
  let (s, tr) := run vlmax rodata prog 400000 s0
  let outs := (List.range (4 * count)).map fun (q : Nat) => s.mem rOutput (Int.ofNat q)
  let exp := (List.range (4 * count)).map fun q => expectWord (q / 4) (q % 4)
  (outs == exp, s.err, tr.length)

end Keccaktree.Asm.Riscv
