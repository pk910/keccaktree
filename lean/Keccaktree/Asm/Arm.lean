import Keccaktree.Asm.X86
import Keccaktree.Asm.Exec
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# AArch64 kernel semantics

The instruction subset of `src/keccak256_{neon_x2,sha3_x2,sha3_x3,sha3_x3r,scalar_x1}.S`
on the shared machine state: `v0..v31` are the vector registers (two 64-bit
lanes of the 8), `x0..x30` the general registers `g[0..30]`, `sp = g[31]`,
the flags N/Z/C/V.  Literal loads (`ldr q, .LRC + 16r`) are resolved by the
translator to their constants.
-/
namespace Keccaktree.Asm.Arm
open Keccaktree.Asm Keccaktree.Asm.X86
open LaneOps

inductive Cond where
  | eq | ne | cs | cc | gt
  deriving Repr, DecidableEq

/-- Register operand of a load/store: a 128-bit `q` register (both lanes), a
64-bit `d` register (lane 0), or a general register. -/
inductive LReg where
  | q (n : Nat)
  | d (n : Nat)
  | x (n : Nat)
  deriving Repr, DecidableEq

inductive Instr where
  -- vector, lane-wise (`.16b` / `.2d` forms coincide for bit-wise operations)
  | eor (d a b : Nat)
  | bic (d a b : Nat)                       -- d = a & ~b
  | eor3 (d a b c : Nat)
  | bcax (d a b c : Nat)                    -- d = a ^ (b & ~c)
  | rax1 (d a b : Nat)                      -- d = a ^ rotl(b, 1)
  | xar (d a b : Nat) (n : Nat)             -- d = rotr(a ^ b, n)
  | shl (d a : Nat) (n : Nat)
  | sri (d a : Nat) (n : Nat)               -- d = (a >>> n) | (d & ~(ones >>> n))
  | addv (d a b : Nat)                      -- add v.2d
  | tbl (d a b : Nat)                       -- tbl vd.16b, {va.16b}, vb.16b (constant indices)
  | zip1 (d a b : Nat)                      -- d = [a0, b0]
  | zip2 (d a b : Nat)                      -- d = [a1, b1]
  | movv (d a : Nat)
  | movi0 (d : Nat)                         -- movi v.2d, #0
  -- general registers (the lazily rotated scalar stream)
  | eorx (d a b : Nat) (ror : Nat)          -- d = a ^ rotr(b, ror)
  | bicx (d a b : Nat) (ror : Nat)          -- d = a & ~rotr(b, ror)
  | rorx (d a : Nat) (n : Nat)
  | movx (d a : Nat)
  | movi (d : Nat) (imm : BitVec 64)
  | add (d a : Nat) (imm : Int)
  | sub (d a : Nat) (imm : Int)
  | subs (d a : Nat) (imm : Int)
  | cmp (a : Nat) (imm : Int)
  | csel (d a b : Nat) (c : Cond)
  -- loads and stores; `wb`: 0 none, 1 pre-index, 2 post-index (`off` applied to the base)
  | ldr (r : LReg) (base : Nat) (off : Int)
  | ldrlit (r : LReg) (lo hi : BitVec 64)   -- literal pool
  | str (r : LReg) (base : Nat) (off : Int)
  | ldp (r1 r2 : LReg) (base : Nat) (off : Int) (wb : Nat)
  | stp (r1 r2 : LReg) (base : Nat) (off : Int) (wb : Nat)
  -- control
  | cbz (a : Nat) (target : Nat)
  | bcond (c : Cond) (target : Nat)
  | b (target : Nat)
  | tailcall (name : String)               -- `b` to another kernel (the tail)
  | ret
  | nop
  | data                                    -- literal pool word (never executed)
  deriving Repr, DecidableEq

variable {α : Type} [LaneOps α]

/-- Lane `l` of vector register `n`. -/
def lane (s : State α) (n l : Nat) : α := (s.getV n).getD l (const 0)

/-- Write both lanes of a vector register (the lanes above are zero). -/
def setLanes (s : State α) (n : Nat) (lo hi : α) : State α :=
  s.setV n (Vector.ofFn fun i : Fin 8 => if i.val = 0 then lo else if i.val = 1 then hi else const 0)

def vop1 (s : State α) (d a : Nat) (f : α → α) : State α :=
  setLanes s d (f (lane s a 0)) (f (lane s a 1))
def vop2 (s : State α) (d a b : Nat) (f : α → α → α) : State α :=
  setLanes s d (f (lane s a 0) (lane s b 0)) (f (lane s a 1) (lane s b 1))
def vop3 (s : State α) (d a b c : Nat) (f : α → α → α → α) : State α :=
  setLanes s d (f (lane s a 0) (lane s b 0) (lane s c 0)) (f (lane s a 1) (lane s b 1) (lane s c 1))

def rotr (x : α) (n : Nat) : α := rol x ((64 - n % 64) % 64)

/-- The general registers live in `gd` (data view); a pointer or count is a
constant word in the `gprWord` encoding.  `gx` decodes it; it is `none` for a
non-constant (symbolic) word, and every instruction that needs it fails then. -/
def gx (s : State α) (n : Nat) : Option Addr := asAddr (s.getGD n)

/-- Write a general register with a pointer/count (`g` is not used by this model). -/
def setX (s : State α) (n : Nat) (a : Addr) : State α := s.setGD n (ptr a)

/-- Run `k` on the decoded register `n`, failing if it is not a constant. -/
def withX (s : State α) (n : Nat) (k : Addr → State α) : State α :=
  match gx s n with
  | some a => k a
  | none => s.fail

/-- The address of `[base, #off]`. -/
def addr (s : State α) (base : Nat) (off : Int) : Option Addr :=
  (gx s base).map fun a => ⟨a.region, a.off + off⟩

/-- Memory access at `[base, #off]`. -/
def withAddr (s : State α) (base : Nat) (off : Int) (k : Addr → State α) : State α :=
  match addr s base off with
  | some a => k a
  | none => s.fail

def condHolds (s : State α) : Cond → Bool
  | .eq => s.zf
  | .ne => !s.zf
  | .cs => s.cf
  | .cc => !s.cf
  | .gt => !s.zf && (s.nf == s.vf)

/-- Flags of `a - b` for plain numbers (the kernels only compare counts). -/
def setFlags (s : State α) (a b : Int) : State α :=
  { s with zf := a = b, cf := b ≤ a, nf := a < b, vf := false }

/-- Words to store for a register operand. -/
def regWords (s : State α) : LReg → List α
  | .q n => [lane s n 0, lane s n 1]
  | .d n => [lane s n 0]
  | .x n => [s.getGD n]

def regSize : LReg → Int
  | .q _ => 16
  | .d _ => 8
  | .x _ => 8

/-- Load a register operand from words. -/
def loadReg (s : State α) (r : LReg) (ws : List α) : State α :=
  match r with
  | .q n => setLanes s n (ws.getD 0 (const 0)) (ws.getD 1 (const 0))
  | .d n => setLanes s n (ws.getD 0 (const 0)) (lane s n 1)
  | .x n => s.setGD n (ws.getD 0 (const 0))

def next (s : State α) : State α := { s with pc := s.pc + 1 }

/-- One word of `tbl` with one source register (16 bytes `lo`, `hi`) and the
index bytes `cw`: byte `i` is source byte `cw[i]`, or zero for an index ≥ 16. -/
def tblWord (lo hi : α) (cw : BitVec 64) : α :=
  (List.range 8).foldl (fun acc i =>
    let m := ((cw >>> (8 * i)) &&& 0xff#64).toNat
    if m ≥ 16 then acc
    else
      let src := if m < 8 then and (shr lo (8 * m)) (const 0xff#64) else and (shr hi (8 * (m - 8))) (const 0xff#64)
      or acc (shl src (8 * i))) (const 0)

def exec (rodata : Array (BitVec 64)) (i : Instr) (s : State α) : State α :=
  if s.halted then s else
  match i with
  | .eor d a b => next (vop2 s d a b xor)
  | .bic d a b => next (vop2 s d a b fun x y => and x (not y))
  | .eor3 d a b c => next (vop3 s d a b c fun x y z => xor (xor x y) z)
  | .bcax d a b c => next (vop3 s d a b c fun x y z => xor x (and y (not z)))
  | .rax1 d a b => next (vop2 s d a b fun x y => xor x (rol y 1))
  | .xar d a b n => next (vop2 s d a b fun x y => rotr (xor x y) n)
  | .shl d a n => next (vop1 s d a fun x => if n < 64 then shl x n else const 0)
  | .sri d a n =>
    let keep := const (if n < 64 then (0xffffffffffffffff#64 <<< (64 - n)) else 0xffffffffffffffff#64)
    let sh : α → α := fun x => if n < 64 then shr x n else const 0
    next (setLanes s d (or (sh (lane s a 0)) (and (lane s d 0) keep)) (or (sh (lane s a 1)) (and (lane s d 1) keep)))
  | .addv d a b => next (vop2 s d a b add)
  | .tbl d a b =>
    match asConst (lane s b 0), asConst (lane s b 1) with
    | some c0, some c1 => next (setLanes s d (tblWord (lane s a 0) (lane s a 1) c0) (tblWord (lane s a 0) (lane s a 1) c1))
    | _, _ => s.fail
  | .zip1 d a b => next (setLanes s d (lane s a 0) (lane s b 0))
  | .zip2 d a b => next (setLanes s d (lane s a 1) (lane s b 1))
  | .movv d a => next (setLanes s d (lane s a 0) (lane s a 1))
  | .movi0 d => next (setLanes s d (const 0) (const 0))
  | .eorx d a b n => next (s.setGD d (xor (s.getGD a) (rotr (s.getGD b) n)))
  | .bicx d a b n => next (s.setGD d (and (s.getGD a) (not (rotr (s.getGD b) n))))
  | .rorx d a n => next (s.setGD d (rotr (s.getGD a) n))
  | .movx d a => next (s.setGD d (s.getGD a))
  | .movi d imm => next (s.setGD d (const imm))
  | .add d a imm => withX s a fun x => next (setX s d ⟨x.region, x.off + imm⟩)
  | .sub d a imm => withX s a fun x => next (setX s d ⟨x.region, x.off - imm⟩)
  | .subs d a imm => withX s a fun x =>
    if x.region = 0 then next (setFlags (setX s d ⟨0, x.off - imm⟩) x.off imm) else s.fail
  | .cmp a imm => withX s a fun x => if x.region = 0 then next (setFlags s x.off imm) else s.fail
  | .csel d a b c => next (s.setGD d (if condHolds s c then s.getGD a else s.getGD b))
  | .ldr r base off => withAddr s base off fun a =>
    match s.loadWords rodata a (regSize r / 8).toNat with
    | some ws => next (loadReg s r ws)
    | none => s.fail
  | .ldrlit r lo hi => next (loadReg s r [const lo, const hi])
  | .str r base off => withAddr s base off fun a =>
    match s.storeWords a (regWords s r) with
    | some s' => next s'
    | none => s.fail
  | .ldp r1 r2 base off wb => withAddr s base (if wb = 2 then 0 else off) fun a =>
    match s.loadWords rodata a ((regSize r1 + regSize r2) / 8).toNat with
    | some ws =>
      let s' := loadReg (loadReg s r1 (ws.take (regSize r1 / 8).toNat)) r2 (ws.drop (regSize r1 / 8).toNat)
      let s'' := if wb = 0 then s' else setX s' base ⟨a.region, a.off + (if wb = 2 then off else 0)⟩
      next s''
    | none => s.fail
  | .stp r1 r2 base off wb => withAddr s base (if wb = 2 then 0 else off) fun a =>
    match s.storeWords a (regWords s r1 ++ regWords s r2) with
    | some s' =>
      let s'' := if wb = 0 then s' else setX s' base ⟨a.region, a.off + (if wb = 2 then off else 0)⟩
      next s''
    | none => s.fail
  | .cbz a t => withX s a fun x => if x.region = 0 then { s with pc := if x.off = 0 then t else s.pc + 1 } else s.fail
  | .bcond c t => { s with pc := if condHolds s c then t else s.pc + 1 }
  | .b t => { s with pc := t }
  | .tailcall name => { s with halted := true, tail := some name }
  | .ret => { s with halted := true }
  | .nop => next s
  | .data => s.fail

def step (rodata : Array (BitVec 64)) (prog : Array Instr) (s : State α) : State α := exec rodata (prog.getD s.pc .nop) s

def run (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → State α → State α × List Instr
  | 0, s => (s, [])
  | n + 1, s =>
    if s.halted then (s, []) else
    let i := prog.getD s.pc .nop
    let (s', tr) := run rodata prog n (exec rodata i s)
    (s', i :: tr)

def execTrace (rodata : Array (BitVec 64)) (l : List Instr) (s : State α) : State α := l.foldl (fun s i => exec rodata i s) s

/-! ## Executable harness -/

/-- The state at entry of `name(output, input, count)` (AAPCS64): `x0`, `x1`, `x2`, `sp`. -/
def initState (input : Int → α) (zero : α) (count : Nat) (entry : Nat) : State α :=
  let g := ((((Vector.replicate 32 (⟨0, 0⟩ : Addr)).set 0 ⟨rOutput, 0⟩).set 1 ⟨rInput, 0⟩).set 2 ⟨0, count⟩).set 31 ⟨rStack, 1 <<< 20⟩
  { v := Vector.replicate 32 (Vector.replicate 8 (const 0#64))
    -- the legacy pointer view `g` is never read: kept constant, so cuts do not depend on the count
    g := Vector.replicate 32 ⟨0, 0⟩, gd := Vector.ofFn fun n : Fin 32 => ptr g[n]
    k := Vector.replicate 8 0
    zf := false, cf := false, nf := false, vf := false, vl := 0
    mem := initMem input zero
    pc := entry, depth := 0, err := false, halted := false, tail := none }

/-- Run the kernel on `count` nodes of the test message; `(ok, err, instructions, tail)`. -/
def check (prog : Array Instr) (rodata : Array (BitVec 64)) (entry : Nat) (count : Nat) :
    Bool × Bool × Nat × Option String :=
  let s0 : State (BitVec 64) := initState seqWord 0 count entry
  let (s, tr) := run rodata prog 400000 s0
  let done := match s.tail with
    | none => count
    | some _ => count - ((gx s 2).getD ⟨0, 0⟩).off.toNat
  let outs := (List.range (4 * done)).map fun (q : Nat) => s.mem rOutput (Int.ofNat q)
  let exp := (List.range (4 * done)).map fun q => expectWord (q / 4) (q % 4)
  (outs == exp, s.err, tr.length, s.tail)

end Keccaktree.Asm.Arm
