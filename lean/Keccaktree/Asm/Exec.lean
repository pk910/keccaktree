import Keccaktree.Asm.X86
import Keccaktree.Spec
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
Executable harness: run a kernel model on concrete input and compare the
output region with the specification.
-/
namespace Keccaktree.Asm.X86

open Keccaktree.Asm

/-- The initial memory: the input region holding `input` (word index → word),
everything else `zero`. -/
def initMem (input : Int → α) (zero : α) : Region → Int → α :=
  fun r q => if r = rInput then input q else zero

/-- The state at entry of `name(output, input, count)` (SysV): `rdi`, `rsi`,
`rdx`, the stack pointer high in the stack region. -/
def initState (input : Int → α) (zero : α) (count : Nat) (entry : Nat) [LaneOps α] : State α :=
  { v := Vector.replicate 32 (Vector.replicate 8 (LaneOps.const 0#64))
    -- the legacy pointer view `g` is never read: kept constant, so cuts do not depend on the count
    g := Vector.replicate 32 ⟨0, 0⟩
    gd := Vector.ofFn fun n : Fin 32 => LaneOps.ptr
      (((((Vector.replicate 32 (⟨0, 0⟩ : Addr)).set 7 ⟨rOutput, 0⟩).set 6 ⟨rInput, 0⟩).set 2 ⟨0, count⟩).set 4 ⟨rStack, 1 <<< 20⟩)[n]
    k := Vector.replicate 8 0
    zf := false, cf := false, nf := false, vf := false, vl := 0
    mem := initMem input zero
    pc := entry, depth := 0, err := false, halted := false, tail := none }

/-- Little-endian words of the test message `seq`: byte `i = 7 i + 3`. -/
def seqWord (q : Int) : BitVec 64 :=
  if q < 0 then 0 else
  Keccak.Spec.ld64 (fun i => BitVec.ofNat 8 (i * 7 + 3)) (8 * q.toNat)

/-- Expected digest word `w` of node `k` of that message. -/
def expectWord (k w : Nat) : BitVec 64 :=
  Keccak.Spec.ld64 (fun i => Keccak.Spec.keccak256 64 (fun j => BitVec.ofNat 8 ((64 * k + j) * 7 + 3)) i) (8 * w)

/-- Run the kernel on `count` nodes; `(ok, error flag, executed instructions, tail call)`.
A tail call to the generic kernel for the last `rdx` nodes is honoured by
checking only the digests the kernel itself wrote and that the handed-over
pointers and count are right. -/
def check (prog : Array Instr) (rodata : Array (BitVec 64)) (entry : Nat) (count : Nat) :
    Bool × Bool × Nat × Option String :=
  let s0 : State (BitVec 64) := initState seqWord 0 count entry
  let (s, tr) := run rodata prog 200000 s0
  let done := match s.tail with
    | none => count
    | some _ => count - ((gx s 2).getD ⟨0, 0⟩).off.toNat
  let outs := (List.range (4 * done)).map fun (q : Nat) => s.mem rOutput (Int.ofNat q)
  let exp := (List.range (4 * done)).map fun q => expectWord (q / 4) (q % 4)
  let handover := match s.tail with
    | none => true
    | some _ => gx s 6 == some ⟨rInput, 64 * done⟩ && gx s 7 == some ⟨rOutput, 32 * done⟩
  (outs == exp && handover, s.err, tr.length, s.tail)

end Keccaktree.Asm.X86
