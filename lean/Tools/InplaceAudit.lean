import Keccaktree.Kernels.Avx2X10.Program
import Keccaktree.Kernels.Avx2X2.Program
import Keccaktree.Kernels.Avx2X4.Program
import Keccaktree.Kernels.Avx2X5.Program
import Keccaktree.Kernels.Avx2X6.Program
import Keccaktree.Kernels.Avx2X8.Program
import Keccaktree.Kernels.Avx2X9.Program
import Keccaktree.Kernels.Avx512X8.Program
import Keccaktree.Kernels.Avx512X8d.Program
import Keccaktree.Kernels.Avx512X9.Program
import Keccaktree.Kernels.Avx512X9d.Program
import Keccaktree.Kernels.Avx512vlX4.Program
import Keccaktree.Kernels.Avx512vlX4d.Program
import Keccaktree.Kernels.X86X1.Program
import Keccaktree.Asm.Exec
import Keccaktree.Asm.Alias
/-! `inplaceaudit`: every x86 kernel model on counts 0 .. 64 + 2·NODES, called in place
(`keccaktree_hash(buf, buf, n)`): (1) the access condition of `Alias.lean` along the separate-region run
from `dupState` (`accessCheck`, sound for `AccessRun`), (2) the aliased machine itself (`runAl`): the
digests the kernel writes land in the storage. -/
open Keccaktree.Asm Keccaktree.Asm.X86

def kernelsX86 : List (String × Array Instr × Array (BitVec 64) × Nat × Nat) := [
  ("Avx2X10", Keccaktree.Kernels.Avx2X10.prog, Keccaktree.Kernels.Avx2X10.rodata, Keccaktree.Kernels.Avx2X10.entry, 10),
  ("Avx2X2", Keccaktree.Kernels.Avx2X2.prog, Keccaktree.Kernels.Avx2X2.rodata, Keccaktree.Kernels.Avx2X2.entry, 2),
  ("Avx2X4", Keccaktree.Kernels.Avx2X4.prog, Keccaktree.Kernels.Avx2X4.rodata, Keccaktree.Kernels.Avx2X4.entry, 4),
  ("Avx2X5", Keccaktree.Kernels.Avx2X5.prog, Keccaktree.Kernels.Avx2X5.rodata, Keccaktree.Kernels.Avx2X5.entry, 5),
  ("Avx2X6", Keccaktree.Kernels.Avx2X6.prog, Keccaktree.Kernels.Avx2X6.rodata, Keccaktree.Kernels.Avx2X6.entry, 6),
  ("Avx2X8", Keccaktree.Kernels.Avx2X8.prog, Keccaktree.Kernels.Avx2X8.rodata, Keccaktree.Kernels.Avx2X8.entry, 8),
  ("Avx2X9", Keccaktree.Kernels.Avx2X9.prog, Keccaktree.Kernels.Avx2X9.rodata, Keccaktree.Kernels.Avx2X9.entry, 9),
  ("Avx512X8", Keccaktree.Kernels.Avx512X8.prog, Keccaktree.Kernels.Avx512X8.rodata, Keccaktree.Kernels.Avx512X8.entry, 8),
  ("Avx512X8d", Keccaktree.Kernels.Avx512X8d.prog, Keccaktree.Kernels.Avx512X8d.rodata, Keccaktree.Kernels.Avx512X8d.entry, 8),
  ("Avx512X9", Keccaktree.Kernels.Avx512X9.prog, Keccaktree.Kernels.Avx512X9.rodata, Keccaktree.Kernels.Avx512X9.entry, 9),
  ("Avx512X9d", Keccaktree.Kernels.Avx512X9d.prog, Keccaktree.Kernels.Avx512X9d.rodata, Keccaktree.Kernels.Avx512X9d.entry, 9),
  ("Avx512vlX4", Keccaktree.Kernels.Avx512vlX4.prog, Keccaktree.Kernels.Avx512vlX4.rodata, Keccaktree.Kernels.Avx512vlX4.entry, 4),
  ("Avx512vlX4d", Keccaktree.Kernels.Avx512vlX4d.prog, Keccaktree.Kernels.Avx512vlX4d.rodata, Keccaktree.Kernels.Avx512vlX4d.entry, 4),
  ("X86X1", Keccaktree.Kernels.X86X1.prog, Keccaktree.Kernels.X86X1.rodata, Keccaktree.Kernels.X86X1.entry, 1)]

/-- Materialise the memory on the windows the kernels touch (input/output words `[0, L)`, the stack
below `2^20`): extensionally the same function, but reads no longer walk the closure chain of every
earlier step. -/
def compact (L : Nat) (s : State (BitVec 64)) : State (BitVec 64) :=
  let t1 := Array.ofFn fun (q : Fin L) => s.mem rInput q.val
  let t2 := Array.ofFn fun (q : Fin L) => s.mem rOutput q.val
  let t3 := Array.ofFn fun (q : Fin 4096) => s.mem rStack (131072 - 4096 + q.val)
  let old := s.mem
  { s with mem := fun r q =>
      if r = rInput ∧ 0 ≤ q ∧ q < L then t1.getD q.toNat 0
      else if r = rOutput ∧ 0 ≤ q ∧ q < L then t2.getD q.toNat 0
      else if r = rStack ∧ 131072 - 4096 ≤ q ∧ q < 131072 then t3.getD (q - (131072 - 4096)).toNat 0
      else old r q }

/-- `accessCheck` and `runAl` step by step, compacting the memory every 512 steps. -/
partial def audit (rodata : Array (BitVec 64)) (prog : Array Instr) (L : Nat) (fuel : Nat) (B : Int)
    (s t : State (BitVec 64)) (k : Nat) (ok : Bool) : Bool × State (BitVec 64) :=
  if fuel = 0 ∨ s.halted then (ok && t.halted == s.halted, t) else
  let i := prog.getD s.pc .nop
  let s' := exec rodata i s
  let ok' := ok && !s'.err && (reads s i).all (fun c => c.1 != rInput || decide (B ≤ c.2)) &&
    (writes s i).all (fun c => c.1 != rInput)
  let t' := execAl rodata (prog.getD t.pc .nop) t
  let (s', t') := if k % 256 = 255 then (compact L s', compact L t') else (s', t')
  audit rodata prog L (fuel - 1) (bumpB B s i) s' t' (k + 1) ok'

def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  for (name, prog, rodata, entry, n) in kernelsX86.filter (fun k => args.isEmpty || args.contains k.1) do
    let mut okc := 0
    for count in List.range (65 + 2 * n) do
      let t0 : State (BitVec 64) := initState seqWord 0 count entry
      let L := 8 * count + 64
      let (acc, tf) := audit rodata prog L 400000 0 (dupState t0) t0 0 true
      let done := match tf.tail with
        | none => count
        | some _ => count - ((gx tf 2).getD ⟨0, 0⟩).off.toNat
      let dig := (List.range (4 * done)).all fun (q : Nat) => tf.mem rInput (Int.ofNat q) == expectWord (q / 4) (q % 4)
      if acc && dig && !tf.err && tf.halted then okc := okc + 1
      else
        IO.println s!"{name} count {count}: access {acc} digests {dig} err {tf.err} halted {tf.halted}"
        bad := bad + 1
    IO.println s!"{name}: {okc} of {65 + 2 * n} counts in place OK"
    (← IO.getStdout).flush
  IO.println s!"failures: {bad}"
  return (if bad = 0 then 0 else 1)
