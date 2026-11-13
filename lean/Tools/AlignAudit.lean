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
import Tools.AlignIdx
/-! `alignaudit`: run every x86 kernel model on counts 0 .. 64 + 2·NODES and report every aligned vector
move (`vmovdqa`/`vmovdqa64`, indices from `Tools.AlignIdx`) whose address is not in the stack region (or a 32-byte aligned constant) (the
model checks only 8-byte alignment; on the machine these moves need 32/64-byte alignment, which only the
realigned stack frame guarantees). -/
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

def addrOf (s : State (BitVec 64)) : Instr → Option Addr
  | .vmov _ _ (.mem m) _ => memAddr? s m
  | .vstore _ m _ => memAddr? s m
  | _ => none

partial def go (rodata : Array (BitVec 64)) (prog : Array Instr) (al : List Nat) (s : State (BitVec 64))
    (fuel : Nat) (acc : Nat × List (Nat × Addr)) : Nat × List (Nat × Addr) :=
  if fuel = 0 ∨ s.halted then acc else
  let i := prog.getD s.pc .nop
  let acc := if al.contains s.pc then
      match addrOf s i with
      | some a => (acc.1 + 1, if a.region = rStack ∨ (a.region = rRodata ∧ a.off % 32 = 0) then acc.2 else (s.pc, a) :: acc.2)
      | none => (acc.1 + 1, acc.2)
    else acc
  go rodata prog al (exec rodata i s) (fuel - 1) acc

def main : IO UInt32 := do
  let mut bad := 0
  for (name, prog, rodata, entry, n) in kernelsX86 do
    let al := (alignedIdx.lookup name).getD []
    let mut execs := 0
    for count in List.range (65 + 2 * n) do
      let s0 : State (BitVec 64) := initState seqWord 0 count entry
      let (k, offs) := go rodata prog al s0 400000 (0, [])
      execs := execs + k
      for (pc, a) in offs do
        IO.println s!"{name} count {count}: aligned move at {pc} addresses region {a.region} offset {a.off}"
        bad := bad + 1
    IO.println s!"{name}: {al.length} aligned moves, {execs} executions checked"
  IO.println s!"non-stack aligned accesses: {bad}"
  return (if bad = 0 then 0 else 1)
