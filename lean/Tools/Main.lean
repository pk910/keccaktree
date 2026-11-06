import Keccaktree.Asm.Tools
import Keccaktree.Kernels.Avx2X4.Program
import Keccaktree.Kernels.Avx2X8.Program
import Keccaktree.Kernels.Avx512vlX4.Program
import Keccaktree.Kernels.Avx512X8.Program
import Keccaktree.Kernels.NeonX2.Program
import Keccaktree.Kernels.Sha3X2.Program
import Keccaktree.Kernels.Sha3X3.Program
import Keccaktree.Kernels.Sha3X3r.Program
import Keccaktree.Kernels.ScalarX1.Program
/-! `kttool`: the proof-generation tools as a native executable.

    kttool scan    <kernel> <count> <fuel> <lanes>
    kttool matches <kernel> <count> <steps> <lanes>
-/
open Keccaktree.Asm.X86 Keccaktree.Asm.X86.Tools

/-- A kernel: its ISA tool, program, constants, entry. -/
structure Kernel where
  T : IsaTool
  prog : Array T.Instr
  rodata : Array (BitVec 64)
  entry : Nat

def kernels : List (String × Kernel) :=
  [("avx2_x4", ⟨x86Tool, Keccaktree.Kernels.Avx2X4.prog, Keccaktree.Kernels.Avx2X4.rodata, Keccaktree.Kernels.Avx2X4.entry⟩),
   ("avx2_x8", ⟨x86Tool, Keccaktree.Kernels.Avx2X8.prog, Keccaktree.Kernels.Avx2X8.rodata, Keccaktree.Kernels.Avx2X8.entry⟩),
   ("avx512vl_x4", ⟨x86Tool, Keccaktree.Kernels.Avx512vlX4.prog, Keccaktree.Kernels.Avx512vlX4.rodata, Keccaktree.Kernels.Avx512vlX4.entry⟩),
   ("avx512_x8", ⟨x86Tool, Keccaktree.Kernels.Avx512X8.prog, Keccaktree.Kernels.Avx512X8.rodata, Keccaktree.Kernels.Avx512X8.entry⟩),
   ("neon_x2", ⟨armTool, Keccaktree.Kernels.NeonX2.prog, Keccaktree.Kernels.NeonX2.rodata, Keccaktree.Kernels.NeonX2.entry⟩),
   ("sha3_x2", ⟨armTool, Keccaktree.Kernels.Sha3X2.prog, Keccaktree.Kernels.Sha3X2.rodata, Keccaktree.Kernels.Sha3X2.entry⟩),
   ("sha3_x3", ⟨armTool, Keccaktree.Kernels.Sha3X3.prog, Keccaktree.Kernels.Sha3X3.rodata, Keccaktree.Kernels.Sha3X3.entry⟩),
   ("sha3_x3r", ⟨armTool, Keccaktree.Kernels.Sha3X3r.prog, Keccaktree.Kernels.Sha3X3r.rodata, Keccaktree.Kernels.Sha3X3r.entry⟩),
   ("scalar_x1", ⟨armTool, Keccaktree.Kernels.ScalarX1.prog, Keccaktree.Kernels.ScalarX1.rodata, Keccaktree.Kernels.ScalarX1.entry⟩)]

def windows (count : Nat) : List (Keccaktree.Asm.Region × Int × Int) :=
  [(rStack, 131072 - 1024, 131072), (rInput, 0, 8 * count), (rOutput, 0, 4 * count)]

def main (args : List String) : IO UInt32 := do
  match args with
  | [cmd, k, a, b, c] =>
    match kernels.find? (·.1 == k) with
    | none => IO.eprintln s!"unknown kernel {k}"; return 1
    | some (_, K) =>
      let T := K.T; let prog := K.prog; let rodata := K.rodata; let entry := K.entry
      let count := a.toNat!
      match cmd with
      | "scan" => scan T prog rodata entry count b.toNat! c.toNat! (windows count); return 0
      | "checkslice" => checkSlice T prog rodata entry count b.toNat! c.toNat!; return 0
      | "slice" => sliceLit T prog rodata entry count b.toNat! c.toNat!; return 0
      | "probespec" => probeSpec count b.toNat!; return 0
      | "probe" => probe T prog rodata entry count b.toNat! c.toNat!; return 0
      | "scanregs" => scan T prog rodata entry count b.toNat! c.toNat! []; return 0
      | "scanmem" => scan T prog rodata entry count b.toNat! 0 (windows count); return 0
      | "matches" => matchesAt T prog rodata entry count b.toNat! c.toNat! (windows count); return 0
      | "run" =>
        -- pure execution speed: step the model `n` times, no matching
        let mut r := Run.init T rodata (randInput 1) count entry
        for _ in [0:b.toNat!] do
          if r.s.halted then break
          r := r.step T prog
        IO.println s!"pc={r.s.pc} halted={r.s.halted} err={r.s.err}"; return 0
      | _ => IO.eprintln "unknown command"; return 1
  | _ => IO.eprintln "usage: kttool scan|matches|slice|checkslice|run <kernel> <count> <n> <lanes>"; return 1
