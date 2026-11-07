import Keccaktree.Asm.Tools
import Keccaktree.Kernels.Avx2X4.Program
import Keccaktree.Kernels.NeonX3.Program
import Keccaktree.Kernels.X86X1.Program
import Keccaktree.Kernels.Avx512X9.Program
import Keccaktree.Kernels.Avx2X10.Program
import Keccaktree.Kernels.Avx2X9.Program
import Keccaktree.Kernels.Avx2X6.Program
import Keccaktree.Kernels.Avx2X5.Program
import Keccaktree.Kernels.Avx2X2.Program
import Keccaktree.Kernels.Avx2X8.Program
import Keccaktree.Kernels.Avx512vlX4.Program
import Keccaktree.Kernels.Avx512X8.Program
import Keccaktree.Kernels.Avx512vlX4d.Program
import Keccaktree.Kernels.Avx512X9d.Program
import Keccaktree.Kernels.Avx512X8d.Program
import Keccaktree.Kernels.NeonX2.Program
import Keccaktree.Kernels.Sha3X2.Program
import Keccaktree.Kernels.Sha3X3.Program
import Keccaktree.Kernels.Sha3X3r.Program
import Keccaktree.Kernels.ScalarX1.Program
import Keccaktree.Kernels.Rv64X1.Program
import Keccaktree.Kernels.ZbbX1.Program
import Keccaktree.Kernels.Rvv.Program
import Keccaktree.Kernels.RvvZvkb.Program
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
  [("avx2_x2", ⟨x86Tool, Keccaktree.Kernels.Avx2X2.prog, Keccaktree.Kernels.Avx2X2.rodata, Keccaktree.Kernels.Avx2X2.entry⟩),
   ("avx2_x5", ⟨x86Tool, Keccaktree.Kernels.Avx2X5.prog, Keccaktree.Kernels.Avx2X5.rodata, Keccaktree.Kernels.Avx2X5.entry⟩),
   ("avx2_x6", ⟨x86Tool, Keccaktree.Kernels.Avx2X6.prog, Keccaktree.Kernels.Avx2X6.rodata, Keccaktree.Kernels.Avx2X6.entry⟩),
   ("avx2_x9", ⟨x86Tool, Keccaktree.Kernels.Avx2X9.prog, Keccaktree.Kernels.Avx2X9.rodata, Keccaktree.Kernels.Avx2X9.entry⟩),
   ("avx2_x10", ⟨x86Tool, Keccaktree.Kernels.Avx2X10.prog, Keccaktree.Kernels.Avx2X10.rodata, Keccaktree.Kernels.Avx2X10.entry⟩),
   ("avx512_x9", ⟨x86Tool, Keccaktree.Kernels.Avx512X9.prog, Keccaktree.Kernels.Avx512X9.rodata, Keccaktree.Kernels.Avx512X9.entry⟩),
   ("x86_x1", ⟨x86Tool, Keccaktree.Kernels.X86X1.prog, Keccaktree.Kernels.X86X1.rodata, Keccaktree.Kernels.X86X1.entry⟩),
   ("neon_x3", ⟨armTool, Keccaktree.Kernels.NeonX3.prog, Keccaktree.Kernels.NeonX3.rodata, Keccaktree.Kernels.NeonX3.entry⟩),
   ("avx2_x4", ⟨x86Tool, Keccaktree.Kernels.Avx2X4.prog, Keccaktree.Kernels.Avx2X4.rodata, Keccaktree.Kernels.Avx2X4.entry⟩),
   ("avx2_x8", ⟨x86Tool, Keccaktree.Kernels.Avx2X8.prog, Keccaktree.Kernels.Avx2X8.rodata, Keccaktree.Kernels.Avx2X8.entry⟩),
   ("avx512vl_x4", ⟨x86Tool, Keccaktree.Kernels.Avx512vlX4.prog, Keccaktree.Kernels.Avx512vlX4.rodata, Keccaktree.Kernels.Avx512vlX4.entry⟩),
   ("avx512_x8d", ⟨x86Tool, Keccaktree.Kernels.Avx512X8d.prog, Keccaktree.Kernels.Avx512X8d.rodata, Keccaktree.Kernels.Avx512X8d.entry⟩),
   ("avx512_x9d", ⟨x86Tool, Keccaktree.Kernels.Avx512X9d.prog, Keccaktree.Kernels.Avx512X9d.rodata, Keccaktree.Kernels.Avx512X9d.entry⟩),
   ("avx512vl_x4d", ⟨x86Tool, Keccaktree.Kernels.Avx512vlX4d.prog, Keccaktree.Kernels.Avx512vlX4d.rodata, Keccaktree.Kernels.Avx512vlX4d.entry⟩),
   ("avx512_x8", ⟨x86Tool, Keccaktree.Kernels.Avx512X8.prog, Keccaktree.Kernels.Avx512X8.rodata, Keccaktree.Kernels.Avx512X8.entry⟩),
   ("neon_x2", ⟨armTool, Keccaktree.Kernels.NeonX2.prog, Keccaktree.Kernels.NeonX2.rodata, Keccaktree.Kernels.NeonX2.entry⟩),
   ("sha3_x2", ⟨armTool, Keccaktree.Kernels.Sha3X2.prog, Keccaktree.Kernels.Sha3X2.rodata, Keccaktree.Kernels.Sha3X2.entry⟩),
   ("sha3_x3", ⟨armTool, Keccaktree.Kernels.Sha3X3.prog, Keccaktree.Kernels.Sha3X3.rodata, Keccaktree.Kernels.Sha3X3.entry⟩),
   ("sha3_x3r", ⟨armTool, Keccaktree.Kernels.Sha3X3r.prog, Keccaktree.Kernels.Sha3X3r.rodata, Keccaktree.Kernels.Sha3X3r.entry⟩),
   ("scalar_x1", ⟨armTool, Keccaktree.Kernels.ScalarX1.prog, Keccaktree.Kernels.ScalarX1.rodata, Keccaktree.Kernels.ScalarX1.entry⟩),
   ("rv64_x1", ⟨riscvTool 2, Keccaktree.Kernels.Rv64X1.prog, Keccaktree.Kernels.Rv64X1.rodata, Keccaktree.Kernels.Rv64X1.entry⟩),
   ("zbb_x1", ⟨riscvTool 2, Keccaktree.Kernels.ZbbX1.prog, Keccaktree.Kernels.ZbbX1.rodata, Keccaktree.Kernels.ZbbX1.entry⟩),
   ("rvv_v2", ⟨riscvTool 2, Keccaktree.Kernels.Rvv.prog, Keccaktree.Kernels.Rvv.rodata, Keccaktree.Kernels.Rvv.entry⟩),
   ("rvv_v4", ⟨riscvTool 4, Keccaktree.Kernels.Rvv.prog, Keccaktree.Kernels.Rvv.rodata, Keccaktree.Kernels.Rvv.entry⟩),
   ("rvv_v8", ⟨riscvTool 8, Keccaktree.Kernels.Rvv.prog, Keccaktree.Kernels.Rvv.rodata, Keccaktree.Kernels.Rvv.entry⟩),
   ("rvv_zvkb_v2", ⟨riscvTool 2, Keccaktree.Kernels.RvvZvkb.prog, Keccaktree.Kernels.RvvZvkb.rodata, Keccaktree.Kernels.RvvZvkb.entry⟩),
   ("rvv_zvkb_v4", ⟨riscvTool 4, Keccaktree.Kernels.RvvZvkb.prog, Keccaktree.Kernels.RvvZvkb.rodata, Keccaktree.Kernels.RvvZvkb.entry⟩),
   ("rvv_zvkb_v8", ⟨riscvTool 8, Keccaktree.Kernels.RvvZvkb.prog, Keccaktree.Kernels.RvvZvkb.rodata, Keccaktree.Kernels.RvvZvkb.entry⟩)]

def windows (count : Nat) : List (Keccaktree.Asm.Region × Int × Int) :=
  [(rStack, 131072 - 1024, 131072), (rInput, 0, 8 * count), (rOutput, 0, 4 * count)]

def main (args : List String) : IO UInt32 := do
  match args with
  | [cmd, k, a, b, c] =>
    match kernels.find? (·.1 == k) with
    | none => IO.eprintln s!"unknown kernel {k}"; return 1
    | some (_, K) =>
      let T := K.T; let prog := K.prog; let entry := K.entry
      -- `KT_PATCH=word:value,..`: override words of the constant image (the runtime-settable `.data`
      -- thresholds, e.g. avx2_x4's small-tail maximum, to explore the code paths of every setting)
      let patches := ((← IO.getEnv "KT_PATCH").getD "").splitOn "," |>.filterMap fun p =>
        match p.splitOn ":" with
        | [a, b] => (a.toNat?).bind fun i => (b.toNat?).map fun v => (i, v)
        | _ => none
      let rodata := patches.foldl (fun (r : Array (BitVec 64)) (i, v) => r.set! i (BitVec.ofNat 64 v)) K.rodata
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
      | "paths" =>
        -- code-path inventory: for every count 0..a run the model on the test message (fuel b) and print the
        -- executed instruction indices, the halting state, the hand-over and which digests the kernel wrote
        for c in [0:count + 1] do
          let mut s : State (BitVec 64) := T.initState seqWord 0 c entry
          let mut pcs : Array Nat := #[]
          for _ in [0:b.toNat!] do
            if s.halted then break
            pcs := pcs.push s.pc
            s := T.step rodata prog s
          let oks := (List.range c).map fun n => (List.range 4).all fun w => s.mem rOutput (Int.ofNat (4 * n + w)) == expectWord n w
          IO.println s!"COUNT {c} halted={s.halted} err={s.err} tail={s.tail} rem={T.countOf s} steps={pcs.size} gd={s.gd.toList.map hex} ok={oks}"
          IO.println s!"PATH {c} {pcs.toList}"
        return 0
      | "run" =>
        -- pure execution speed: step the model `n` times, no matching
        let mut r := Run.init T rodata (randInput 1) count entry
        for _ in [0:b.toNat!] do
          if r.s.halted then break
          r := r.step T prog
        IO.println s!"pc={r.s.pc} halted={r.s.halted} err={r.s.err}"; return 0
      | _ => IO.eprintln "unknown command"; return 1
  | _ => IO.eprintln "usage: kttool scan|matches|slice|checkslice|run <kernel> <count> <n> <lanes>"; return 1
