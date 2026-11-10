import Keccaktree.Asm.LibTable
import Keccaktree.Kernels.X86X1.Lib
import Keccaktree.Kernels.Avx2X2.Lib
import Keccaktree.Kernels.Avx2X4.LibV
import Keccaktree.Kernels.Avx2X5.Lib
import Keccaktree.Kernels.Avx2X6.Lib
import Keccaktree.Kernels.Avx2X8.Lib
import Keccaktree.Kernels.Avx2X9.Lib
import Keccaktree.Kernels.Avx2X10.LibV
import Keccaktree.Kernels.Avx512vlX4.Lib
import Keccaktree.Kernels.Avx512vlX4d.Lib
import Keccaktree.Kernels.Avx512X8.Lib
import Keccaktree.Kernels.Avx512X8d.Lib
import Keccaktree.Kernels.Avx512X9.Lib
import Keccaktree.Kernels.Avx512X9d.Lib
set_option linter.unusedVariables false
/-!
# The x86-64 library: all fourteen kernels, every count, every node

The table of the x86-64 kernels' library theorems (`kernel` of each `Lib`, in the order of
`LibTable.x86Shape`).  avx2_x4 and avx2_x10 read a threshold the library calibrates at run time
(word 112 of their constant image); their entries are the kernels under the configured values
(`LibV.kernel v`, proved for every `v < 2^64`), so the table depends on the configuration `cfg`.
`lib_x86_all`: for every configuration, from the x86-64 entry state of any kernel (`EntryX86`: any
flags, masks and vector length at a call or tail call), the library run halts without a model fault
with every node's digest in the output buffer.
-/
namespace Keccaktree.Kernels.X86Lib
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibTable

/-- A runtime configuration: the calibrated threshold words of avx2_x4 and avx2_x10. -/
structure Cfg where
  x4 : Nat
  x10 : Nat
  hx4 : x4 < 2 ^ 64
  hx10 : x10 < 2 ^ 64

def table (cfg : Cfg) : Library.Table X86.isa EntryX86 Digest :=
  [X86X1.Lib.kernel, Avx2X2.Lib.kernel, Avx2X4.LibV.kernel cfg.x4 cfg.hx4, Avx2X5.Lib.kernel,
   Avx2X6.Lib.kernel, Avx2X8.Lib.kernel, Avx2X9.Lib.kernel, Avx2X10.LibV.kernel cfg.x10 cfg.hx10,
   Avx512vlX4.Lib.kernel, Avx512vlX4d.Lib.kernel, Avx512X8.Lib.kernel, Avx512X8d.Lib.kernel,
   Avx512X9.Lib.kernel, Avx512X9d.Lib.kernel]

theorem table_shape (cfg : Cfg) : (table cfg).shape = x86Shape := rfl

/-- **The x86-64 library theorem**, for every configuration of the calibrated thresholds. -/
theorem lib_x86_all (cfg : Cfg) : ∀ K ∈ table cfg, ∀ (off count : Nat) (input : Int → BitVec 64)
    (S : State (BitVec 64)), EntryX86 K.name off count input S → Library.LibOk (table cfg) K off count input S :=
  lib_x86 table table_shape cfg

end Keccaktree.Kernels.X86Lib
