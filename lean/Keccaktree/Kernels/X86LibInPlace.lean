import Keccaktree.Asm.LibAlias
import Keccaktree.Kernels.X86Lib
import Keccaktree.Kernels.X86X1.InPlaceAll
import Keccaktree.Kernels.Avx2X2.InPlaceAll
import Keccaktree.Kernels.Avx2X4.InPlaceAllV
import Keccaktree.Kernels.Avx2X5.InPlaceAll
import Keccaktree.Kernels.Avx2X6.InPlaceAll
import Keccaktree.Kernels.Avx2X8.InPlaceAll
import Keccaktree.Kernels.Avx2X9.InPlaceAll
import Keccaktree.Kernels.Avx2X10.InPlaceAllV
import Keccaktree.Kernels.Avx512vlX4.InPlaceAll
import Keccaktree.Kernels.Avx512vlX4d.InPlaceAll
import Keccaktree.Kernels.Avx512X8.InPlaceAll
import Keccaktree.Kernels.Avx512X8d.InPlaceAll
import Keccaktree.Kernels.Avx512X9.InPlaceAll
import Keccaktree.Kernels.Avx512X9d.InPlaceAll
set_option linter.unusedVariables false
/-!
# The in-place x86-64 library: all fourteen kernels, every count, every node, one buffer

The table of the x86-64 kernels' in-place theorems (`kernelAl` of each `InPlaceAll`, in the order of
`LibTable.x86Shape`; avx2_x4 and avx2_x10 under the configured thresholds, `InPlaceAllV.kernelAl v`).
`lib_inplace_x86_all`: for every configuration, from the in-place x86-64 entry state of any kernel
(`EntryAlX86`: output = input buffer), the library run halts without a model fault with every node's
digest in the buffer.
-/
namespace Keccaktree.Kernels.X86LibInPlace
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibAlias Keccaktree.Kernels.X86Lib

def table (cfg : Cfg) : Library.Table X86.isaAl EntryAlX86 LibX86.Digest :=
  [X86X1.InPlaceAll.kernelAl, Avx2X2.InPlaceAll.kernelAl, Avx2X4.InPlaceAllV.kernelAl cfg.x4 cfg.hx4,
   Avx2X5.InPlaceAll.kernelAl, Avx2X6.InPlaceAll.kernelAl, Avx2X8.InPlaceAll.kernelAl, Avx2X9.InPlaceAll.kernelAl,
   Avx2X10.InPlaceAllV.kernelAl cfg.x10 cfg.hx10, Avx512vlX4.InPlaceAll.kernelAl, Avx512vlX4d.InPlaceAll.kernelAl,
   Avx512X8.InPlaceAll.kernelAl, Avx512X8d.InPlaceAll.kernelAl, Avx512X9.InPlaceAll.kernelAl,
   Avx512X9d.InPlaceAll.kernelAl]

theorem table_shape (cfg : Cfg) : (table cfg).shape = LibTable.x86Shape := rfl

/-- **The in-place x86-64 library theorem**, for every configuration of the calibrated thresholds. -/
theorem lib_inplace_x86_all (cfg : Cfg) : ∀ K ∈ table cfg, ∀ (off count : Nat) (input : Int → BitVec 64)
    (S : State (BitVec 64)), EntryAlX86 K.name off count input S → Library.LibOk (table cfg) K off count input S :=
  lib_inplace_x86 table table_shape cfg

end Keccaktree.Kernels.X86LibInPlace
