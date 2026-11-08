import Keccaktree.Kernels.ScalarX1.InPlaceAll
import Keccaktree.Kernels.Sha3X2.InPlaceAll
import Keccaktree.Kernels.NeonX2.InPlaceAll
import Keccaktree.Kernels.Sha3X3.InPlaceAll
import Keccaktree.Kernels.Sha3X3r.InPlaceAll
import Keccaktree.Kernels.NeonX3.InPlaceAll
set_option linter.unusedVariables false
/-!
# The in-place AArch64 library: all six kernels, every count, every node, one buffer

The table of the six AArch64 kernels' in-place theorems (`kernelAl` of each `InPlaceAll`, in the order
of `LibTable.armShape`).  `lib_inplace_arm_all`: from the in-place AArch64 entry state of any kernel
(`EntryArmAl`: one buffer, any flags), the library run — the kernel and the kernel it hands the
remaining nodes over to — halts without a model fault with every node's digest in the buffer.
-/
namespace Keccaktree.Kernels.ArmLibInPlace
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibTable

def table : Library.Table Arm.alIsa.isaAl LibArmAl.EntryArmAl LibX86.Digest :=
  [ScalarX1.InPlaceAll.kernelAl, Sha3X2.InPlaceAll.kernelAl, NeonX2.InPlaceAll.kernelAl,
   Sha3X3.InPlaceAll.kernelAl, Sha3X3r.InPlaceAll.kernelAl, NeonX3.InPlaceAll.kernelAl]

theorem table_shape : table.shape = armShape := rfl

/-- **The in-place AArch64 library theorem.** -/
theorem lib_inplace_arm_all : ∀ K ∈ table, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    LibArmAl.EntryArmAl K.name off count input S → Library.LibOk table K off count input S :=
  LibArmAl.lib_inplace_arm table table_shape

end Keccaktree.Kernels.ArmLibInPlace
