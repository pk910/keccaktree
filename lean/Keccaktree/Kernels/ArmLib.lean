import Keccaktree.Kernels.ScalarX1.All
import Keccaktree.Kernels.Sha3X2.All
import Keccaktree.Kernels.NeonX2.All
import Keccaktree.Kernels.Sha3X3.All
import Keccaktree.Kernels.Sha3X3r.All
import Keccaktree.Kernels.NeonX3.All
set_option linter.unusedVariables false
/-!
# The AArch64 library: all six kernels, every count, every node

The table of the six AArch64 kernels' all-count theorems (in the order of `LibTable.armShape`:
scalar_x1, sha3_x2, neon_x2 of rank 0; sha3_x3 → scalar_x1, sha3_x3r → sha3_x2, neon_x3 → scalar_x1
of rank 1).  `lib_arm_all`: from the library's AArch64 entry state of any kernel (any flags) on any
number of nodes, the run — the kernel and the kernel it hands the remaining nodes over to — halts
without a model fault with every node's keccak256 digest in place.
-/
namespace Keccaktree.Kernels.ArmLib
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibTable

def table : Library.Table Arm.isa EntryArm LibX86.Digest :=
  [ScalarX1.All.kernel, Sha3X2.All.kernel, NeonX2.All.kernel, Sha3X3.All.kernel, Sha3X3r.All.kernel, NeonX3.All.kernel]

theorem table_shape : table.shape = armShape := rfl

/-- **The AArch64 library theorem.** -/
theorem lib_arm_all : ∀ K ∈ table, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryArm K.name off count input S → Library.LibOk table K off count input S :=
  lib_arm table table_shape

end Keccaktree.Kernels.ArmLib
