import Keccaktree.Kernels.Rv64X1.InPlaceAll
import Keccaktree.Kernels.ZbbX1.InPlaceAll
import Keccaktree.Kernels.RvvV2.InPlaceAll
import Keccaktree.Kernels.RvvZvkbV2.InPlaceAll
import Keccaktree.Kernels.RvvV4.InPlaceAll
import Keccaktree.Kernels.RvvZvkbV4.InPlaceAll
import Keccaktree.Kernels.RvvV8.InPlaceAll
import Keccaktree.Kernels.RvvZvkbV8.InPlaceAll
set_option linter.unusedVariables false
/-!
# The in-place RISC-V library at VLEN 128, 256, 512 (`vlmax` = 2, 4, 8)

One table per vector length, the four kernels' in-place theorems (`kernelAl`) in the order of
`LibTable.rvShape`.  `lib_inplace<V>`: from the in-place RISC-V entry state of any kernel (`EntryRvAl`:
output = input buffer, any `vl` at the call), the library run halts without a model fault with every
node's digest in the buffer.
-/
namespace Keccaktree.Kernels.RvLibInPlace
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibRvAl Keccaktree.Asm.LibTable

def table2 : Library.Table (Riscv.alIsa 2).isaAl EntryRvAl LibX86.Digest :=
  [Rv64X1.InPlaceAll.kernelAl 2, ZbbX1.InPlaceAll.kernelAl 2, RvvV2.InPlaceAll.kernelAl, RvvZvkbV2.InPlaceAll.kernelAl]
def table4 : Library.Table (Riscv.alIsa 4).isaAl EntryRvAl LibX86.Digest :=
  [Rv64X1.InPlaceAll.kernelAl 4, ZbbX1.InPlaceAll.kernelAl 4, RvvV4.InPlaceAll.kernelAl, RvvZvkbV4.InPlaceAll.kernelAl]
def table8 : Library.Table (Riscv.alIsa 8).isaAl EntryRvAl LibX86.Digest :=
  [Rv64X1.InPlaceAll.kernelAl 8, ZbbX1.InPlaceAll.kernelAl 8, RvvV8.InPlaceAll.kernelAl, RvvZvkbV8.InPlaceAll.kernelAl]

theorem shape2 : table2.shape = rvShape := rfl
theorem shape4 : table4.shape = rvShape := rfl
theorem shape8 : table8.shape = rvShape := rfl

/-- **The in-place RISC-V library at VLEN = 128.** -/
theorem lib_inplace2 : ∀ K ∈ table2, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryRvAl K.name off count input S → Library.LibOk table2 K off count input S :=
  lib_inplace_rv 2 table2 shape2

/-- **The in-place RISC-V library at VLEN = 256.** -/
theorem lib_inplace4 : ∀ K ∈ table4, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryRvAl K.name off count input S → Library.LibOk table4 K off count input S :=
  lib_inplace_rv 4 table4 shape4

/-- **The in-place RISC-V library at VLEN = 512.** -/
theorem lib_inplace8 : ∀ K ∈ table8, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryRvAl K.name off count input S → Library.LibOk table8 K off count input S :=
  lib_inplace_rv 8 table8 shape8

end Keccaktree.Kernels.RvLibInPlace
