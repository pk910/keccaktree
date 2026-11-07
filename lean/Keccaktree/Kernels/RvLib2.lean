import Keccaktree.Kernels.Rv64X1.All
import Keccaktree.Kernels.ZbbX1.All
import Keccaktree.Kernels.RvvV2.All
import Keccaktree.Kernels.RvvZvkbV2.All
/-! # The RISC-V library at VLEN = 128 (see `RvLib`) -/
namespace Keccaktree.Kernels.RvLib
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Kernels.RiscvCommon

/-- The RISC-V library at VLEN = 128 (`vlmax = 2`): the four kernels in the order of `rvShape`. -/
def table2 : Library.Table (Riscv.isa 2) LibTable.EntryRv Digest :=
  [Rv64X1.All.kernel 2, ZbbX1.All.kernel 2, RvvV2.All.kernel, RvvZvkbV2.All.kernel]

theorem shape2 : (table2).shape = LibTable.rvShape := rfl

/-- **The RISC-V library at VLEN = 128**: from the entry state of any of its kernels (any `vl` at the call),
on any number of nodes, the library run halts without a model fault with every node's digest in place. -/
theorem lib2 : ∀ K ∈ table2, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    LibTable.EntryRv K.name off count input S → Library.LibOk (table2) K off count input S :=
  LibTable.lib_rv 2 (table2) shape2

/-- The RISC-V library at VLEN = 128 under any legal vector-length choice `ch` (RVV 1.0 §6.3). -/
def table2ch (ch : Nat → Nat) (hch : Riscv.LegalVl 2 ch) : Library.Table (Riscv.isaCh 2 ch) LibTable.EntryRv Digest :=
  [Rv64X1.All.kernel_ch 2 ch, ZbbX1.All.kernel_ch 2 ch, RvvV2.All.kernel_ch ch hch, RvvZvkbV2.All.kernel_ch ch hch]

theorem shape2ch (ch : Nat → Nat) (hch : Riscv.LegalVl 2 ch) : (table2ch ch hch).shape = LibTable.rvShape := rfl

/-- **The RISC-V library at VLEN = 128, any legal `vl` choice.** -/
theorem lib2ch (ch : Nat → Nat) (hch : Riscv.LegalVl 2 ch) : ∀ K ∈ table2ch ch hch,
    ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    LibTable.EntryRv K.name off count input S → Library.LibOk (table2ch ch hch) K off count input S :=
  LibRv.lib_rv_ch 2 ch (table2ch ch hch) (shape2ch ch hch)

end Keccaktree.Kernels.RvLib
