import Keccaktree.Kernels.Rv64X1.All
import Keccaktree.Kernels.ZbbX1.All
import Keccaktree.Kernels.RvvV4.All
import Keccaktree.Kernels.RvvZvkbV4.All
/-! # The RISC-V library at VLEN = 256 (see `RvLib`) -/
namespace Keccaktree.Kernels.RvLib
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Kernels.RiscvCommon

/-- The RISC-V library at VLEN = 256 (`vlmax = 4`): the four kernels in the order of `rvShape`. -/
def table4 : Library.Table (Riscv.isa 4) LibTable.EntryRv Digest :=
  [Rv64X1.All.kernel 4, ZbbX1.All.kernel 4, RvvV4.All.kernel, RvvZvkbV4.All.kernel]

theorem shape4 : (table4).shape = LibTable.rvShape := rfl

/-- **The RISC-V library at VLEN = 256**: from the entry state of any of its kernels (any `vl` at the call),
on any number of nodes, the library run halts without a model fault with every node's digest in place. -/
theorem lib4 : ∀ K ∈ table4, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    LibTable.EntryRv K.name off count input S → Library.LibOk (table4) K off count input S :=
  LibTable.lib_rv 4 (table4) shape4

/-- The RISC-V library at VLEN = 256 under any legal vector-length choice `ch` (RVV 1.0 §6.3). -/
def table4ch (ch : Nat → Nat) (hch : Riscv.LegalVl 4 ch) : Library.Table (Riscv.isaCh 4 ch) LibTable.EntryRv Digest :=
  [Rv64X1.All.kernel_ch 4 ch, ZbbX1.All.kernel_ch 4 ch, RvvV4.All.kernel_ch ch hch, RvvZvkbV4.All.kernel_ch ch hch]

theorem shape4ch (ch : Nat → Nat) (hch : Riscv.LegalVl 4 ch) : (table4ch ch hch).shape = LibTable.rvShape := rfl

/-- **The RISC-V library at VLEN = 256, any legal `vl` choice.** -/
theorem lib4ch (ch : Nat → Nat) (hch : Riscv.LegalVl 4 ch) : ∀ K ∈ table4ch ch hch,
    ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    LibTable.EntryRv K.name off count input S → Library.LibOk (table4ch ch hch) K off count input S :=
  LibRv.lib_rv_ch 4 ch (table4ch ch hch) (shape4ch ch hch)

end Keccaktree.Kernels.RvLib
