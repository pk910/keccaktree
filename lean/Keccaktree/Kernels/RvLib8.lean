import Keccaktree.Kernels.Rv64X1.All
import Keccaktree.Kernels.ZbbX1.All
import Keccaktree.Kernels.RvvV8.All
import Keccaktree.Kernels.RvvZvkbV8.All
/-! # The RISC-V library at VLEN = 512 (see `RvLib`) -/
namespace Keccaktree.Kernels.RvLib
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Kernels.RiscvCommon

/-- The RISC-V library at VLEN = 512 (`vlmax = 8`): the four kernels in the order of `rvShape`. -/
def table8 : Library.Table (Riscv.isa 8) LibTable.EntryRv Digest :=
  [Rv64X1.All.kernel 8, ZbbX1.All.kernel 8, RvvV8.All.kernel, RvvZvkbV8.All.kernel]

theorem shape8 : (table8).shape = LibTable.rvShape := rfl

/-- **The RISC-V library at VLEN = 512**: from the entry state of any of its kernels (any `vl` at the call),
on any number of nodes, the library run halts without a model fault with every node's digest in place. -/
theorem lib8 : ∀ K ∈ table8, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    LibTable.EntryRv K.name off count input S → Library.LibOk (table8) K off count input S :=
  LibTable.lib_rv 8 (table8) shape8

/-- The RISC-V library at VLEN = 512 under any legal vector-length choice `ch` (RVV 1.0 §6.3). -/
def table8ch (ch : Nat → Nat) (hch : Riscv.LegalVl 8 ch) : Library.Table (Riscv.isaCh 8 ch) LibTable.EntryRv Digest :=
  [Rv64X1.All.kernel_ch 8 ch, ZbbX1.All.kernel_ch 8 ch, RvvV8.All.kernel_ch ch hch, RvvZvkbV8.All.kernel_ch ch hch]

theorem shape8ch (ch : Nat → Nat) (hch : Riscv.LegalVl 8 ch) : (table8ch ch hch).shape = LibTable.rvShape := rfl

/-- **The RISC-V library at VLEN = 512, any legal `vl` choice.** -/
theorem lib8ch (ch : Nat → Nat) (hch : Riscv.LegalVl 8 ch) : ∀ K ∈ table8ch ch hch,
    ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    LibTable.EntryRv K.name off count input S → Library.LibOk (table8ch ch hch) K off count input S :=
  LibRv.lib_rv_ch 8 ch (table8ch ch hch) (shape8ch ch hch)

end Keccaktree.Kernels.RvLib
