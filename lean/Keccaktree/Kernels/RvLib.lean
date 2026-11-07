import Keccaktree.Kernels.Rv64X1.All
import Keccaktree.Kernels.ZbbX1.All
import Keccaktree.Kernels.RvvV2.All
import Keccaktree.Kernels.RvvZvkbV2.All
import Keccaktree.Kernels.RvvV4.All
import Keccaktree.Kernels.RvvZvkbV4.All
import Keccaktree.Kernels.RvvV8.All
import Keccaktree.Kernels.RvvZvkbV8.All
/-!
# The RISC-V library, every kernel on any number of nodes

One table per vector length the RVV kernels are proved for: `vlmax = VLEN/64 ∈ {2, 4, 8}`
(VLEN 128, 256, 512).  The scalar kernels (`rv64_x1`, `zbb_x1`) have no `vsetvli` and are proved for
every `vlmax` (`Riscv.run_vlmax`).  **Coverage gap**: the dispatcher selects `rvv`/`rvv_zvkb` for every
VLEN ≥ 128; VLEN ≥ 1024 (`vlmax ≥ 16`) is not covered — the model's vector registers hold 8 lanes
(`State.v : Vector (Vector α 8) 32`), so `Riscv.isa vlmax` with `vlmax > 8` is not a faithful model and
no theorem is stated for it.  `lib<V>ch`: the same under any legal vector-length choice
(`Riscv.LegalVl`, RVV 1.0 §6.3), not only `vl = min(avl, VLMAX)`.
-/
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
