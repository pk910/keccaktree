import Keccaktree.Kernels.Rv64X1.AllU
import Keccaktree.Kernels.ZbbX1.AllU
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The RISC-V library with misaligned buffers: the scalar kernels

For buffers at any byte offsets `mi`, `mo` (the machine addresses modulo 8) and any vector length,
the scalar kernels `rv64_x1` and `zbb_x1` (`AllU.kernelU`) form a library without tail calls whose
library theorem holds (`libU`, and `libU_ch` under any vector-length choice).  The RVV kernels at
misaligned buffers are not part of it (see `notes/rvu.md`).
-/
namespace Keccaktree.Kernels.RvLibU
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Kernels.RiscvBytes

/-- The scalar RISC-V kernels' shape (rank 0, no tail calls). -/
def scalarShape : List (String × Nat × List String) := [(LibTable.sym "rv64_x1", 0, []), (LibTable.sym "zbb_x1", 0, [])]

theorem scalarShape_noTail : LibRvU.noTail scalarShape = true := by decide

/-- The scalar kernels at byte offsets `mi`, `mo` and `vlmax` lanes per vector register. -/
def tableU (vlmax mi mo : Nat) (hmi : mi < 8) (hmo : mo < 8) :
    Library.Table (Riscv.isa vlmax) (LibRvU.EntryRvU mi mo) (DigestB mi mo) :=
  [Rv64X1.AllU.kernelU vlmax mi mo hmi hmo, ZbbX1.AllU.kernelU vlmax mi mo hmi hmo]

theorem shapeU (vlmax mi mo : Nat) (hmi : mi < 8) (hmo : mo < 8) : (tableU vlmax mi mo hmi hmo).shape = scalarShape := rfl

/-- **The scalar RISC-V library at any buffer alignment**: from the entry state of either kernel (any
`vl` at the call, the input buffer at byte `mi + 64·off` and the output buffer at byte `mo + 32·off`
of their regions), on any number of nodes, the run halts without a model fault with every node's
digest in the output bytes `mo + 32·(off+n) …`. -/
theorem libU (vlmax mi mo : Nat) (hmi : mi < 8) (hmo : mo < 8) :
    ∀ K ∈ tableU vlmax mi mo hmi hmo, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      LibRvU.EntryRvU mi mo K.name off count input S → Library.LibOk (tableU vlmax mi mo hmi hmo) K off count input S :=
  LibRvU.lib_noTail _ scalarShape (shapeU vlmax mi mo hmi hmo) scalarShape_noTail

/-- The same tables under the vector-length choice `ch`. -/
def tableU_ch (vlmax mi mo : Nat) (ch : Nat → Nat) (hmi : mi < 8) (hmo : mo < 8) :
    Library.Table (Riscv.isaCh vlmax ch) (LibRvU.EntryRvU mi mo) (DigestB mi mo) :=
  [Rv64X1.AllU.kernelU_ch vlmax mi mo ch hmi hmo, ZbbX1.AllU.kernelU_ch vlmax mi mo ch hmi hmo]

theorem shapeU_ch (vlmax mi mo : Nat) (ch : Nat → Nat) (hmi : mi < 8) (hmo : mo < 8) :
    (tableU_ch vlmax mi mo ch hmi hmo).shape = scalarShape := rfl

theorem libU_ch (vlmax mi mo : Nat) (ch : Nat → Nat) (hmi : mi < 8) (hmo : mo < 8) :
    ∀ K ∈ tableU_ch vlmax mi mo ch hmi hmo, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      LibRvU.EntryRvU mi mo K.name off count input S → Library.LibOk (tableU_ch vlmax mi mo ch hmi hmo) K off count input S :=
  LibRvU.lib_noTail _ scalarShape (shapeU_ch vlmax mi mo ch hmi hmo) scalarShape_noTail

end Keccaktree.Kernels.RvLibU
