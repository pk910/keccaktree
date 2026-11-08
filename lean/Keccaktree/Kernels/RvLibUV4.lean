import Keccaktree.Kernels.RvLibU
import Keccaktree.Kernels.RvvV4.AllUM
import Keccaktree.Kernels.RvvZvkbV4.AllUM
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The RISC-V library at any buffer alignment, all four kernels

For buffers at byte offsets `mi`, `mo` (the machine addresses modulo 8) and VLEN = 256
(`vlmax = 4`): the four kernels (`rv64_x1`, `zbb_x1`: `AllU.kernelU`; `rvv`, `rvv_zvkb`:
`AllUM.kernelU`, the bounce path if `mi ||| mo ≠ 0`) in the order of `rvShape`, and the library theorem
`lib4U`.  Deterministic `vl = min(avl, VLMAX)` (the RVV bounce path is not proved
under other legal `vl` choices).
-/
namespace Keccaktree.Kernels.RvLibUV
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Kernels.RiscvBytes

def table4U (mi mo : Nat) (hmi : mi < 8) (hmo : mo < 8) :
    Library.Table (Riscv.isa 4) (LibRvU.EntryRvU mi mo) (DigestB mi mo) :=
  [Rv64X1.AllU.kernelU 4 mi mo hmi hmo, ZbbX1.AllU.kernelU 4 mi mo hmi hmo, RvvV4.AllUM.kernelU mi mo hmi hmo,
    RvvZvkbV4.AllUM.kernelU mi mo hmi hmo]


/-- **The RISC-V library at VLEN = 256, any buffer alignment.** -/
theorem lib4U (mi mo : Nat) (hmi : mi < 8) (hmo : mo < 8) :
    ∀ K ∈ table4U mi mo hmi hmo, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      LibRvU.EntryRvU mi mo K.name off count input S → Library.LibOk (table4U mi mo hmi hmo) K off count input S :=
  LibRvU.lib_rvU 4 mi mo _ rfl

end Keccaktree.Kernels.RvLibUV
