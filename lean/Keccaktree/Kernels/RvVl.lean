import Keccaktree.Asm.RiscvEntryCtl
import Keccaktree.Kernels.Rv64X1.Program
import Keccaktree.Kernels.ZbbX1.Program
import Keccaktree.Kernels.Rvv.Program
import Keccaktree.Kernels.RvvZvkb.Program
/-!
# The RISC-V kernels never read the vector length they are entered with

For each RISC-V kernel, the index intervals where `vl` may still hold the caller's value
(`Riscv.annotate` from the entry, index 1) form a consistent annotation, checked by the kernel:
no vector instruction runs there; `vl` becomes defined only through `vsetvli`.  So every RISC-V
kernel's theorem holds for any `vl`/`vtype` at the call (unspecified by the ABI).
-/
namespace Keccaktree.Kernels.RvVl
open Keccaktree.Asm Keccaktree.Asm.Riscv

def rv64_x1 : List (Nat × Nat) := [(1, 5430)]
def zbb_x1 : List (Nat × Nat) := [(1, 3499)]
def rvv : List (Nat × Nat) := [(1, 13), (383, 384)]
def rvv_zvkb : List (Nat × Nat) := [(1, 13), (240, 241)]

set_option maxRecDepth 100000 in
theorem rv64_x1_ok : AnnOk Rv64X1.prog (vlAnn rv64_x1) := vlAnnOk_sound _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
theorem zbb_x1_ok : AnnOk ZbbX1.prog (vlAnn zbb_x1) := vlAnnOk_sound _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
theorem rvv_ok : AnnOk Rvv.prog (vlAnn rvv) := vlAnnOk_sound _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
theorem rvv_zvkb_ok : AnnOk RvvZvkb.prog (vlAnn rvv_zvkb) := vlAnnOk_sound _ _ (by decide +kernel)

theorem entries : vlAnn rv64_x1 1 = X86.Dom.all ∧ vlAnn zbb_x1 1 = X86.Dom.all ∧ vlAnn rvv 1 = X86.Dom.all ∧
    vlAnn rvv_zvkb 1 = X86.Dom.all := by decide

end Keccaktree.Kernels.RvVl
