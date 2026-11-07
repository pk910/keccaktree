import Keccaktree.Asm.ArmEntryCtl
import Keccaktree.Kernels.ScalarX1.Program
import Keccaktree.Kernels.Sha3X2.Program
import Keccaktree.Kernels.NeonX2.Program
import Keccaktree.Kernels.Sha3X3.Program
import Keccaktree.Kernels.Sha3X3r.Program
import Keccaktree.Kernels.NeonX3.Program
/-!
# The AArch64 kernels never read the flags they are entered with

For each AArch64 kernel, the index intervals where the NZCV flags may still hold the caller's
values (computed by `Arm.annotate`, the may-dirty fixpoint from the entry) form a consistent
annotation, checked by the kernel: no `b.cond`/`csel` reads a flag there, and the flags become
clean only through `cmp`/`subs`.  With `LibArm.mkKernelArm` this makes every AArch64 kernel's
theorem hold for any flags at entry (a tail call from `sha3_x3`/`neon_x3`/`sha3_x3r`, or a call).
-/
namespace Keccaktree.Kernels.ArmFlags
open Keccaktree.Asm Keccaktree.Asm.Arm

def scalar_x1 : List (Nat × Nat) := [(0, 2443), (2444, 2451)]
def sha3_x2 : List (Nat × Nat) := [(0, 9), (1599, 1604)]
def neon_x2 : List (Nat × Nat) := [(0, 9), (3788, 3793)]
def sha3_x3 : List (Nat × Nat) := [(0, 1)]
def sha3_x3r : List (Nat × Nat) := [(0, 1)]
def neon_x3 : List (Nat × Nat) := [(0, 1)]

set_option maxRecDepth 100000 in
theorem scalar_x1_ok : AnnOk ScalarX1.prog (flagAnn scalar_x1) := flagAnnOk_sound _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
theorem sha3_x2_ok : AnnOk Sha3X2.prog (flagAnn sha3_x2) := flagAnnOk_sound _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
theorem neon_x2_ok : AnnOk NeonX2.prog (flagAnn neon_x2) := flagAnnOk_sound _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
theorem sha3_x3_ok : AnnOk Sha3X3.prog (flagAnn sha3_x3) := flagAnnOk_sound _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
theorem sha3_x3r_ok : AnnOk Sha3X3r.prog (flagAnn sha3_x3r) := flagAnnOk_sound _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
theorem neon_x3_ok : AnnOk NeonX3.prog (flagAnn neon_x3) := flagAnnOk_sound _ _ (by decide +kernel)

/-- The entry (index 0) is in the dirty set of every annotation. -/
theorem entries : flagAnn scalar_x1 0 = X86.Dom.all ∧ flagAnn sha3_x2 0 = X86.Dom.all ∧
    flagAnn neon_x2 0 = X86.Dom.all ∧ flagAnn sha3_x3 0 = X86.Dom.all ∧ flagAnn sha3_x3r 0 = X86.Dom.all ∧
    flagAnn neon_x3 0 = X86.Dom.all := by decide

end Keccaktree.Kernels.ArmFlags
