import Keccaktree.Asm.X86Ann
import Keccaktree.Asm.X86AliasIsa
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
/-!
# AVX-512 kernels in place: the control half

The AVX-512 kernels enter the separate-region library through agent x86b's `mkKernelAnn` (a per-index
dirty-set annotation `annIv entry lo hi Din Dom1` with internal calls, checked by `annJOk`; the run
from any control state is `run_ovr_annJ`).  The in-place library needs, besides the kernel's
`AccessThm`, the same fact as a `CtlThm` of `X86.alIsa` (`LibAliasGen`): `ctlThm_annJ`.  Then
**`mkKernelAnnAl`** (the arguments of `mkKernelAnn` and the access theorem) is a kernel of the in-place
x86 library (`KernelThm X86.isaAl EntryAlX86 Digest`, through `LibAlias.mkKernelAlOf`).

Requires x86b's `Asm/X86Ann.lean` (branch all-x86b).
-/
namespace Keccaktree.Asm.LibAlias
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibAliasGen

/-- **The control theorem of an annotated x86 kernel** (from x86b's `annJOk` certificate). -/
theorem ctlThm_annJ (rodata : Array (BitVec 64)) (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (bhi lo hi : Nat) (Din : Dom) (hann : annJOk prog bhi entry lo hi Din Dom1 = true) :
    CtlThm X86.alIsa Entry rodata prog entry steps := by
  have hbe : bhi ≤ entry := by
    simp only [annJOk, Bool.and_eq_true, decide_eq_true_eq] at hann; exact hann.1.2
  apply ctlThm_of_pred X86.alIsa Entry rodata prog entry steps (annIv entry lo hi Din Dom1)
    (LibX86.annIv_entry entry lo hi Din Dom1) (DepthInv bhi)
  · intro off count input S hE hpc
    unfold DepthInv
    rw [if_neg (show ¬ (normCtl S).pc < bhi from fun h => by
      have : (normCtl S).pc = entry := hpc
      omega)]
    exact hE.ctrl.2.2.2.2.2.2.2
  · intro p; rfl
  · intro n s c hP he
    exact run_ovr_annJ rodata prog bhi _ (annJOk_sound prog bhi entry lo hi Din Dom1 hann) n s c hP he

/-- **An annotated (AVX-512) x86 kernel of the in-place library**: the arguments of `mkKernelAnn` and the
kernel's access theorem. -/
def mkKernelAnnAl (name : String) (rank : Nat) (targets : List String) (rodata : Array (BitVec 64))
    (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat) (bhi lo hi : Nat) (Din : Dom)
    (hann : annJOk prog bhi entry lo hi Din Dom1 = true)
    (h : NormThm rodata prog entry steps targets) (ha : AccessThm rodata prog entry steps) :
    Library.KernelThm X86.isaAl EntryAlX86 Digest :=
  mkKernelAlOf (mkKernelAnn name rank targets rodata prog entry steps bhi lo hi Din hann h) ha
    (ctlThm_annJ rodata prog entry steps bhi lo hi Din hann)

end Keccaktree.Asm.LibAlias
