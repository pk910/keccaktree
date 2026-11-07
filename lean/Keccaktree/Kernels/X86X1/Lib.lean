import Keccaktree.Kernels.X86X1.All
import Keccaktree.Asm.LibX86
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_x86_x1` as a kernel of the library

`x86_x1_all` is proved from a fresh call's control state.  The library enters a
kernel also by a tail call, with whatever flags, mask registers and vector
length the calling kernel left: `LibX86.mkKernel` covers that, from two facts
the kernel checks on the program: the first 8 instructions (six pushes,
`sub rsp, 440`, `test rdx, rdx`) write ZF/CF before any read, and no
instruction touches the masks, `nf`/`vf` or `vl`.
-/
namespace Keccaktree.Kernels.X86X1.Lib
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86
open Keccaktree.Kernels.X86X1 (prog rodata)

theorem norm_thm : NormThm rodata prog 0 (fun _ c => 21 + 4269 * c) [] := by
  intro off c input S hE hb hpc
  have hE' : All.Entry off c input S :=
    ⟨⟨hE.ctrl.1, hE.ctrl.2.1, hE.ctrl.2.2.1, hE.ctrl.2.2.2.1, hE.ctrl.2.2.2.2.1, hE.ctrl.2.2.2.2.2.1,
      hE.ctrl.2.2.2.2.2.2.1, hpc, hE.ctrl.2.2.2.2.2.2.2⟩, hE.ok, hE.rdx, hE.rsp, hE.rsi, hE.rdi, hE.inp⟩
  obtain ⟨hh, he, ht, hp, hd⟩ := All.x86_x1_all off c input S hE' hb
  exact ⟨hh, he, hp, Or.inl ⟨ht, fun n hn => hd n hn⟩⟩

/-- `keccaktree_keccak256_x86_x1` as a kernel of the library (rank 0: it hands nothing over). -/
def kernel : Library.KernelThm X86.isa EntryX86 Digest :=
  mkKernel "keccaktree_keccak256_x86_x1" 0 [] rodata prog 0 (fun _ c => 21 + 4269 * c) 8 (by decide +kernel) (by decide +kernel)
    (fun _ _ => by omega) norm_thm

theorem ranks_ok : Library.RanksOk [kernel] := Library.ranksOk_of_shape _ (by decide +kernel)

/-- **The library theorem on the table `[x86_x1]`**: from the library's x86 entry state — any
flags, masks and vector length — the run halts without a model fault with every node's digest
in place. -/
theorem lib_x86_x1 (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hS : EntryX86 "keccaktree_keccak256_x86_x1" off count input S) : Library.LibOk [kernel] kernel off count input S :=
  Library.lib_correct [kernel] 0 (by simp [kernel, mkKernel]) ranks_ok digest_local _ kernel (by simp) off count input S
    (Nat.le_refl _) hS

end Keccaktree.Kernels.X86X1.Lib
