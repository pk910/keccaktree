import Keccaktree.Kernels.ZbbX1.AllU
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_zbb_x1` on any number of nodes (aligned buffers): the library interface

The case `mi = mo = 0` of `AllU.zbb_x1_allU` (any buffer alignment), in the form the library uses:
the entry state `Entry` (buffers at node offset `off` of their regions), the word-level digest
`Digest`, and the kernel of the RISC-V library (`kernel`, `kernel_ch`).

**Result** (`zbb_x1_all`): for every count `c` and node offset `off` with `64·(off+c) ≤ 2^54`, from
an entry state, `32 + 3443·c` steps halt without a model fault and without a tail call, keep the
output words before node `off`, and leave in output words `4(off+n)+w` the keccak256 digest of input
node `off+n`, for every `n < c`.
-/
namespace Keccaktree.Kernels.ZbbX1.All
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon Keccaktree.Kernels.RiscvBytes
open Keccaktree.Kernels.ZbbX1 (prog rodata)

/-- The instruction set (VLEN-independent scalar kernel: any `vlmax`; the library uses 2). -/
abbrev RV : Isa := Riscv.isa 2

/-- The entry state of a call `keccaktree_keccak256_zbb_x1(out, in, count)` at node offset `off`
(RISC-V calling convention: `a0 = x10` output, `a1 = x11` input, `a2 = x12` count, `sp = x2`), the
buffers at node `off` of their (8-byte aligned) regions; `AllU.EntryU` with `mi = mo = 0`. -/
structure Entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.vl = 0 ∧ S.pc = 1 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  a2 : S.getGD 12 = gprWord ⟨0, count⟩
  sp : S.getGD 2 = gprWord ⟨rStack, 1048576⟩
  a1 : S.getGD 11 = gprWord ⟨rInput, 64 * off⟩
  a0 : S.getGD 10 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`keccaktree_keccak256_zbb_x1` on any number of nodes**, aligned buffers. -/
theorem zbb_x1_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    (RV.run rodata prog (32 + 3443 * c) S).halted = true ∧
    (RV.run rodata prog (32 + 3443 * c) S).err = false ∧
    (RV.run rodata prog (32 + 3443 * c) S).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (RV.run rodata prog (32 + 3443 * c) S).mem rOutput q = S.mem rOutput q) ∧
    ∀ n, n < c → Digest input (RV.run rodata prog (32 + 3443 * c) S) (off + n) := by
  have hE' : AllU.EntryU 0 0 off c input S :=
    ⟨hE.ctrl, hE.ok, hE.a2, hE.sp, hE.a1.trans (congrArg (fun o => gprWord ⟨rInput, o⟩) (by push_cast; omega)),
      hE.a0.trans (congrArg (fun o => gprWord ⟨rOutput, o⟩) (by push_cast; omega)), hE.inp⟩
  have h := AllU.zbb_x1_allU 0 0 off c input S (by decide) (by decide) hE' hb
  rw [AllU.iterSteps_00, Nat.mul_comm c 3443] at h
  obtain ⟨hh, he, ht, hp, hd⟩ := h
  refine ⟨hh, he, ht, fun q hq => ?_, fun n hn => (digestB_zero input _ (off + n)).mp (hd n hn)⟩
  apply word_ext
  intro t ht'
  rw [← byteAt_word _ q t ht', ← byteAt_word _ q t ht']
  exact hp _ (by push_cast; omega)

/-! ## In the library -/

set_option maxRecDepth 100000 in
/-- The kernel has no `vsetvli`: its runs are the same for every vector length. -/
theorem scalar : prog.toList.all (fun i => !i.usesVlmax) = true := by decide +kernel

/-- What the library needs (`LibRv.NormThmRv`), for every `vlmax`: from the library's entry state
(normalised control part, `pc` at the entry), the run halts with every digest and no tail call. -/
theorem norm_thm (vlmax : Nat) : LibRv.NormThmRv vlmax rodata prog 1 (fun _ c => 32 + 3443 * c) [] := by
  intro off count input S hE hb hpc
  obtain ⟨⟨g, k, z, cf, n, v, l, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩ := hE
  have hE' : Entry off count input S := ⟨⟨g, k, z, cf, n, v, l, hpc, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩
  obtain ⟨hh, he, ht, hp, hd⟩ := zbb_x1_all off count input S hE' hb
  show Library.Outcome _ _ _ off count input S ((Riscv.isa vlmax).run rodata prog (32 + 3443 * count) S)
  rw [Riscv.run_vlmax vlmax 2 rodata prog scalar]
  exact ⟨hh, he, hp, Or.inl ⟨ht, hd⟩⟩

/-- `keccaktree_keccak256_zbb_x1` as a kernel of the RISC-V library at any `vlmax` (rank 0: it
hands nothing over; any `vl` at entry). -/
def kernel (vlmax : Nat) : Library.KernelThm (Riscv.isa vlmax) LibTable.EntryRv Digest :=
  LibRv.mkKernelRv vlmax (LibTable.sym "zbb_x1") 0 [] rodata prog 1 (fun _ c => 32 + 3443 * c)
    (Riscv.vlAnn RvVl.zbb_x1) RvVl.zbb_x1_ok RvVl.entries.2.1 (norm_thm vlmax)

/-- Under any vector-length choice (`Riscv.isaCh`): the kernel has no `vsetvli`, the same run. -/
theorem norm_thm_ch (vlmax : Nat) (ch : Nat → Nat) :
    LibRv.NormThmRvCh vlmax ch rodata prog 1 (fun _ c => 32 + 3443 * c) [] := by
  intro off count input S hE hb hpc
  have h := norm_thm vlmax off count input S hE hb hpc
  show Library.Outcome _ _ _ off count input S ((Riscv.isaCh vlmax ch).run rodata prog (32 + 3443 * count) S)
  rw [Riscv.run_ch_scalar vlmax ch rodata prog scalar]
  exact h

/-- `keccaktree_keccak256_zbb_x1` in the RISC-V library under the vector-length choice `ch`. -/
def kernel_ch (vlmax : Nat) (ch : Nat → Nat) : Library.KernelThm (Riscv.isaCh vlmax ch) LibTable.EntryRv Digest :=
  LibRv.mkKernelRvCh vlmax ch (LibTable.sym "zbb_x1") 0 [] rodata prog 1 (fun _ c => 32 + 3443 * c)
    (Riscv.vlAnn RvVl.zbb_x1) RvVl.zbb_x1_ok RvVl.entries.2.1 (norm_thm_ch vlmax ch)

end Keccaktree.Kernels.ZbbX1.All
