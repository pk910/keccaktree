import Keccaktree.Kernels.ZbbX1.GenSE.Seg
import Keccaktree.Kernels.ZbbX1.GenSB.Seg
import Keccaktree.Kernels.ZbbX1.GenSX.Seg
import Keccaktree.Kernels.RiscvCommon
import Keccaktree.Kernels.RvVl
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_zbb_x1` on any number of nodes

The kernel tests the count (`bnez a2`), builds its frame and spills the pointers and the count
(`GenSE`), runs a loop whose body hashes one node and advances both spilled pointers (`GenSB`),
decrements the spilled count at the back edge (`ld; addi -1; sd; beq; j`, concrete steps of
`RiscvSteps`), and restores the callee-saved registers (`GenSX`) before `ret`.  The segments are
proved once, symbolically, at every relocated position; the loop is an induction over the
iterations, iteration `k` running the body relocated by `k` nodes.

**Result** (`zbb_x1_all`): for every count `c` and node offset `off` with `64·(off+c) ≤ 2^54`, from
an entry state (`Entry`), `32 + 3443·c` steps halt without a model fault and without a tail call,
keep the output words before node `off`, and leave in output words `4(off+n)+w` the keccak256
digest of input node `off+n`, for every `n < c`.

**Alignment.** The model's buffers are regions addressed by byte offsets; the entry places the
input at offset `64·off` and the output at `32·off` of their regions, i.e. both buffers are 8-byte
aligned (region bases are 8-byte aligned).  This is the precondition of the theorem: the kernel's
byte-copy path for misaligned buffers (`lbu`/`sb`) is not modelled (`unsupported`) and not taken.
-/
namespace Keccaktree.Kernels.ZbbX1.All
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon
open Keccaktree.Asm.Riscv (setR getR brHolds run_one exec_ld_word exec_sd_word exec_opi_eq exec_br_num exec_j_eq
  exec_ret_eq getR_zero getR_pos gprWord_dec envOf_setR_other setR_getGD_same setR_getGD_other setR_mem' setR_pc
  setR_halted setR_err setR_tail setR_k setR_flags setR_g next_getGD next_halted next_err next_tail next_pc next_mem
  next_g next_k next_zf next_cf next_nf next_vf next_vl next_depth setR_zf setR_cf setR_nf setR_vf setR_vl setR_depth
  getGD_withMem getGD_withPc envOf_next envOf_withPc)
open Keccaktree.Kernels.ZbbX1 (prog rodata)

/-- The instruction set (VLEN-independent scalar kernel: any `vlmax`; the library uses 2). -/
abbrev RV : Isa := Riscv.isa 2

/-! ## The calling convention and the digests -/

/-- The entry state of a call `keccaktree_keccak256_zbb_x1(out, in, count)` at node offset `off`
(RISC-V calling convention: `a0 = x10` output, `a1 = x11` input, `a2 = x12` count, `sp = x2`):
the control part of a fresh call at the kernel's entry instruction (`pc = 1`), `sp` at the top of
the stack region, `a1`/`a0` at node `off` of the input/output regions (8-byte aligned: see the
module comment), the input region holding the message.  The vector registers, the other general
registers and every other memory word are arbitrary. -/
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
/-- The body's input invariant at node `m`, from the message. -/
theorem body_inv0 (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat) (hin : ∀ q, S.mem rInput q = input q) :
    GenSB.Inv0 (fun i => envOf S ((rho m).var i)) (fun _ => absorbNode (nodeWords input m)) := by
  have key : ∀ q : Int, envOf S ((rho m).var (memVar rInput q)) = input (q + 8 * (m : Int)) := by
    intro q; rw [rho_var_in, envOf_mem, hin]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, absorbNode_lane8 _, absorbNode_lane9 _, absorbNode_lane10 _,
    absorbNode_lane11 _, absorbNode_lane12 _, absorbNode_lane13 _, absorbNode_lane14 _, absorbNode_lane15 _,
    absorbNode_lane16 _, absorbNode_lane17 _, absorbNode_lane18 _, absorbNode_lane19 _, absorbNode_lane20 _,
    absorbNode_lane21 _, absorbNode_lane22 _, absorbNode_lane23 _, absorbNode_lane24 _⟩
  all_goals
    show envOf S ((rho m).var (memVar rInput _)) = _
    rw [key]
    simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, absorbNode_lane0, absorbNode_lane1, absorbNode_lane2,
      absorbNode_lane3, absorbNode_lane4, absorbNode_lane5, absorbNode_lane6, absorbNode_lane7, nodeWords, rotl0]
    congr 1
    simp only [Int.ofNat_eq_coe]
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The body's output invariant at node `m` is the digest of node `m`. -/
theorem body_digest (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat)
    (h : GenSB.Inv25 (fun i => envOf S ((rho m).var i)) (GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25)) :
    Digest input S m := by
  have key : ∀ w : Nat, envOf S ((rho m).var (memVar rOutput (Int.ofNat (4 * 0 + w)))) = S.mem rOutput (Int.ofNat (4 * m + w)) := by
    intro w; rw [rho_var_out, envOf_mem]; congr 1; simp only [Int.ofNat_eq_coe]; omega
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hw : ∀ w : Nat, w < 4 → S.mem rOutput (Int.ofNat (4 * m + w)) =
      L (GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25 ⟨0, by decide⟩) w := by
    intro w hw
    rw [← key w]
    rcases w with _ | _ | _ | _ | w
    · have := h0; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h1; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h2; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h3; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · omega
  intro w i hw' hi
  have hr : GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25 ⟨0, by decide⟩ =
      Spec.rounds 24 (absorbNode (nodeWords input m)) := GenSB.aat_0 _
  rw [hw w hw', hr, absorbNode_keccak, squeezeByte_eq]
  have e1 : (8 * w + i) / 8 = w := by omega
  have e2 : (8 * w + i) % 8 = i := by omega
  rw [e1, e2]
  simp only [Spec.keccakF, Fin.val_mk]

/-! ## The back edge (concrete steps on the spilled count) -/

theorem prog_1 : prog.getD 1 .nop = .br .ne 12 0 3 := by decide +kernel
theorem prog_2 : prog.getD 2 .nop = .j 3498 := by decide +kernel
theorem prog_5410 : prog.getD 3479 .nop = .ld 5 2 80 := by decide +kernel
theorem prog_5411 : prog.getD 3480 .nop = .opi 5 5 .addi 0xffffffffffffffff#64 := by decide +kernel
theorem prog_5412 : prog.getD 3481 .nop = .sd 5 2 80 := by decide +kernel
theorem prog_5413 : prog.getD 3482 .nop = .br .eq 5 0 3484 := by decide +kernel
theorem prog_5414 : prog.getD 3483 .nop = .j 20 := by decide +kernel
theorem prog_5429 : prog.getD 3498 .nop = .ret := by decide +kernel

/-- The states along the back edge from `Sb` (count word `n`). -/
def B1 (Sb : State (BitVec 64)) (n : Int) : State (BitVec 64) := Riscv.next (setR Sb 5 (gprWord ⟨0, n⟩))
def B2 (Sb : State (BitVec 64)) (n : Int) : State (BitVec 64) := Riscv.next (setR (B1 Sb n) 5 (gprWord ⟨0, n - 1⟩))
def B3 (Sb : State (BitVec 64)) (n : Int) : State (BitVec 64) :=
  Riscv.next { B2 Sb n with mem := memStore (B2 Sb n).mem rStack 131054 (gprWord ⟨0, n - 1⟩) }
def B4 (Sb : State (BitVec 64)) (n : Int) : State (BitVec 64) :=
  { B3 Sb n with pc := if brHolds .eq (n - 1) 0 then 3484 else (B3 Sb n).pc + 1 }

theorem sp_wf : (⟨rStack, 1048352⟩ : Addr).wf := by decide

set_option maxRecDepth 100000 in
/-- `ld t0, 80(sp); addi t0, t0, -1; sd t0, 80(sp); beq t0, zero, exit` on a count word `n ≥ 1`. -/
theorem run_back (Sb : State (BitVec 64)) (n : Int) (hh : Sb.halted = false) (hpc : Sb.pc = 3479)
    (hsp : Sb.getGD 2 = gprWord ⟨rStack, 1048352⟩) (hcnt : Sb.mem rStack 131054 = gprWord ⟨0, n⟩)
    (h0 : 1 ≤ n) (h1 : n < 2 ^ 55) :
    RV.run rodata prog 4 Sb = B4 Sb n := by
  have hld := exec_ld_word 2 rodata Sb 5 2 80 ⟨rStack, 1048352⟩ hh hsp sp_wf (by decide) (by decide)
  rw [show ((⟨rStack, 1048352⟩ : Addr).off + 80) / 8 = 131054 by decide, show (⟨rStack, 1048352⟩ : Addr).region = rStack from rfl,
    hcnt] at hld
  have e1 : RV.run rodata prog 1 Sb = B1 Sb n := by
    rw [run_one 2 rodata prog Sb hh, hpc, prog_5410, hld]; rfl
  have hh1 : (B1 Sb n).halted = false := by simp only [B1, next_halted, setR_halted, hh]
  have hpc1 : (B1 Sb n).pc = 3480 := by simp only [B1, next_pc, setR_pc, hpc]
  have hg1 : getR (B1 Sb n) 5 = gprWord ⟨0, n⟩ := by
    rw [getR_pos _ 5 (by decide), B1, next_getGD, setR_getGD_same Sb 5 (by decide) (by decide)]
  have e2 : RV.run rodata prog 1 (B1 Sb n) = B2 Sb n := by
    rw [run_one 2 rodata prog _ hh1, hpc1, prog_5411, exec_opi_eq 2 rodata _ 5 5 .addi _ hh1]
    rw [B2]
    show Riscv.next (setR (B1 Sb n) 5 (getR (B1 Sb n) 5 + 0xffffffffffffffff#64)) = _
    rw [hg1, gprWord_dec]
  have hh2 : (B2 Sb n).halted = false := by simp only [B2, next_halted, setR_halted, hh1]
  have hpc2 : (B2 Sb n).pc = 3481 := by simp only [B2, next_pc, setR_pc, hpc1]
  have hsp2 : (B2 Sb n).getGD 2 = gprWord ⟨rStack, 1048352⟩ := by
    rw [B2, next_getGD, setR_getGD_other _ 5 2 (by decide), B1, next_getGD, setR_getGD_other _ 5 2 (by decide), hsp]
  have hg2 : getR (B2 Sb n) 5 = gprWord ⟨0, n - 1⟩ := by
    rw [getR_pos _ 5 (by decide), B2, next_getGD, setR_getGD_same _ 5 (by decide) (by decide)]
  have hsd := exec_sd_word 2 rodata (B2 Sb n) 5 2 80 ⟨rStack, 1048352⟩ hh2 hsp2 sp_wf (by decide) (by decide)
  rw [show ((⟨rStack, 1048352⟩ : Addr).off + 80) / 8 = 131054 by decide, show (⟨rStack, 1048352⟩ : Addr).region = rStack from rfl,
    hg2] at hsd
  have e3 : RV.run rodata prog 1 (B2 Sb n) = B3 Sb n := by
    rw [run_one 2 rodata prog _ hh2, hpc2, prog_5412, hsd, B3]
  have hh3 : (B3 Sb n).halted = false := by simp only [B3, next_halted]; exact hh2
  have hpc3 : (B3 Sb n).pc = 3482 := by simp only [B3, next_pc, hpc2]
  have hg3 : getR (B3 Sb n) 5 = gprWord ⟨0, n - 1⟩ := by
    rw [getR_pos _ 5 (by decide), B3, next_getGD, getGD_withMem]; rw [getR_pos _ 5 (by decide)] at hg2; exact hg2
  have e4 : RV.run rodata prog 1 (B3 Sb n) = B4 Sb n := by
    rw [run_one 2 rodata prog _ hh3, hpc3, prog_5413,
      exec_br_num 2 rodata _ .eq 5 0 3484 (n - 1) 0 hh3 hg3 (getR_zero _)
        (by show 0 ≤ n - 1 ∧ n - 1 < 2 ^ 55; constructor <;> omega) (by decide), B4]
  rw [show 4 = 1 + 1 + 1 + 1 from rfl, Isa.run_add, Isa.run_add, Isa.run_add, e1, e2, e3, e4]

theorem B4_mem (Sb : State (BitVec 64)) (n : Int) :
    (B4 Sb n).mem = memStore Sb.mem rStack 131054 (gprWord ⟨0, n - 1⟩) := by
  simp only [B4, B3, B2, B1, next_mem, setR_mem']

theorem B4_env (Sb : State (BitVec 64)) (n : Int) (i : Nat) (h5 : i ≠ 261) (hc : i ≠ memVar rStack 131054) :
    envOf (B4 Sb n) i = envOf Sb i := by
  rw [B4, envOf_withPc, B3, envOf_next]
  have hm : (B2 Sb n).mem = Sb.mem := by simp only [B2, B1, next_mem, setR_mem']
  rw [← hm, envOf_memStore_other _ rStack 131054 _ i hc, B2, envOf_next, envOf_setR_other _ 5 (by decide) _ i h5, B1,
    envOf_next, envOf_setR_other _ 5 (by decide) _ i h5]

theorem B4_ctrl (Sb : State (BitVec 64)) (n : Int) :
    (B4 Sb n).g = (Sb.g.setIfInBounds 5 ⟨0, 0⟩).setIfInBounds 5 ⟨0, 0⟩ ∧ (B4 Sb n).k = Sb.k ∧
    (B4 Sb n).zf = Sb.zf ∧ (B4 Sb n).cf = Sb.cf ∧ (B4 Sb n).nf = Sb.nf ∧ (B4 Sb n).vf = Sb.vf ∧
    (B4 Sb n).vl = Sb.vl ∧ (B4 Sb n).depth = Sb.depth ∧ (B4 Sb n).halted = Sb.halted ∧
    (B4 Sb n).err = Sb.err ∧ (B4 Sb n).tail = Sb.tail := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [B4, B3, B2, B1, next_g, next_k, next_zf, next_cf, next_nf, next_vf, next_vl, next_depth, next_halted,
      next_err, next_tail, setR_g _ 5 (by decide : (5 : Nat) ≠ 0), setR_k, setR_halted, setR_err, setR_tail,
      setR_zf, setR_cf, setR_nf, setR_vf, setR_vl, setR_depth]

theorem B4_pc (Sb : State (BitVec 64)) (n : Int) (hpc : Sb.pc = 3479) :
    (B4 Sb n).pc = if n - 1 = 0 then 3484 else 3483 := by
  rw [B4]
  have : (B3 Sb n).pc = 3482 := by simp only [B3, B2, B1, next_pc, setR_pc, hpc]
  show (if brHolds .eq (n - 1) 0 then 3484 else (B3 Sb n).pc + 1) = _
  rw [this]
  by_cases h : n - 1 = 0 <;> simp [brHolds, h]

/-! ## The loop -/

/-- The state at the loop head before iteration `k` (of a call on `c` nodes at offset `off` from
`S0`): the body's start cut relocated by `off + k` nodes, the count word `c - k`, the message,
the earlier output words, and the digests of the nodes done. -/
@[reducible] def Head (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (k : Nat) (S : State (BitVec 64)) : Prop :=
  relocState (rho (off + k)) (cutOf GenSB.ctl0 GenSB.sc0) = cutOf GenSB.ctl0 S ∧ SliceCert.Ok S ∧
  S.mem rStack 131054 = gprWord ⟨0, (c : Int) - k⟩ ∧ (∀ q, S.mem rInput q = input q) ∧
  (∀ q : Int, q < 4 * (off : Int) → S.mem rOutput q = S0.mem rOutput q) ∧
  (∀ n, n < k → Digest input S (off + n))

/-- The state at the epilogue: its start cut (relocated by `m` nodes; only the stack pointer is a
control word), the earlier output words, and every digest. -/
@[reducible] def ExitAt (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (S : State (BitVec 64)) : Prop :=
  relocState (rho m) (cutOf GenSX.ctl0 GenSX.sc0) = cutOf GenSX.ctl0 S ∧ SliceCert.Ok S ∧
  (∀ q : Int, q < 4 * (off : Int) → S.mem rOutput q = S0.mem rOutput q) ∧
  (∀ n, n < c → Digest input S (off + n))

theorem body_len : GenSB.segLen = 3438 := by decide +kernel

/-- The body's write condition is false outside the node's own output words and the stack. -/
theorem wok_out (q : Int) (h : q < 0 ∨ 4 ≤ q) :
    ((rOutput == 3 && q != 131054) || (rOutput == 2 && decide (0 ≤ q) && decide (q < 4))) = false := by
  rcases h with h | h
  · rw [show decide (0 ≤ q) = false from decide_eq_false (by omega)]; rfl
  · rw [show decide (q < 4) = false from decide_eq_false (by omega)]
    cases decide (0 ≤ q) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One iteration of the loop.** From the loop head before iteration `k < c`, `3443` steps
(body, back edge, `j`) reach the loop head before iteration `k + 1`; after the last, `3442` steps
(body, back edge) reach the epilogue. -/
theorem iter (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (k : Nat) (S : State (BitVec 64)) (hk : k < c) (hH : Head off c input S0 k S) :
    (k + 1 < c → Head off c input S0 (k + 1) (RV.run rodata prog 3443 S)) ∧
    (k + 1 = c → ExitAt off c input S0 (off + k) (RV.run rodata prog 3442 S)) := by
  obtain ⟨hcut, hok, hcnt, hin, hpre, hdig⟩ := hH
  have hρ := rho_ok (off + k)
  have hw : (rho (off + k)).within GenSB.B := rho_within (off + k) (by omega)
  have sr := GenSB.seg_run (rho (off + k)) hρ hw S hcut hok
  have fr := GenSB.seg_frame (rho (off + k)) hρ hw S hcut hok
  have dat := GenSB.seg_data (rho (off + k)) hρ hw S hcut hok _ (body_inv0 input S (off + k) hin)
  generalize hSb : GenSB.segAt25 S = Sb at sr fr dat
  obtain ⟨hrun, hokb, hcutb⟩ := sr
  have fb := cut_fields _ _ _ _ hcutb
  -- the stack pointer at the end of the body
  have hsp : Sb.getGD 2 = gprWord ⟨rStack, 1048352⟩ := by
    have e1 := cut_word (rho (off + k)) hρ GenSB.ctl25 GenSB.sc25 Sb hcutb 258 (Or.inl (by decide))
    rw [show cutVar GenSB.ctl25 GenSB.sc25 258 = .ptr ⟨rStack, 1048352⟩ by decide +kernel, reloc_ptr_stack] at e1
    rw [← envOf_gdVar Sb 2 (by decide)]
    exact cut_ptr GenSB.ctl25 Sb 258 (by decide) _ e1
  -- the count word survives the body
  have hcntb : Sb.mem rStack 131054 = gprWord ⟨0, (c : Int) - k⟩ := by
    rw [fr rStack 131054 (by rw [rho_wshift_stack]; decide), hcnt]
  have hpcb : Sb.pc = 3479 := fb.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hhb : Sb.halted = false := hokb.2.1
  have hb' : 64 * (off + c) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hback := run_back Sb ((c : Int) - k) hhb hpcb hsp hcntb (by omega)
    (by rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; omega)
  generalize hU : B4 Sb ((c : Int) - k) = U at hback
  have hUmem : U.mem = memStore Sb.mem rStack 131054 (gprWord ⟨0, (c : Int) - k - 1⟩) := by rw [← hU]; exact B4_mem _ _
  have hUpc : U.pc = if (c : Int) - k - 1 = 0 then 3484 else 3483 := by rw [← hU]; exact B4_pc _ _ hpcb
  have hUc := B4_ctrl Sb ((c : Int) - k)
  rw [hU] at hUc
  have hUenv : ∀ i, i ≠ 261 → i ≠ memVar rStack 131054 → envOf U i = envOf Sb i := by
    intro i h5 hc; rw [← hU]; exact B4_env _ _ i h5 hc
  have hUok : SliceCert.Ok U := ⟨hUc.2.2.2.2.2.2.2.2.2.1.trans hokb.1, hUc.2.2.2.2.2.2.2.2.1.trans hokb.2.1,
    hUc.2.2.2.2.2.2.2.2.2.2.trans hokb.2.2⟩
  have hUo : ∀ q, U.mem rOutput q = Sb.mem rOutput q := by
    intro q; rw [hUmem]; exact memStore_other _ _ _ _ _ _ (Or.inl (by decide))
  have hUi : ∀ q, U.mem rInput q = Sb.mem rInput q := by
    intro q; rw [hUmem]; exact memStore_other _ _ _ _ _ _ (Or.inl (by decide))
  -- frames of the body
  have hbi : ∀ q, Sb.mem rInput q = S.mem rInput q := fun q => fr rInput q rfl
  have hbo : ∀ q : Int, q - 4 * ((off + k : Nat) : Int) < 0 → Sb.mem rOutput q = S.mem rOutput q := by
    intro q hq
    apply fr rOutput q
    rw [rho_wshift_out]
    exact wok_out _ (Or.inl hq)
  have hpre' : ∀ q : Int, q < 4 * (off : Int) → U.mem rOutput q = S0.mem rOutput q := by
    intro q hq; rw [hUo, hbo q (by omega)]; exact hpre q hq
  have hdig' : ∀ n, n < k + 1 → Digest input U (off + n) := by
    intro n hn
    by_cases hnk : n < k
    · apply digest_congr input S U (off + n) _ (hdig n hnk)
      intro w hw; rw [hUo]; exact hbo _ (by simp only [Int.ofNat_eq_coe]; omega)
    · have hnk' : n = k := by omega
      rw [hnk']
      apply digest_congr input Sb U (off + k) (fun w _ => hUo _)
      exact body_digest input Sb (off + k) dat
  have hL : ∀ L' : List Nat, (L'.all fun i => GenSB.ctl25.contains i && (decide (i < 288) || memVarRegion i == rStack)) = true →
      (L'.all fun i => i != 261 && i != memVar rStack 131054) = true → ∀ i ∈ L', envOf U i = envOf Sb i := by
    intro L' _ hL2 i hi
    have := List.all_eq_true.mp hL2 i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact hUenv i this.1 this.2
  have hrun_b : RV.run rodata prog 3442 S = U := by
    rw [show 3442 = GenSB.segLen + 4 by rw [body_len], Isa.run_add, hrun, hback]
  refine ⟨fun hk1 => ?_, fun hk1 => ?_⟩
  · -- `j loop`: back to the loop head, one node further
    have hz : ¬ ((c : Int) - k - 1 = 0) := by omega
    have hpcU : U.pc = 3483 := by rw [hUpc, if_neg hz]
    have hhU : U.halted = false := hUok.2.1
    have hj : RV.run rodata prog 1 U = { U with pc := 20 } := by
      rw [run_one 2 rodata prog U hhU, hpcU, prog_5414, exec_j_eq 2 rodata U 20 hhU]
    have hrun' : RV.run rodata prog 3443 S = { U with pc := 20 } := by
      rw [show 3443 = 3442 + 1 from rfl, Isa.run_add, hrun_b, hj]
    rw [hrun']
    refine ⟨?_, hUok, ?_, fun q => (hUi q).trans ((hbi q).trans (hin q)), hpre', hdig'⟩
    · rw [show off + (k + 1) = (off + k) + 1 by omega, ← rho_add]
      apply cut_transfer (rho (off + k)) _ hρ (Reloc.add_ok _ _ hρ (rho_ok 1)) GenSB.ctl25 GenSB.ctl0 GenSB.sc25 GenSB.sc0 Sb
        { U with pc := 20 } hcutb
        (hL_dec _ _ (by decide +kernel)) (fun i hi => (envOf_withPc U 20 i).trans (hL _ (by decide +kernel) (by decide +kernel) i hi))
        (hval_succ _ _ hρ (rho_ok 1) _ _ _ _ (by decide +kernel))
      obtain ⟨g1, k1, z1, c1, n1, v1, l1, _, d1⟩ := fb
      obtain ⟨g2, k2, z2, c2, n2, v2, l2, d2, _⟩ := hUc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
      · show U.g = _; rw [g2, g1]; decide +kernel
      · show U.k = _; rw [k2, k1]; decide +kernel
      · show U.zf = _; rw [z2, z1]; decide +kernel
      · show U.cf = _; rw [c2, c1]; decide +kernel
      · show U.nf = _; rw [n2, n1]; decide +kernel
      · show U.vf = _; rw [v2, v1]; decide +kernel
      · show U.vl = _; rw [l2, l1]; decide +kernel
      · show U.depth = _; rw [d2, d1]; decide +kernel
    · show U.mem rStack 131054 = _
      rw [hUmem, memStore_same]
      exact congrArg (fun z : Int => gprWord ⟨0, z⟩) (by omega)
  · -- the last iteration: on to the epilogue
    have hz : (c : Int) - k - 1 = 0 := by omega
    have hpcU : U.pc = 3484 := by rw [hUpc, if_pos hz]
    rw [hrun_b]
    refine ⟨?_, hUok, hpre', ?_⟩
    · apply cut_transfer (rho (off + k)) _ hρ hρ GenSB.ctl25 GenSX.ctl0 GenSB.sc25 GenSX.sc0 Sb U hcutb
        (hL_dec _ _ (by decide +kernel)) (fun i hi => hL _ (by decide +kernel) (by decide +kernel) i hi)
        (hval_same _ _ _ _ _ (by decide +kernel))
      obtain ⟨g1, k1, z1, c1, n1, v1, l1, _, d1⟩ := fb
      obtain ⟨g2, k2, z2, c2, n2, v2, l2, d2, _⟩ := hUc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [g2, g1]; decide +kernel
      · rw [k2, k1]; decide +kernel
      · rw [z2, z1]; decide +kernel
      · rw [c2, c1]; decide +kernel
      · rw [n2, n1]; decide +kernel
      · rw [v2, v1]; decide +kernel
      · rw [l2, l1]; decide +kernel
      · rw [hpcU]; decide +kernel
      · rw [d2, d1]; decide +kernel
    · intro n hn; exact hdig' n (by omega)

/-- **The loop**: from the loop head before iteration `k`, the remaining `d + 1 = c - k` iterations
reach the epilogue with every digest written. -/
theorem loop (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ d k (S : State (BitVec 64)), k + d + 1 = c → Head off c input S0 k S →
      ExitAt off c input S0 (off + c - 1) (RV.run rodata prog (3443 * d + 3442) S) := by
  intro d
  induction d with
  | zero =>
    intro k S hk hH
    have := (iter off c input S0 hb k S (by omega) hH).2 (by omega)
    rw [show off + c - 1 = off + k by omega, show 3443 * 0 + 3442 = 3442 from rfl]
    exact this
  | succ d ih =>
    intro k S hk hH
    have h1 := (iter off c input S0 hb k S (by omega) hH).1 (by omega)
    rw [show 3443 * (d + 1) + 3442 = 3443 + (3443 * d + 3442) by omega, Isa.run_add]
    exact ih (k + 1) _ (by omega) h1

theorem exit_len : GenSX.segLen = 14 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The epilogue**: the restores and `ret` halt with the memory unchanged. -/
theorem epilogue (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (hm : 64 * m ≤ 2 ^ 54)
    (U : State (BitVec 64)) (hX : ExitAt off c input S0 m U) :
    (RV.run rodata prog 15 U).halted = true ∧ (RV.run rodata prog 15 U).err = false ∧
    (RV.run rodata prog 15 U).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (RV.run rodata prog 15 U).mem rOutput q = S0.mem rOutput q) ∧
    ∀ n, n < c → Digest input (RV.run rodata prog 15 U) (off + n) := by
  obtain ⟨hcut, hok, hpre, hdig⟩ := hX
  have hρ := rho_ok m
  have hw : (rho m).within GenSX.B := rho_within m hm
  have sr := GenSX.seg_run (rho m) hρ hw U hcut hok
  have fr := GenSX.seg_frame (rho m) hρ hw U hcut hok
  generalize hSx : GenSX.segAt1 U = Sx at sr fr
  obtain ⟨hrun, hokx, hcutx⟩ := sr
  have fx := cut_fields _ _ _ _ hcutx
  have hpc : Sx.pc = 3498 := fx.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hr : RV.run rodata prog 15 U = { Sx with halted := true } := by
    rw [show 15 = GenSX.segLen + 1 by rw [exit_len], Isa.run_add, hrun, run_one 2 rodata prog Sx hokx.2.1, hpc, prog_5429,
      exec_ret_eq 2 rodata Sx hokx.2.1]
  have hmem : ∀ r q, Sx.mem r q = U.mem r q := fun r q => fr r q rfl
  rw [hr]
  refine ⟨rfl, hokx.1, hokx.2.2, fun q hq => (hmem _ _).trans (hpre q hq), fun n hn => ?_⟩
  exact digest_congr input U _ _ (fun w _ => hmem _ _) (hdig n hn)

/-! ## The whole call -/

theorem entry_len : GenSE.segLen = 17 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`keccaktree_keccak256_zbb_x1` on any number of nodes.**  For every count `c` and node offset
`off` with `64·(off + c) ≤ 2^54`, from an entry state, `32 + 3443·c` steps of the fetch-execute
loop halt without a model fault and without a tail call, keep the output words before node `off`,
and leave the keccak256 digest of input node `off + n` in output words `4(off+n) .. 4(off+n)+3`,
for every `n < c`. -/
theorem zbb_x1_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    (RV.run rodata prog (32 + 3443 * c) S).halted = true ∧
    (RV.run rodata prog (32 + 3443 * c) S).err = false ∧
    (RV.run rodata prog (32 + 3443 * c) S).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (RV.run rodata prog (32 + 3443 * c) S).mem rOutput q = S.mem rOutput q) ∧
    ∀ n, n < c → Digest input (RV.run rodata prog (32 + 3443 * c) S) (off + n) := by
  have hρ := rho_ok off
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hh : S.halted = false := hE.ok.2.1
  have hpc0 : S.pc = 1 := hE.ctrl.2.2.2.2.2.2.2.1
  have hcwf : (⟨0, (c : Int)⟩ : Addr).wf := by
    show 0 ≤ (c : Int) ∧ (c : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  -- bnez a2, frame
  have hbr : RV.run rodata prog 1 S = { S with pc := if brHolds .ne (c : Int) 0 then 3 else S.pc + 1 } := by
    rw [run_one 2 rodata prog S hh, hpc0, prog_1,
      exec_br_num 2 rodata S .ne 12 0 3 c 0 hh ((getR_pos S 12 (by decide)).trans hE.a2) (getR_zero S) hcwf (by decide)]
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- no node: `j` to the `ret`
    subst hc
    generalize hT1 : ({ S with pc := if brHolds .ne ((0 : Nat) : Int) 0 then 3 else S.pc + 1 } : State (BitVec 64)) = T1 at hbr
    have hT1pc : T1.pc = 2 := by rw [← hT1]; simp [brHolds, hpc0]
    have hT1h : T1.halted = false := by rw [← hT1]; exact hh
    have h2 : RV.run rodata prog 1 T1 = { T1 with pc := 3498 } := by
      rw [run_one 2 rodata prog T1 hT1h, hT1pc, prog_2, exec_j_eq 2 rodata T1 3498 hT1h]
    have h3 : RV.run rodata prog 1 { T1 with pc := 3498 } = { T1 with pc := 3498, halted := true } := by
      rw [run_one 2 rodata prog _ hT1h]
      exact exec_ret_eq 2 rodata { T1 with pc := 3498 } hT1h
    have hrun : RV.run rodata prog 3 S = { T1 with pc := 3498, halted := true } := by
      rw [show 3 = 1 + 1 + 1 from rfl, Isa.run_add, Isa.run_add, hbr, h2, h3]
    rw [show 32 + 3443 * 0 = 3 + 29 from rfl, Isa.run_add, hrun, Isa.run_halted _ _ _ _ _ rfl]
    have hmem : T1.mem = S.mem := by rw [← hT1]
    refine ⟨rfl, ?_, ?_, fun q _ => by show T1.mem rOutput q = _; rw [hmem], fun n hn => absurd hn (Nat.not_lt_zero _)⟩
    · show T1.err = false; rw [← hT1]; exact hE.ok.1
    · show T1.tail = none; rw [← hT1]; exact hE.ok.2.2
  · have hbrc : brHolds .ne (c : Int) 0 = true := by simp [brHolds]; omega
    rw [hbrc] at hbr
    generalize hT1 : ({ S with pc := if true = true then 3 else S.pc + 1 } : State (BitVec 64)) = T1 at hbr
    have hT1pc : T1.pc = 3 := by rw [← hT1]; rfl
    have hT1ok : SliceCert.Ok T1 := by rw [← hT1]; exact hE.ok
    have hT1env : ∀ i, envOf T1 i = envOf S i := by intro i; rw [← hT1]; rfl
    have hT1mem : T1.mem = S.mem := by rw [← hT1]
    have hwf_in : (⟨rInput, 64 * (off : Int)⟩ : Addr).wf := by
      show 0 ≤ 64 * (off : Int) ∧ 64 * (off : Int) < 2 ^ 55
      rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
    have hwf_out : (⟨rOutput, 32 * (off : Int)⟩ : Addr).wf := by
      show 0 ≤ 32 * (off : Int) ∧ 32 * (off : Int) < 2 ^ 55
      rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
    -- the entry cut, at node offset `off`
    have hc0 : relocState (rho off) (cutOf GenSE.ctl0 GenSE.sc0) = cutOf GenSE.ctl0 T1 := by
      apply relocState_cutOf (rho off) GenSE.ctl0 GenSE.sc0 T1
      · intro i hi
        simp only [GenSE.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · rw [cutVar_ptr_of GenSE.ctl0 T1 258 ⟨rStack, 1048576⟩ (by decide)
              ((hT1env 258).trans ((envOf_gdVar S 2 (by decide)).trans hE.sp)) (by decide) (by decide),
            show cutVar GenSE.ctl0 GenSE.sc0 258 = .ptr ⟨rStack, 1048576⟩ by decide +kernel, reloc_ptr_stack]
        · rw [cutVar_ptr_of GenSE.ctl0 T1 266 ⟨rOutput, 32 * (off : Int)⟩ (by decide)
              ((hT1env 266).trans ((envOf_gdVar S 10 (by decide)).trans hE.a0)) hwf_out (by show rOutput ≠ 0; decide),
            show cutVar GenSE.ctl0 GenSE.sc0 266 = .ptr ⟨rOutput, 0⟩ by decide +kernel, reloc_ptr_out, Int.zero_add]
        · rw [cutVar_ptr_of GenSE.ctl0 T1 267 ⟨rInput, 64 * (off : Int)⟩ (by decide)
              ((hT1env 267).trans ((envOf_gdVar S 11 (by decide)).trans hE.a1)) hwf_in (by show rInput ≠ 0; decide),
            show cutVar GenSE.ctl0 GenSE.sc0 267 = .ptr ⟨rInput, 0⟩ by decide +kernel, reloc_ptr_in, Int.zero_add]
      · intro i hi h; simp only [GenSE.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
      · obtain ⟨g, k, z, cf, n, v, l, p, d⟩ := hE.ctrl
        have e : T1.g = S.g ∧ T1.k = S.k ∧ T1.zf = S.zf ∧ T1.cf = S.cf ∧ T1.nf = S.nf ∧ T1.vf = S.vf ∧ T1.vl = S.vl ∧
            T1.depth = S.depth := by rw [← hT1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := e
        rw [e1, e2, e3, e4, e5, e6, e7, e8, hT1pc, g, k, z, cf, n, v, l, d]
        decide +kernel
    -- E: frame stores and spills
    have hw0 : (rho off).within (2 ^ 54) := rho_within off (by omega)
    have s1 := GenSE.seg_run (rho off) hρ hw0 T1 hc0 hT1ok
    have f1 := GenSE.seg_frame (rho off) hρ hw0 T1 hc0 hT1ok
    have m1 := GenSE.seg_moves (rho off) hρ hw0 T1 hc0 hT1ok 2097155 268 (by simp)
    generalize hT2 : GenSE.segAt1 T1 = T2 at s1 f1 m1
    obtain ⟨hrun1, hok1, hcut1⟩ := s1
    have ft1 := cut_fields _ _ _ _ hcut1
    have hH : Head off c input S 0 T2 := by
      refine ⟨?_, hok1, ?_, fun q => (f1 rInput q rfl).trans ((congrFun (congrFun hT1mem rInput) q).trans (hE.inp q)),
        fun q _ => (f1 rOutput q rfl).trans (congrFun (congrFun hT1mem rOutput) q),
        fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      · apply cut_transfer (rho off) (rho (off + 0)) hρ hρ GenSE.ctl1 GenSB.ctl0 GenSE.sc1 GenSB.sc0 T2 T2 hcut1
          (hL_dec _ _ (by decide +kernel)) (fun i _ => rfl) (hval_same _ _ _ _ _ (by decide +kernel))
        obtain ⟨g1, k1, z1, c1, n1, v1, l1, p1, d1⟩ := ft1
        exact ⟨g1.trans (by decide +kernel), k1.trans (by decide +kernel), z1.trans (by decide +kernel),
          c1.trans (by decide +kernel), n1.trans (by decide +kernel), v1.trans (by decide +kernel),
          l1.trans (by decide +kernel), p1.trans (by decide +kernel), d1.trans (by decide +kernel)⟩
      · rw [rho_var_stack off 2097155 (by decide) (by decide +kernel), Reloc.var_lt (rho off) 268 (by decide)] at m1
        rw [show (2097155 : Nat) = memVar rStack 131054 by decide +kernel, envOf_mem] at m1
        rw [m1, hT1env, (envOf_gdVar S 12 (by decide) : envOf S 268 = S.getGD 12), hE.a2]
        simp
    have hl := loop off c input S hb (c - 1) 0 T2 (by omega) hH
    have he := epilogue off c input S (off + c - 1) (by omega) _ hl
    have hrun1' : RV.run rodata prog 17 T1 = T2 := by rw [← entry_len]; exact hrun1
    rw [show 32 + 3443 * c = 1 + 17 + (3443 * (c - 1) + 3442) + 15 by omega, Isa.run_add, Isa.run_add, Isa.run_add,
      hbr, hrun1']
    exact he

/-! ## In the library -/

/-- The kernel has no `vsetvli`: its runs are the same for every vector length. -/
theorem scalar : prog.all (fun i => !i.usesVlmax) = true := by decide +kernel

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

end Keccaktree.Kernels.ZbbX1.All
