import Keccaktree.Asm.RiscvFoot
import Keccaktree.Asm.KernelGlue
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Concrete RISC-V steps on counts

The count-dependent instructions of a RISC-V kernel's frame (the test of the count at entry,
the load / decrement / store / test of the spilled count at the loop's back edge) run on
concrete states whose count is any number; these lemmas give their effect for every count.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next
open Keccaktree.Asm.Arm (gx setX withX addr withAddr)

/-- One fetch-execute step of a running state. -/
theorem run_one (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) (S : State (BitVec 64))
    (hh : S.halted = false) : (isa vlmax).run rodata prog 1 S = exec vlmax rodata (prog.getD S.pc .nop) S := by
  show (if S.halted then S else (isa vlmax).run rodata prog 0 ((isa vlmax).exec rodata (prog.getD S.pc (isa vlmax).nop) S)) = _
  rw [hh]; rfl

theorem gx_word (S : State (BitVec 64)) (n : Nat) (a : Addr) (h : S.getGD n = gprWord a) (hwf : a.wf) :
    gx S n = some a := by
  simp only [gx, h]
  show some (wordGpr (gprWord a)) = some a
  rw [wordGpr_gprWord a hwf]

theorem getR_zero (S : State (BitVec 64)) : getR S 0 = gprWord ⟨0, 0⟩ := by
  simp only [getR, ↓reduceIte]; rfl

theorem getR_pos (S : State (BitVec 64)) (n : Nat) (h : n ≠ 0) : getR S n = S.getGD n := by
  simp only [getR, h, ↓reduceIte]

/-- `ld d, off(b)` of a word in a writable region. -/
theorem exec_ld_word (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d b : Nat) (off : Int) (a : Addr)
    (hh : S.halted = false) (hb : S.getGD b = gprWord a) (hwf : a.wf) (hal : (a.off + off) % 8 = 0) (hr : a.region ≠ rRodata) :
    exec vlmax rodata (.ld d b off) S = next (setR S d (S.mem a.region ((a.off + off) / 8))) := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr, addr, gx_word S b a hb hwf, Option.map_some,
    State.loadWords, hal, List.range_one, List.map_cons, List.map_nil, State.read, hr, Int.ofNat_eq_natCast,
    Int.natCast_zero, Int.add_zero]

/-- `sd s, off(b)` into a writable region. -/
theorem exec_sd_word (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (src b : Nat) (off : Int) (a : Addr)
    (hh : S.halted = false) (hb : S.getGD b = gprWord a) (hwf : a.wf) (hal : (a.off + off) % 8 = 0) (hr : a.region ≠ rRodata) :
    exec vlmax rodata (.sd src b off) S =
      next { S with mem := memStore S.mem a.region ((a.off + off) / 8) (getR S src) } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr, addr, gx_word S b a hb hwf, Option.map_some,
    State.storeWords, hal, ne_eq, hr, not_false_eq_true, and_self, memStoreFrom]

theorem exec_opi_eq (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d a : Nat) (k : OpI) (imm : BitVec 64)
    (hh : S.halted = false) : exec vlmax rodata (.opi d a k imm) S = next (setR S d (opi k (getR S a) imm)) := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

/-- `addi` of `-1` to a number. -/
theorem gprWord_dec (n : Int) : gprWord ⟨0, n⟩ + 0xffffffffffffffff#64 = gprWord ⟨0, n - 1⟩ := by
  rw [gprWord_add_const]
  show gprWord ⟨0, n + (0xffffffffffffffff#64).toInt⟩ = _
  rw [show (0xffffffffffffffff#64).toInt = -1 by decide]
  rfl

theorem asAddr_bv (w : BitVec 64) : LaneOps.asAddr w = some (wordGpr w) := rfl

/-- A branch on two numbers. -/
theorem exec_br_num (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (c : BCond) (a b t : Nat) (x y : Int)
    (hh : S.halted = false) (ha : getR S a = gprWord ⟨0, x⟩) (hb : getR S b = gprWord ⟨0, y⟩)
    (hx : (⟨0, x⟩ : Addr).wf) (hy : (⟨0, y⟩ : Addr).wf) :
    exec vlmax rodata (.br c a b t) S = { S with pc := if brHolds c x y then t else S.pc + 1 } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, ha, hb, asAddr_bv, wordGpr_gprWord _ hx, wordGpr_gprWord _ hy]

theorem exec_j_eq (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (t : Nat) (hh : S.halted = false) :
    exec vlmax rodata (.j t) S = { S with pc := t } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

theorem exec_ret_eq (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (hh : S.halted = false) :
    exec vlmax rodata .ret S = { S with halted := true } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

/-- Writing a general register keeps every other cut variable. -/
theorem envOf_setR_other (S : State (BitVec 64)) (n : Nat) (hn : n < 32) (x : BitVec 64) (v : Nat) (hv : v ≠ 256 + n) :
    envOf (setR S n x) v = envOf S v := by
  unfold setR
  split
  · rfl
  · unfold envOf
    split
    · rfl
    · split
      · rename_i h1 h2
        simp only [State.setGD, Vector.getD, Array.getD]
        by_cases hv' : v - 256 < 32
        · simp only [Vector.size_toArray, hv', ↓reduceDIte, Array.getInternal_eq_getElem, Vector.getElem_toArray,
            Vector.getElem_setIfInBounds, show n ≠ v - 256 by omega, ↓reduceIte]
        · simp only [Vector.size_toArray, hv', ↓reduceDIte]
      · rfl

theorem setR_getGD_same (S : State (BitVec 64)) (n : Nat) (hn : n < 32) (hn0 : n ≠ 0) (x : BitVec 64) :
    (setR S n x).getGD n = x := by
  simp only [setR, hn0, ↓reduceIte, State.getGD, State.setGD, Vector.getD, Array.getD]
  simp [hn]

theorem setR_getGD_other (S : State (BitVec 64)) (n m : Nat) (hm : m ≠ n) (x : BitVec 64) :
    (setR S n x).getGD m = S.getGD m := by
  unfold setR
  split
  · rfl
  · simp only [State.getGD, State.setGD, Vector.getD, Array.getD]
    by_cases h : m < 32
    · simp [h, Vector.getElem_setIfInBounds, Array.getElem_setIfInBounds, Ne.symm hm]
    · simp [h]

@[simp] theorem setR_mem' (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).mem = S.mem := by
  unfold setR; split <;> rfl
@[simp] theorem setR_pc (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).pc = S.pc := by
  unfold setR; split <;> rfl
@[simp] theorem setR_halted (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).halted = S.halted := by
  unfold setR; split <;> rfl
@[simp] theorem setR_err (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).err = S.err := by
  unfold setR; split <;> rfl
@[simp] theorem setR_tail (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).tail = S.tail := by
  unfold setR; split <;> rfl
@[simp] theorem setR_k (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).k = S.k := by
  unfold setR; split <;> rfl
@[simp] theorem setR_flags (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) :
    (setR S n x).zf = S.zf ∧ (setR S n x).cf = S.cf ∧ (setR S n x).nf = S.nf ∧ (setR S n x).vf = S.vf ∧
    (setR S n x).vl = S.vl ∧ (setR S n x).depth = S.depth ∧ (setR S n x).v = S.v := by
  unfold setR; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem setR_g (S : State (BitVec 64)) (n : Nat) (hn : n ≠ 0) (x : BitVec 64) :
    (setR S n x).g = S.g.setIfInBounds n ⟨0, 0⟩ := by
  simp only [setR, hn, ↓reduceIte, State.setGD]

end Keccaktree.Asm.Riscv

namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next
open Keccaktree.Asm.Arm (gx setX withX addr withAddr)

theorem exec_mv_eq (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d a : Nat) (hh : S.halted = false) :
    exec vlmax rodata (.mv d a) S = next (setR S d (getR S a)) := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

theorem exec_op_eq (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d a b : Nat) (k : Op2) (hh : S.halted = false) :
    exec vlmax rodata (.op d a b k) S = next (setR S d (op2 k (getR S a) (getR S b))) := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

theorem exec_li_eq (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d : Nat) (imm : BitVec 64) (hh : S.halted = false) :
    exec vlmax rodata (.li d imm) S = next (setR S d imm) := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]; rfl

theorem gprWord_num_toNat (r : Int) (h0 : 0 ≤ r) (h1 : r < 2 ^ 55) : (gprWord ⟨0, r⟩).toNat = r.toNat := by
  show (BitVec.ofInt 64 r).toNat = _
  rw [BitVec.toNat_ofInt]
  rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl] at h1
  have e : (((2 : Nat) ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  rw [e, Int.emod_eq_of_lt h0 (by omega)]

/-- `vsetvli d, a` with `a` holding the number `r`: `vl = min r vlmax`. -/
theorem exec_vsetvli_num (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d a : Nat) (r : Int)
    (hh : S.halted = false) (ha : getR S a = gprWord ⟨0, r⟩) (h0 : 0 ≤ r) (h1 : r < 2 ^ 55) :
    exec vlmax rodata (.vsetvli d a) S =
      next { setR S d (BitVec.ofNat 64 (min r.toNat vlmax)) with vl := min r.toNat vlmax } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, ha]
  show next { setR S d (BitVec.ofNat 64 (min (gprWord ⟨0, r⟩).toNat vlmax)) with vl := min (gprWord ⟨0, r⟩).toNat vlmax } = _
  rw [gprWord_num_toNat r h0 h1]

/-- `sub a2, a2, t0` on numbers. -/
theorem gprWord_sub_nat (r : Int) (w : Nat) :
    gprWord ⟨0, r⟩ + (~~~(BitVec.ofNat 64 w) + 1#64) = gprWord ⟨0, r - (w : Int)⟩ := by
  show BitVec.ofInt 64 r + (~~~(BitVec.ofNat 64 w) + 1#64) = BitVec.ofInt 64 (r - (w : Int))
  rw [← BitVec.neg_eq_not_add, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast]

/-- A number control word of a concrete state. -/
theorem cutVar_const_of (ctl : List Nat) (S : State (BitVec 64)) (i : Nat) (w : BitVec 64) (hi : i ∈ ctl)
    (h : envOf S i = w) (hr : (wordGpr w).region = 0) : cutVar ctl S i = .const w := by
  simp only [cutVar, List.contains_iff_mem.mpr hi, ↓reduceIte, h, hr]
  simp

/-- The alignment test of the RVV kernels on node-aligned buffers: `(a0 | a1) & 7 = 0`. -/
theorem align_zero (o i : Nat) :
    (gprWord ⟨rOutput, 32 * (o : Int)⟩ ||| gprWord ⟨rInput, 64 * (i : Int)⟩) &&& 7#64 = 0#64 := by
  rw [BitVec.and_or_distrib_right, gprWord_low3, gprWord_low3]
  show BitVec.ofInt 64 (32 * (o : Int)) &&& 7#64 ||| BitVec.ofInt 64 (64 * (i : Int)) &&& 7#64 = 0#64
  have h1 : BitVec.ofInt 64 (32 * (o : Int)) = BitVec.ofNat 64 o * 32#64 := by
    rw [show 32 * (o : Int) = ((32 * o : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]
  have h2 : BitVec.ofInt 64 (64 * (i : Int)) = BitVec.ofNat 64 i * 64#64 := by
    rw [show 64 * (i : Int) = ((64 * i : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [h1, h2]
  generalize BitVec.ofNat 64 o = x
  generalize BitVec.ofNat 64 i = y
  bv_decide

end Keccaktree.Asm.Riscv

namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next

/-! Field lemmas of `next` (rewrite with these instead of unfolding `next` by definitional
unfolding: `exact`/`show` through `next (setR …)` can make the elaborator evaluate the
register file). -/
@[simp] theorem next_getGD (s : State (BitVec 64)) (n : Nat) : (next s).getGD n = s.getGD n := rfl
@[simp] theorem next_halted (s : State (BitVec 64)) : (next s).halted = s.halted := rfl
@[simp] theorem next_err (s : State (BitVec 64)) : (next s).err = s.err := rfl
@[simp] theorem next_tail (s : State (BitVec 64)) : (next s).tail = s.tail := rfl
@[simp] theorem next_pc (s : State (BitVec 64)) : (next s).pc = s.pc + 1 := rfl
@[simp] theorem next_mem (s : State (BitVec 64)) : (next s).mem = s.mem := rfl
@[simp] theorem next_g (s : State (BitVec 64)) : (next s).g = s.g := rfl
@[simp] theorem next_k (s : State (BitVec 64)) : (next s).k = s.k := rfl
@[simp] theorem next_ctrl (s : State (BitVec 64)) : (next s).zf = s.zf ∧ (next s).cf = s.cf ∧ (next s).nf = s.nf ∧
    (next s).vf = s.vf ∧ (next s).vl = s.vl ∧ (next s).depth = s.depth := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Keccaktree.Asm.Riscv

namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next

@[simp] theorem next_zf (s : State (BitVec 64)) : (next s).zf = s.zf := rfl
@[simp] theorem next_cf (s : State (BitVec 64)) : (next s).cf = s.cf := rfl
@[simp] theorem next_nf (s : State (BitVec 64)) : (next s).nf = s.nf := rfl
@[simp] theorem next_vf (s : State (BitVec 64)) : (next s).vf = s.vf := rfl
@[simp] theorem next_vl (s : State (BitVec 64)) : (next s).vl = s.vl := rfl
@[simp] theorem next_depth (s : State (BitVec 64)) : (next s).depth = s.depth := rfl
@[simp] theorem setR_zf (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).zf = S.zf := (setR_flags S n x).1
@[simp] theorem setR_cf (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).cf = S.cf := (setR_flags S n x).2.1
@[simp] theorem setR_nf (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).nf = S.nf := (setR_flags S n x).2.2.1
@[simp] theorem setR_vf (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).vf = S.vf := (setR_flags S n x).2.2.2.1
@[simp] theorem setR_vl (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).vl = S.vl := (setR_flags S n x).2.2.2.2.1
@[simp] theorem setR_depth (S : State (BitVec 64)) (n : Nat) (x : BitVec 64) : (setR S n x).depth = S.depth :=
  (setR_flags S n x).2.2.2.2.2.1

end Keccaktree.Asm.Riscv

namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next

/-! Record updates of `mem` / `pc`, read back (rewrite lemmas, see `next_getGD`). -/
@[simp] theorem getGD_withMem (s : State (BitVec 64)) (m : Region → Int → BitVec 64) (n : Nat) :
    ({ s with mem := m } : State (BitVec 64)).getGD n = s.getGD n := rfl
@[simp] theorem getGD_withPc (s : State (BitVec 64)) (p n : Nat) : ({ s with pc := p } : State (BitVec 64)).getGD n = s.getGD n := rfl
theorem envOf_next (s : State (BitVec 64)) (i : Nat) : envOf (next s) i = envOf s i := rfl
theorem envOf_withPc (s : State (BitVec 64)) (p i : Nat) : envOf ({ s with pc := p } : State (BitVec 64)) i = envOf s i := rfl

end Keccaktree.Asm.Riscv
