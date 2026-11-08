import Keccaktree.Kernels.RvvCommon
import Keccaktree.Kernels.RiscvBytesV
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The RVV kernels with misaligned buffers: concrete steps

`rvv`/`rvv_zvkb` take the bounce path when `a7 = (a0 | a1) & 7 ≠ 0`: the batch is capped at 8 nodes
(`li t4, 8; bleu t3, t4; mv t3, t4`), the node bytes are copied into the stack buffer with
`vsetvli e8, m8; vle8 v24, (a1); vse8 v24, (sp)` and loaded from there (`vlseg8e64 (sp)`, the start
of the batch body `GenM<w>`), the digests are stored into the buffer (`vsseg4e64 (sp)`) and copied out
with `vsetvli e8, m4; vle8 v24, (sp); vse8 v24, (a0)`.  This module: the straight-line steps of the
frame on concrete states (`StV`: control part without `vl`, pc, `vl`, registers, memory).
-/
namespace Keccaktree.Kernels.RvvCommonU
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon Keccaktree.Kernels.RiscvBytes
open Keccaktree.Asm.Riscv (setR getR brHolds run_one exec_br_num getR_zero getR_pos setR_pc setR_mem' setR_halted
  setR_err setR_tail setR_k setR_g setR_zf setR_cf setR_nf setR_vf setR_vl setR_depth exec_opi_eq exec_op_eq exec_mv_eq
  exec_li_eq exec_vsetvli_num)

/-- The control part of the RVV kernels' states (any `vl`). -/
def CtlV (T : State (BitVec 64)) : Prop :=
  T.g = Vector.replicate 32 ⟨0, 0⟩ ∧ T.k = Vector.replicate 8 0 ∧ T.zf = false ∧ T.cf = false ∧ T.nf = false ∧
    T.vf = false ∧ T.depth = 0 ∧ T.err = false ∧ T.halted = false ∧ T.tail = none

theorem CtlV.setR {T : State (BitVec 64)} (h : CtlV T) (n : Nat) (x : BitVec 64) : CtlV (setR T n x) := by
  obtain ⟨g, k, z, c, nf, v, d, e, hh, t⟩ := h
  by_cases hn : n = 0
  · subst hn; exact ⟨g, k, z, c, nf, v, d, e, hh, t⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [setR_g _ _ hn, g, replicate_set]
    all_goals simp only [setR_k, setR_zf, setR_cf, setR_nf, setR_vf, setR_depth, setR_err, setR_halted, setR_tail, *]

theorem CtlV.next {T : State (BitVec 64)} (h : CtlV T) : CtlV (Riscv.next T) := h
theorem CtlV.withMem {T : State (BitVec 64)} (h : CtlV T) (m : Region → Int → BitVec 64) : CtlV { T with mem := m } := h
theorem CtlV.withPc {T : State (BitVec 64)} (h : CtlV T) (p : Nat) : CtlV { T with pc := p } := h
theorem CtlV.withVl {T : State (BitVec 64)} (h : CtlV T) (l : Nat) : CtlV { T with vl := l } := h
theorem CtlV.ok {T : State (BitVec 64)} (h : CtlV T) : SliceCert.Ok T := ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩
theorem CtlV.halted {T : State (BitVec 64)} (h : CtlV T) : T.halted = false := h.2.2.2.2.2.2.2.2.1

/-- `T`: control part, `pc = p`, `vl = L`, general registers `R`, memory `M`. -/
structure StV (T : State (BitVec 64)) (p L : Nat) (R : Nat → BitVec 64) (M : Region → Int → BitVec 64) : Prop where
  ctl : CtlV T
  pc : T.pc = p
  vl : T.vl = L
  regs : ∀ r, r < 32 → T.getGD r = R r
  mem : T.mem = M

section steps
variable {V : Nat} {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {S : State (BitVec 64)} {n p L : Nat}
  {R : Nat → BitVec 64} {M : Region → Int → BitVec 64}

theorem StV.next_setR {T : State (BitVec 64)} (h : StV T p L R M) (d : Nat) (hd : d < 32) (hd0 : d ≠ 0) (v : BitVec 64) :
    StV (Riscv.next (setR T d v)) (p + 1) L (upd R d v) M := by
  refine ⟨(h.ctl.setR _ _).next, by rw [Riscv.next_pc, setR_pc, h.pc], by rw [Riscv.next_vl, setR_vl, h.vl],
    fun r hr => ?_, by rw [Riscv.next_mem, setR_mem', h.mem]⟩
  rw [Riscv.next_getGD, getGD_setR _ _ _ hd]
  unfold upd
  by_cases e : r = d
  · subst e; simp [hd0]
  · simp only [e, false_and, ↓reduceIte]; exact h.regs r hr

theorem StV.step {T : State (BitVec 64)} (i : Riscv.Instr) (h : StV T p L R M) (hi : prog.getD p .nop = i) :
    (Riscv.isa V).run rodata prog 1 T = Riscv.exec V rodata i T := by
  rw [run_one V rodata prog T h.ctl.halted, h.pc, hi]

theorem StV.of {T : State (BitVec 64)} (h : CtlV T) : StV T T.pc T.vl (fun r => T.getGD r) T.mem :=
  ⟨h, rfl, rfl, fun _ _ => rfl, rfl⟩

/-- `mv d, s`. -/
theorem StV.mv (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (d s : Nat)
    (hi : prog.getD p .nop = .mv d s) (hd : d < 32) (hd0 : d ≠ 0) (hs : s < 32) (hs0 : s ≠ 0) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (p + 1) L (upd R d (R s)) M := by
  rw [Isa.run_add, StV.step _ h hi, exec_mv_eq V rodata _ d s h.ctl.halted, getR_pos _ s hs0, h.regs s hs]
  exact h.next_setR d hd hd0 _

/-- `li d, imm`. -/
theorem StV.li (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (d : Nat) (imm : BitVec 64)
    (hi : prog.getD p .nop = .li d imm) (hd : d < 32) (hd0 : d ≠ 0) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (p + 1) L (upd R d imm) M := by
  rw [Isa.run_add, StV.step _ h hi, exec_li_eq V rodata _ d imm h.ctl.halted]
  exact h.next_setR d hd hd0 _

/-- `slli d, s, k` on a small number. -/
theorem StV.slli (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (d s k x : Nat)
    (hi : prog.getD p .nop = .opi d s .slli (BitVec.ofNat 64 k)) (hd : d < 32) (hd0 : d ≠ 0) (hs : s < 32) (hs0 : s ≠ 0)
    (hR : R s = BitVec.ofNat 64 x) (hk : k < 64) (hx : x * 2 ^ k < 2 ^ 64) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (p + 1) L (upd R d (BitVec.ofNat 64 (x * 2 ^ k))) M := by
  rw [Isa.run_add, StV.step _ h hi, exec_opi_eq V rodata _ d s .slli _ h.ctl.halted, getR_pos _ s hs0, h.regs s hs, hR]
  have e : (Riscv.opi .slli (BitVec.ofNat 64 x) (BitVec.ofNat 64 k) : BitVec 64) = BitVec.ofNat 64 (x * 2 ^ k) := by
    show BitVec.ofNat 64 x <<< (BitVec.ofNat 64 k).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show x < 2 ^ 64 by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      calc x ≤ x * 2 ^ k := Nat.le_mul_of_pos_right _ this
        _ < 2 ^ 64 := hx)]
  rw [e]
  exact h.next_setR d hd hd0 _

/-- `add d, a, b`: a pointer plus a small number. -/
theorem StV.addp (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (d a b : Nat) (ptr : Addr) (x : Nat)
    (hi : prog.getD p .nop = .op d a b .add) (hd : d < 32) (hd0 : d ≠ 0) (ha : a < 32) (ha0 : a ≠ 0) (hb : b < 32)
    (hb0 : b ≠ 0) (hRa : R a = gprWord ptr) (hRb : R b = BitVec.ofNat 64 x) (hx : x < 2 ^ 62) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (p + 1) L (upd R d (gprWord ⟨ptr.region, ptr.off + x⟩)) M := by
  rw [Isa.run_add, StV.step _ h hi, exec_op_eq V rodata _ d a b .add h.ctl.halted, getR_pos _ a ha0, getR_pos _ b hb0,
    h.regs a ha, h.regs b hb, hRa, hRb]
  have e : (Riscv.op2 .add (gprWord ptr) (BitVec.ofNat 64 x) : BitVec 64) = gprWord ⟨ptr.region, ptr.off + x⟩ := by
    show gprWord ptr + BitVec.ofNat 64 x = _
    rw [gprWord_add_const]
    have : (BitVec.ofNat 64 x).toInt = x := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [if_pos (by omega)]
    rw [this]
  rw [e]
  exact h.next_setR d hd hd0 _

/-- `sub d, a, b` on numbers. -/
theorem StV.subn (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (d a b : Nat) (r : Int) (x : Nat)
    (hi : prog.getD p .nop = .op d a b .sub) (hd : d < 32) (hd0 : d ≠ 0) (ha : a < 32) (ha0 : a ≠ 0) (hb : b < 32)
    (hb0 : b ≠ 0) (hRa : R a = gprWord ⟨0, r⟩) (hRb : R b = BitVec.ofNat 64 x) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (p + 1) L (upd R d (gprWord ⟨0, r - (x : Int)⟩)) M := by
  rw [Isa.run_add, StV.step _ h hi, exec_op_eq V rodata _ d a b .sub h.ctl.halted, getR_pos _ a ha0, getR_pos _ b hb0,
    h.regs a ha, h.regs b hb, hRa, hRb]
  have e : (Riscv.op2 .sub (gprWord ⟨0, r⟩) (BitVec.ofNat 64 x) : BitVec 64) = gprWord ⟨0, r - (x : Int)⟩ :=
    Riscv.gprWord_sub_nat r x
  rw [e]
  exact h.next_setR d hd hd0 _

/-- A branch on two number registers. -/
theorem StV.br2 (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (c : Riscv.BCond) (a b t : Nat) (x y : Int)
    (hi : prog.getD p .nop = .br c a b t) (ha : a < 32) (ha0 : a ≠ 0) (hb : b < 32) (hb0 : b ≠ 0)
    (hRa : R a = gprWord ⟨0, x⟩) (hRb : R b = gprWord ⟨0, y⟩) (hx : (⟨0, x⟩ : Addr).wf) (hy : (⟨0, y⟩ : Addr).wf) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (if brHolds c x y then t else p + 1) L R M := by
  rw [Isa.run_add, StV.step _ h hi, exec_br_num V rodata _ c a b t x y h.ctl.halted
    ((getR_pos _ a ha0).trans ((h.regs a ha).trans hRa)) ((getR_pos _ b hb0).trans ((h.regs b hb).trans hRb)) hx hy, h.pc]
  exact ⟨h.ctl.withPc _, rfl, h.vl, h.regs, h.mem⟩

/-- A branch on a number register against `zero`. -/
theorem StV.brz (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (c : Riscv.BCond) (a t : Nat) (x : Int)
    (hi : prog.getD p .nop = .br c a 0 t) (ha : a < 32) (ha0 : a ≠ 0) (hR : R a = gprWord ⟨0, x⟩) (hx : (⟨0, x⟩ : Addr).wf) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (if brHolds c x 0 then t else p + 1) L R M := by
  rw [Isa.run_add, StV.step _ h hi, exec_br_num V rodata _ c a 0 t x 0 h.ctl.halted
    ((getR_pos _ a ha0).trans ((h.regs a ha).trans hR)) (getR_zero _) hx ⟨by decide, by decide⟩, h.pc]
  exact ⟨h.ctl.withPc _, rfl, h.vl, h.regs, h.mem⟩

theorem StV.vlset {T : State (BitVec 64)} (h : StV T p L R M) (d : Nat) (hd : d < 32) (x : BitVec 64) (m : Nat) :
    CtlV (Riscv.next { setR T d x with vl := m }) ∧ (Riscv.next { setR T d x with vl := m }).pc = p + 1 ∧
    (∀ r, r < 32 → (Riscv.next { setR T d x with vl := m }).getGD r = if r = d ∧ d ≠ 0 then x else R r) ∧
    (Riscv.next { setR T d x with vl := m }).mem = M := by
  have e1 : ∀ n, (Riscv.next { setR T d x with vl := m }).getGD n = (setR T d x).getGD n := fun _ => rfl
  have e2 : (Riscv.next { setR T d x with vl := m }).pc = (setR T d x).pc + 1 := rfl
  have e3 : (Riscv.next { setR T d x with vl := m }).mem = (setR T d x).mem := rfl
  refine ⟨((h.ctl.setR d x).withVl m).next, by rw [e2, setR_pc, h.pc], fun r hr => ?_, by rw [e3, setR_mem', h.mem]⟩
  rw [e1, getGD_setR _ _ _ hd]
  by_cases e : r = d ∧ d ≠ 0
  · rw [if_pos e, if_pos e]
  · rw [if_neg e, if_neg e]; exact h.regs r hr

/-- `vsetvli d, a` (e64) with `a` holding `r ≥ 0`: `vl = min r V`. -/
theorem StV.vsetvli (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (d a : Nat) (r : Int)
    (hi : prog.getD p .nop = .vsetvli d a) (hd : d < 32) (ha : a < 32) (ha0 : a ≠ 0) (hR : R a = gprWord ⟨0, r⟩)
    (h0 : 0 ≤ r) (h1 : r < 2 ^ 55) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (p + 1) (min r.toNat V)
      (if d = 0 then R else upd R d (BitVec.ofNat 64 (min r.toNat V))) M := by
  rw [Isa.run_add, StV.step _ h hi, exec_vsetvli_num V rodata _ d a r h.ctl.halted ((getR_pos _ a ha0).trans
    ((h.regs a ha).trans hR)) h0 h1]
  have hx := fun (x : BitVec 64) => StV.vlset (h := h) (d := d) (hd := hd) (x := x) (m := min r.toNat V)
  by_cases hd0 : d = 0
  · subst hd0
    rw [if_pos rfl]
    have := hx (BitVec.ofNat 64 (min r.toNat V))
    simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte] at this
    exact ⟨this.1, this.2.1, rfl, fun r' hr => (this.2.2.1 r' hr).trans (by simp [upd]), this.2.2.2⟩
  · rw [if_neg hd0]
    have := hx (BitVec.ofNat 64 (min r.toNat V))
    exact ⟨this.1, this.2.1, rfl, fun r' hr => (this.2.2.1 r' hr).trans (by unfold upd; by_cases e : r' = d <;> simp [e, hd0]),
      this.2.2.2⟩

/-- `vsetvli zero, a, e8, m<lmul>` with `a` holding `r ≥ 0`, `r ≤ VLMAX_e8`: `vl = r` bytes. -/
theorem StV.vsetvli8 (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (a lmul : Nat) (r : Nat)
    (hi : prog.getD p .nop = .vsetvlie8 0 a lmul) (ha : a < 32) (ha0 : a ≠ 0) (hR : R a = BitVec.ofNat 64 r)
    (h1 : r < 2 ^ 55) (hle : r ≤ 8 * V * lmul) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (p + 1) r R M := by
  have hRr : getR ((Riscv.isa V).run rodata prog n S) a = gprWord ⟨0, (r : Int)⟩ := by
    rw [getR_pos _ a ha0, h.regs a ha, hR]; show _ = BitVec.ofInt 64 (r : Int); rw [BitVec.ofInt_natCast]
  rw [Isa.run_add, StV.step _ h hi, exec_vsetvlie8_num V rodata _ 0 a lmul r h.ctl.halted hRr (by omega) (by omega)
    (by simpa using hle)]
  have e : (r : Int).toNat = r := by simp
  rw [e]
  have := StV.vlset h 0 (by decide) (BitVec.ofNat 64 r) r
  simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte] at this
  exact ⟨this.1, this.2.1, rfl, this.2.2.1, this.2.2.2⟩

end steps


/-! ## Byte-vector copies -/

/-- `setGroup` writes vector registers only. -/
theorem setGroup_eq_v (V : Nat) (s : State (BitVec 64)) (d : Nat) (ws : List (BitVec 64)) (n : Nat) :
    ∃ v, Riscv.setGroup V s d ws n = { s with v := v } := by
  unfold Riscv.setGroup
  generalize List.range ((n + V - 1) / V) = l
  induction l generalizing s with
  | nil => exact ⟨s.v, rfl⟩
  | cons x l ih =>
    simp only [List.foldl_cons]
    obtain ⟨v, hv⟩ := ih (Riscv.setLanes s (d + x) (min V (n - x * V)) fun l => ws.getD (x * V + l) (LaneOps.const 0))
    exact ⟨v, hv.trans rfl⟩

section copy
variable {V : Nat} {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {S : State (BitVec 64)} {n p L : Nat}
  {R : Nat → BitVec 64} {M : Region → Int → BitVec 64}

set_option maxHeartbeats 4000000 in
/-- **`vle8 d, (b1); vse8 d, (b2)`**: the `L` bytes at `a1` stored at `a2` (any alignment of either). -/
theorem StV.copy8 (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (d b1 b2 : Nat) (a1 a2 : Addr)
    (hi1 : prog.getD p .nop = .vle8 d b1) (hi2 : prog.getD (p + 1) .nop = .vse8 d b2) (hb1 : b1 < 32) (hb2 : b2 < 32)
    (hR1 : R b1 = gprWord a1) (hR2 : R b2 = gprWord a2) (hw1 : a1.wf) (hw2 : a2.wf) (hr1 : a1.region ≠ rRodata)
    (hr2 : a2.region ≠ rRodata) (hV : 0 < V) (hV8 : V ≤ 8) (hL8 : L % 8 = 0) (hL0 : L ≠ 0)
    (hd : d + (L / 8 + V - 1) / V ≤ 32) :
    StV ((Riscv.isa V).run rodata prog (n + 1 + 1) S) (p + 1 + 1) L R
      (vstoreMem M a2 ((List.range (L / 8)).map fun (j : Nat) => wordAt (M a1.region) (a1.off + 8 * (j : Int))) (L / 8)) := by
  have hT := h
  generalize hT0 : (Riscv.isa V).run rodata prog n S = T at hT
  have e1 : (Riscv.isa V).run rodata prog (n + 1) S = Riscv.next (Riscv.setGroup V T d
      ((List.range (L / 8)).map fun (j : Nat) => wordAt (M a1.region) (a1.off + 8 * (j : Int))) (L / 8)) := by
    rw [Isa.run_add, hT0, StV.step _ hT hi1, exec_vle8_conc V rodata T d b1 a1 hT.ctl.halted ((hT.regs b1 hb1).trans hR1)
      hw1 hr1 (by rw [hT.vl]; exact hL8) hV, hT.vl, hT.mem]
  obtain ⟨v, hv⟩ := setGroup_eq_v V T d ((List.range (L / 8)).map fun (j : Nat) => wordAt (M a1.region) (a1.off + 8 * (j : Int))) (L / 8)
  have hgw : ∀ j, j < L / 8 → Riscv.groupWord V (Riscv.next { T with v := v }) d j =
      wordAt (M a1.region) (a1.off + 8 * (j : Int)) := by
    intro j hj
    have := groupWord_setGroup V hV hV8 T d ((List.range (L / 8)).map fun (j : Nat) => wordAt (M a1.region) (a1.off + 8 * (j : Int)))
      (L / 8) hd j hj
    rw [hv] at this
    rw [show Riscv.groupWord V (Riscv.next { T with v := v }) d j = Riscv.groupWord V { T with v := v } d j from rfl, this,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  rw [hv] at e1
  generalize hT1 : Riscv.next { T with v := v } = T1 at e1 hgw
  have c1 : CtlV T1 := by rw [← hT1]; exact hT.ctl
  have p1 : T1.pc = p + 1 := by rw [← hT1]; show T.pc + 1 = _; rw [hT.pc]
  have v1 : T1.vl = L := by rw [← hT1]; exact hT.vl
  have g1 : ∀ r, T1.getGD r = T.getGD r := by intro r; rw [← hT1]; rfl
  have m1 : T1.mem = M := by rw [← hT1]; exact hT.mem
  have hh1 : T1.halted = false := c1.halted
  have hl : ((List.range (L / 8)).map fun j => Riscv.groupWord V T1 d j) =
      (List.range (L / 8)).map fun (j : Nat) => wordAt (M a1.region) (a1.off + 8 * (j : Int)) := by
    apply List.map_congr_left; intro j hj; exact hgw j (List.mem_range.mp hj)
  rw [Isa.run_add, e1, run_one V rodata prog T1 hh1, p1, hi2,
    exec_vse8_conc V rodata T1 d b2 a2 hh1 ((g1 b2).trans ((hT.regs b2 hb2).trans hR2)) hw2 hr2 (by rw [v1]; exact hL8) hV
      (by rw [v1]; exact hL0)]
  refine ⟨(c1.withMem _).next, by show T1.pc + 1 = _; rw [p1], v1, fun r hr => by
    show T1.getGD r = _; rw [g1]; exact hT.regs r hr, ?_⟩
  show vstoreMem T1.mem a2 _ (T1.vl / 8) = _
  rw [v1, m1, hl]

/-- `vsseg<nf>e64 s, (b)` into an aligned buffer. -/
theorem StV.vsseg (h : StV ((Riscv.isa V).run rodata prog n S) p L R M) (src b nf : Nat) (a : Addr)
    (hi : prog.getD p .nop = .vsseg src b nf) (hb : b < 32) (hR : R b = gprWord a) (hw : a.wf) (hr : a.region ≠ rRodata)
    (h0 : a.off % 8 = 0) :
    StV ((Riscv.isa V).run rodata prog (n + 1) S) (p + 1) L R
      (memStoreFrom M a.region (a.off / 8) ((List.range (nf * L)).map fun q =>
        Riscv.lane ((Riscv.isa V).run rodata prog n S) (src + q % nf) (q / nf))) := by
  rw [Isa.run_add, StV.step _ h hi, exec_vsseg_conc V rodata _ src b nf a h.ctl.halted ((h.regs b hb).trans hR) hw hr h0]
  refine ⟨(h.ctl.withMem _).next, by show _ + 1 = _; rw [h.pc], h.vl, fun r hr => h.regs r hr, ?_⟩
  show memStoreFrom _ _ _ _ = _
  rw [h.mem, h.vl]

end copy

/-! ## The bounce batch -/

/-- The stack pointer inside the frame (`sp - 512`) and its first word (the bounce buffer). -/
def SPv : Int := 1048064
def BUFq : Int := 131008

theorem spv_wf : (⟨rStack, SPv⟩ : Addr).wf := by decide

theorem ofNat_gprWord (x : Nat) (h : x < 2 ^ 55) : BitVec.ofNat 64 x = gprWord ⟨0, (x : Int)⟩ := by
  show _ = BitVec.ofInt 64 (x : Int); rw [BitVec.ofInt_natCast]

theorem wordGpr_small (x : Nat) (h : x < 2 ^ 56) : (wordGpr (BitVec.ofNat 64 x)).region = 0 := by
  unfold wordGpr
  have : (BitVec.ofNat 64 x >>> 56).toNat = 0 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  simp only [this, ↓reduceIte]

/-- The instructions of the RVV kernels' frame and bounce path; `t` is the `bnez a7` after the rounds
(rvv 368, rvv_zvkb 225). -/
structure MProg (prog : Array Riscv.Instr) (t : Nat) : Prop where
  p7 : prog.getD 7 .nop = .mv 28 12
  p8 : prog.getD 8 .nop = .br .eq 17 0 12
  p9 : prog.getD 9 .nop = .li 29 0x8#64
  p10 : prog.getD 10 .nop = .br .geu 29 28 12
  p11 : prog.getD 11 .nop = .mv 28 29
  p12 : prog.getD 12 .nop = .vsetvli 5 28
  p13 : prog.getD 13 .nop = .br .ne 17 0 16
  p16 : prog.getD 16 .nop = .opi 28 5 .slli 0x6#64
  p17 : prog.getD 17 .nop = .vsetvlie8 0 28 8
  p18 : prog.getD 18 .nop = .vle8 24 11
  p19 : prog.getD 19 .nop = .vse8 24 2
  p20 : prog.getD 20 .nop = .vsetvli 0 5
  q0 : prog.getD t .nop = .br .ne 17 0 (t + 3)
  q3 : prog.getD (t + 3) .nop = .vsseg 0 2 4
  q4 : prog.getD (t + 4) .nop = .opi 28 5 .slli 0x5#64
  q5 : prog.getD (t + 5) .nop = .vsetvlie8 0 28 4
  q6 : prog.getD (t + 6) .nop = .vle8 24 2
  q7 : prog.getD (t + 7) .nop = .vse8 24 10
  q8 : prog.getD (t + 8) .nop = .opi 28 5 .slli 0x6#64
  q9 : prog.getD (t + 9) .nop = .op 11 11 28 .add
  q10 : prog.getD (t + 10) .nop = .opi 28 5 .slli 0x5#64
  q11 : prog.getD (t + 11) .nop = .op 10 10 28 .add
  q12 : prog.getD (t + 12) .nop = .op 12 12 5 .sub
  q13 : prog.getD (t + 13) .nop = .br .ne 12 0 7

/-- A misaligned batch body with `vl = w` (`GenM<w>`, proved symbolically, at relocation `rho 0`): from
the `vlseg8e64 v0, (sp)` (`pc = 21`) to the `bnez a7` after the rounds (`pc = t`), `len` steps. -/
structure MBody (V : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (t w len : Nat) where
  ctl0 : List Nat
  sc0 : State (BitVec 64)
  ctlK : List Nat
  scK : State (BitVec 64)
  segAt : State (BitVec 64) → State (BitVec 64)
  hctl0 : ctl0 = [258, 261, 286]
  c258 : cutVar ctl0 sc0 258 = .ptr ⟨rStack, SPv⟩
  c261 : cutVar ctl0 sc0 261 = .const (BitVec.ofNat 64 w)
  c286 : cutVar ctl0 sc0 286 = .const 0x8000000000000000#64
  hsc0 : sc0.g = Vector.replicate 32 ⟨0, 0⟩ ∧ sc0.k = Vector.replicate 8 0 ∧ sc0.zf = false ∧ sc0.cf = false ∧
    sc0.nf = false ∧ sc0.vf = false ∧ sc0.vl = w ∧ sc0.pc = 21 ∧ sc0.depth = 0
  k258 : 258 ∈ ctlK
  k261 : 261 ∈ ctlK
  k286 : 286 ∈ ctlK
  d258 : cutVar ctlK scK 258 = .ptr ⟨rStack, SPv⟩
  d261 : cutVar ctlK scK 261 = .const (BitVec.ofNat 64 w)
  d286 : cutVar ctlK scK 286 = .const 0x8000000000000000#64
  hscK : scK.g = Vector.replicate 32 ⟨0, 0⟩ ∧ scK.k = Vector.replicate 8 0 ∧ scK.zf = false ∧ scK.cf = false ∧
    scK.nf = false ∧ scK.vf = false ∧ scK.vl = w ∧ scK.pc = t ∧ scK.depth = 0
  run : ∀ S0 : State (BitVec 64), relocState (rho 0) (cutOf ctl0 sc0) = cutOf ctl0 S0 → SliceCert.Ok S0 →
    (Riscv.isa V).run rodata prog len S0 = segAt S0 ∧ SliceCert.Ok (segAt S0) ∧
    relocState (rho 0) (cutOf ctlK scK) = cutOf ctlK (segAt S0)
  frame : ∀ S0 : State (BitVec 64), relocState (rho 0) (cutOf ctl0 sc0) = cutOf ctl0 S0 → SliceCert.Ok S0 →
    ∀ r q, (segAt S0).mem r q = S0.mem r q
  moves : ∀ S0 : State (BitVec 64), relocState (rho 0) (cutOf ctl0 sc0) = cutOf ctl0 S0 → SliceCert.Ok S0 →
    ∀ i ∈ ([266, 267, 268, 273] : List Nat), envOf (segAt S0) i = envOf S0 i
  data : ∀ S0 : State (BitVec 64), relocState (rho 0) (cutOf ctl0 sc0) = cutOf ctl0 S0 → SliceCert.Ok S0 →
    ∀ msg : Nat → Nat → BitVec 64, (∀ l f, l < w → f < 8 → S0.mem rStack (BUFq + (8 * l + f : Nat)) = msg l f) →
    ∀ l f, l < w → f < 4 → Riscv.lane (segAt S0) f l = L (Spec.keccakF (absorbNode (msg l))) f

/-- The loop head (`p = 7`) or the exit (`p = t + 14`) after `j` of the `c` nodes, misaligned path
(`a7 = mi ||| mo ≠ 0`). -/
structure MidU (mi mo off c : Nat) (input : Int → BitVec 64) (S0 S : State (BitVec 64)) (j p : Nat) : Prop where
  ctl : CtlV S
  pc : S.pc = p
  sp : S.getGD 2 = gprWord ⟨rStack, SPv⟩
  a0 : S.getGD 10 = gprWord ⟨rOutput, mo + 32 * (off + j)⟩
  a1 : S.getGD 11 = gprWord ⟨rInput, mi + 64 * (off + j)⟩
  a2 : S.getGD 12 = gprWord ⟨0, (c : Int) - j⟩
  a7 : S.getGD 17 = gprWord ⟨0, ((mi ||| mo : Nat) : Int)⟩
  t5 : S.getGD 30 = 0x8000000000000000#64
  msg : ∀ q, S.mem rInput q = input q
  pre : ∀ b : Int, b < mo + 32 * off → byteAt (S.mem rOutput) b = byteAt (S0.mem rOutput) b
  dig : ∀ n, n < j → DigestB mi mo input S (off + n)

/-- The steps of a bounce batch with `r` nodes left (body length `len`). -/
def bSteps (r len : Nat) : Nat := (if r ≤ 8 then 6 else 7) + 5 + len + 12

theorem or_lt8 (mi mo : Nat) (hmi : mi < 8) (hmo : mo < 8) : (mi ||| mo) < 8 := by
  have := Nat.or_lt_two_pow (n := 3) (show mi < 2 ^ 3 by omega) (show mo < 2 ^ 3 by omega)
  simpa using this

theorem num_wf (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 55) : (⟨0, x⟩ : Addr).wf := ⟨h0, h1⟩

theorem setR0 (S : State (BitVec 64)) (x : BitVec 64) : setR S 0 x = S := by simp [setR]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The head of a bounce batch: `mv t3, a2; beqz a7; li t4, 8; bleu t3, t4; [mv t3, t4]` to the `vsetvli`. -/
theorem headM {V : Nat} {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {t : Nat} (hp : MProg prog t)
    (mi mo off c : Nat) (input : Int → BitVec 64) (S0 S : State (BitVec 64)) (j : Nat) (hmi : mi < 8) (hmo : mo < 8)
    (ha7 : 0 < mi ||| mo) (hM : MidU mi mo off c input S0 S j 7) (hj : j < c) (hc : c < 2 ^ 54) :
    ∃ R : Nat → BitVec 64, StV ((Riscv.isa V).run rodata prog (if c - j ≤ 8 then 4 else 5) S) 12 S.vl R S.mem ∧
      R 28 = gprWord ⟨0, min ((c : Int) - j) 8⟩ ∧ ∀ x, x ≠ 28 → x ≠ 29 → R x = S.getGD x := by
  have h7 := or_lt8 mi mo hmi hmo
  have s0 : StV ((Riscv.isa V).run rodata prog 0 S) 7 S.vl (fun r => S.getGD r) S.mem :=
    ⟨hM.ctl, hM.pc, rfl, fun _ _ => rfl, rfl⟩
  have s1 := StV.mv s0 28 12 hp.p7 (by decide) (by decide) (by decide) (by decide)
  have ha7wf : (⟨0, ((mi ||| mo : Nat) : Int)⟩ : Addr).wf := num_wf _ (by omega) (by omega)
  have s2 := StV.brz s1 .eq 17 12 _ hp.p8 (by decide) (by decide) (by simp [upd]; exact hM.a7) ha7wf
  have hbr1 : brHolds .eq ((mi ||| mo : Nat) : Int) 0 = false := by simp only [brHolds, beq_eq_false_iff_ne, ne_eq]; omega
  rw [hbr1, if_neg (by decide)] at s2
  have s3 := StV.li s2 29 0x8#64 hp.p9 (by decide) (by decide)
  have hr0 : (⟨0, (c : Int) - j⟩ : Addr).wf := num_wf _ (by omega) (by omega)
  have s4 := StV.br2 s3 .geu 29 28 12 8 ((c : Int) - j) hp.p10 (by decide) (by decide) (by decide) (by decide)
    (by simp [upd]; decide) (by simp [upd]; exact hM.a2) ⟨by decide, by decide⟩ hr0
  by_cases hr8 : c - j ≤ 8
  · have hb : brHolds .geu 8 ((c : Int) - j) = true := by simp only [brHolds, decide_eq_true_eq]; omega
    rw [hb, if_pos rfl] at s4
    refine ⟨_, by rw [if_pos hr8]; exact s4, ?_, fun x h28 h29 => ?_⟩
    · simp [upd]; rw [hM.a2]; congr 2; omega
    · simp [upd, h28, h29]
  · have hb : brHolds .geu 8 ((c : Int) - j) = false := by simp only [brHolds, decide_eq_false_iff_not]; omega
    rw [hb, if_neg (by decide)] at s4
    have s5 := StV.mv s4 28 29 hp.p11 (by decide) (by decide) (by decide) (by decide)
    refine ⟨_, by rw [if_neg hr8]; exact s5, ?_, fun x h28 h29 => ?_⟩
    · simp [upd]
      rw [show min ((c : Int) - j) 8 = 8 by omega]; decide
    · simp [upd, h28, h29]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- From the `vsetvli` to the batch body: `vsetvli t0, t3; bnez a7; slli t3, t0, 6; vsetvli zero, t3, e8, m8;
vle8 v24, (a1); vse8 v24, (sp); vsetvli zero, t0` — the `w` nodes' bytes in the bounce buffer. -/
theorem preM {V : Nat} {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {t : Nat} (hp : MProg prog t)
    (hV : 0 < V) (hV8 : V ≤ 8) (S : State (BitVec 64)) (k0 L0 : Nat) (R : Nat → BitVec 64) (M : Region → Int → BitVec 64)
    (h : StV ((Riscv.isa V).run rodata prog k0 S) 12 L0 R M) (rm : Int) (h28 : R 28 = gprWord ⟨0, rm⟩) (hrm : 1 ≤ rm)
    (hrm8 : rm ≤ 8) (a7 : Nat) (h17 : R 17 = gprWord ⟨0, (a7 : Int)⟩) (ha7 : 0 < a7) (ha78 : a7 < 8)
    (a : Int) (h11 : R 11 = gprWord ⟨rInput, a⟩) (ha0 : 0 ≤ a) (ha1 : a + 512 < 2 ^ 55)
    (h2 : R 2 = gprWord ⟨rStack, SPv⟩) (w : Nat) (hw : w = min rm.toNat V) :
    ∃ R' : Nat → BitVec 64, StV ((Riscv.isa V).run rodata prog (k0 + 7) S) 21 w R'
      (memStoreFrom M rStack BUFq ((List.range (8 * w)).map fun (i : Nat) => wordAt (M rInput) (a + 8 * (i : Int)))) ∧
      R' 5 = BitVec.ofNat 64 w ∧ ∀ x, x ≠ 5 → x ≠ 28 → R' x = R x := by
  have hw1 : 1 ≤ w := by omega
  have hwV : w ≤ V := by omega
  have s6 := StV.vsetvli h 5 28 rm hp.p12 (by decide) (by decide) (by decide) h28 (by omega) (by omega)
  rw [if_neg (by decide), ← hw] at s6
  have s7 := StV.brz s6 .ne 17 16 (a7 : Int) hp.p13 (by decide) (by decide) (by simp [upd]; exact h17)
    (num_wf _ (by omega) (by omega))
  have hbr : brHolds .ne (a7 : Int) 0 = true := by simp only [brHolds, bne_iff_ne, ne_eq]; omega
  rw [hbr, if_pos rfl] at s7
  have s8 := StV.slli s7 28 5 6 w hp.p16 (by decide) (by decide) (by decide) (by decide) (by simp [upd]) (by decide)
    (by omega)
  have s9 := StV.vsetvli8 s8 28 8 (w * 2 ^ 6) hp.p17 (by decide) (by decide) (by simp [upd]) (by omega)
    (by rw [Nat.mul_comm 8 V]; omega)
  have s10 := StV.copy8 s9 24 11 2 ⟨rInput, a⟩ ⟨rStack, SPv⟩ hp.p18 hp.p19 (by decide) (by decide)
    (by simp [upd]; exact h11) (by simp [upd]; exact h2) (show (0 : Int) ≤ a ∧ a < 2 ^ 55 from ⟨ha0, by omega⟩) spv_wf
    (by show rInput ≠ rRodata; decide) (by decide) hV hV8 (by omega) (by omega) (by
      have : (w * 2 ^ 6 / 8 + V - 1) / V < 9 := by
        apply (Nat.div_lt_iff_lt_mul hV).mpr; rw [show w * 2 ^ 6 / 8 = 8 * w by omega]; omega
      omega)
  have s11 := StV.vsetvli s10 0 5 w hp.p20 (by decide) (by decide) (by decide) (by simp [upd]; exact ofNat_gprWord w (by omega))
    (by omega) (by omega)
  rw [if_pos rfl, show min ((w : Int)).toNat V = w by omega] at s11
  have hn : w * 2 ^ 6 / 8 = 8 * w := by omega
  rw [hn] at s11
  refine ⟨upd (upd R 5 (BitVec.ofNat 64 w)) 28 (BitVec.ofNat 64 (w * 2 ^ 6)), ?_, by simp [upd],
    fun x h5 h28' => by simp [upd, h5, h28']⟩
  have e : vstoreMem M ⟨rStack, SPv⟩ ((List.range (8 * w)).map fun (j : Nat) => wordAt (M rInput) (a + 8 * (j : Int))) (8 * w) =
      memStoreFrom M rStack BUFq ((List.range (8 * w)).map fun (i : Nat) => wordAt (M rInput) (a + 8 * (i : Int))) := by
    unfold vstoreMem
    rw [if_pos (by decide)]
    rfl
  rw [← e]
  exact s11

/-- The digest words of the batch in the bounce buffer (`vsseg4e64 v0, (sp)`). -/
def bufOut (M : Region → Int → BitVec 64) (C : State (BitVec 64)) (w : Nat) : Region → Int → BitVec 64 :=
  memStoreFrom M rStack BUFq ((List.range (4 * w)).map fun q => Riscv.lane C (0 + q % 4) (q / 4))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- After the batch body: `bnez a7; vsseg4e64 v0, (sp); slli t3, t0, 5; vsetvli zero, t3, e8, m4;
vle8 v24, (sp); vse8 v24, (a0); slli; add a1; slli; add a0; sub a2, a2, t0; bnez a2`. -/
theorem tailM {V : Nat} {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {t : Nat} (hp : MProg prog t)
    (hV : 0 < V) (hV8 : V ≤ 8) (C : State (BitVec 64)) (w : Nat) (hc : CtlV C) (hpc : C.pc = t) (hvl : C.vl = w)
    (hw1 : 1 ≤ w) (hwV : w ≤ V) (h2 : C.getGD 2 = gprWord ⟨rStack, SPv⟩) (h5 : C.getGD 5 = BitVec.ofNat 64 w)
    (b : Int) (h10 : C.getGD 10 = gprWord ⟨rOutput, b⟩) (hb0 : 0 ≤ b) (hb1 : b + 512 < 2 ^ 55)
    (a : Int) (h11 : C.getGD 11 = gprWord ⟨rInput, a⟩)
    (r : Int) (h12 : C.getGD 12 = gprWord ⟨0, r⟩) (hr : (w : Int) ≤ r) (hr1 : r < 2 ^ 55)
    (a7 : Nat) (h17 : C.getGD 17 = gprWord ⟨0, (a7 : Int)⟩) (ha7 : 0 < a7) (ha78 : a7 < 8) :
    ∃ R' : Nat → BitVec 64, StV ((Riscv.isa V).run rodata prog 12 C) (if r - w = 0 then t + 14 else 7) (w * 2 ^ 5) R'
      (vstoreMem (bufOut C.mem C w) ⟨rOutput, b⟩ ((List.range (4 * w)).map fun (j : Nat) =>
        wordAt (bufOut C.mem C w rStack) (SPv + 8 * (j : Int))) (4 * w)) ∧
      R' 2 = gprWord ⟨rStack, SPv⟩ ∧ R' 10 = gprWord ⟨rOutput, b + (w * 2 ^ 5 : Nat)⟩ ∧
      R' 11 = gprWord ⟨rInput, a + (w * 2 ^ 6 : Nat)⟩ ∧ R' 12 = gprWord ⟨0, r - w⟩ ∧ R' 17 = C.getGD 17 ∧
      R' 30 = C.getGD 30 := by
  have s0 : StV ((Riscv.isa V).run rodata prog 0 C) t w (fun r => C.getGD r) C.mem := ⟨hc, hpc, hvl, fun _ _ => rfl, rfl⟩
  have s1 := StV.brz s0 .ne 17 (t + 3) (a7 : Int) hp.q0 (by decide) (by decide) h17 (num_wf _ (by omega) (by omega))
  have hbr : brHolds .ne (a7 : Int) 0 = true := by simp only [brHolds, bne_iff_ne, ne_eq]; omega
  rw [hbr, if_pos rfl] at s1
  -- the vector registers are those of `C` after the branch
  have hv1 : ((Riscv.isa V).run rodata prog (0 + 1) C).v = C.v := by
    show ((Riscv.isa V).run rodata prog 1 ((Riscv.isa V).run rodata prog 0 C)).v = C.v
    rw [StV.step _ s0 hp.q0, show (Riscv.isa V).run rodata prog 0 C = C from rfl, exec_br_num V rodata C .ne 17 0 (t + 3) (a7 : Int) 0 hc.halted
      ((getR_pos _ 17 (by decide)).trans h17) (getR_zero _) (num_wf _ (by omega) (by omega)) ⟨by decide, by decide⟩]
  have s2 := StV.vsseg s1 0 2 4 ⟨rStack, SPv⟩ hp.q3 (by decide) h2 spv_wf (by decide) (by decide)
  have hlane : ∀ f l, Riscv.lane ((Riscv.isa V).run rodata prog (0 + 1) C) f l = Riscv.lane C f l := by
    intro f l; unfold Riscv.lane State.getV; rw [hv1]
  have hM2 : memStoreFrom C.mem (⟨rStack, SPv⟩ : Addr).region ((⟨rStack, SPv⟩ : Addr).off / 8)
      ((List.range (4 * w)).map fun q => Riscv.lane ((Riscv.isa V).run rodata prog (0 + 1) C) (0 + q % 4) (q / 4)) =
      bufOut C.mem C w := by
    unfold bufOut
    show memStoreFrom C.mem rStack (SPv / 8) _ = memStoreFrom C.mem rStack BUFq _
    rw [show SPv / 8 = BUFq by decide]
    congr 1
    apply List.map_congr_left; intro q _; exact hlane _ _
  rw [hM2] at s2
  have s3 := StV.slli s2 28 5 5 w hp.q4 (by decide) (by decide) (by decide) (by decide) h5 (by decide)
    (by omega)
  have s4 := StV.vsetvli8 s3 28 4 (w * 2 ^ 5) hp.q5 (by decide) (by decide) (by simp [upd]) (by omega)
    (by rw [Nat.mul_comm 8 V]; omega)
  have s5 := StV.copy8 s4 24 2 10 ⟨rStack, SPv⟩ ⟨rOutput, b⟩ hp.q6 hp.q7 (by decide) (by decide)
    (by simp [upd]; exact h2) (by simp [upd]; exact h10) spv_wf (show (0 : Int) ≤ b ∧ b < 2 ^ 55 from ⟨hb0, by omega⟩)
    (by decide) (by show rOutput ≠ rRodata; decide) hV hV8 (by omega) (by omega) (by
      have : (w * 2 ^ 5 / 8 + V - 1) / V < 9 := by
        apply (Nat.div_lt_iff_lt_mul hV).mpr; rw [show w * 2 ^ 5 / 8 = 4 * w by omega]; omega
      omega)
  rw [show w * 2 ^ 5 / 8 = 4 * w by omega] at s5
  have s6 := StV.slli s5 28 5 6 w hp.q8 (by decide) (by decide) (by decide) (by decide) (by simp [upd]; exact h5) (by decide)
    (by omega)
  have s7 := StV.addp s6 11 11 28 ⟨rInput, a⟩ (w * 2 ^ 6) hp.q9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp [upd]; exact h11) (by simp [upd]) (by omega)
  have s8 := StV.slli s7 28 5 5 w hp.q10 (by decide) (by decide) (by decide) (by decide) (by simp [upd]; exact h5) (by decide)
    (by omega)
  have s9 := StV.addp s8 10 10 28 ⟨rOutput, b⟩ (w * 2 ^ 5) hp.q11 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp [upd]; exact h10) (by simp [upd]) (by omega)
  have s10 := StV.subn s9 12 12 5 r w hp.q12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [upd]; exact h12) (by simp [upd]; exact h5)
  have s11 := StV.brz s10 .ne 12 7 (r - w) hp.q13 (by decide) (by decide) (by simp [upd]) (num_wf _ (by omega) (by omega))
  have hpc11 : (if brHolds .ne (r - (w : Int)) 0 then 7 else t + 3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) =
      if r - w = 0 then t + 14 else 7 := by
    by_cases hz : r - (w : Int) = 0
    · rw [if_pos hz, if_neg (by simp only [brHolds, bne_iff_ne, ne_eq]; omega)]
    · rw [if_neg hz, if_pos (by simp only [brHolds, bne_iff_ne, ne_eq]; omega)]
  rw [hpc11] at s11
  refine ⟨_, s11, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (simp [upd]; try exact h2)

theorem vstoreMem_other (M : Region → Int → BitVec 64) (a : Addr) (vs : List (BitVec 64)) (n : Nat) (r : Region) (q : Int)
    (h : r ≠ a.region) : vstoreMem M a vs n r q = M r q := by
  unfold vstoreMem
  split <;> rw [memStoreFrom_get, if_neg (fun h' => h h'.1)]

theorem memStoreFrom_other (M : Region → Int → BitVec 64) (r0 : Region) (q0 : Int) (L : List (BitVec 64)) (r : Region)
    (h : r ≠ r0) : memStoreFrom M r0 q0 L r = M r := by
  funext q; rw [memStoreFrom_get, if_neg (fun h' => h h'.1)]

theorem cut_gd (ρ : Reloc) (hρ : ρ.ok) (ctl : List Nat) (sc C : State (BitVec 64)) (h : relocState ρ (cutOf ctl sc) = cutOf ctl C)
    (n : Nat) (hn : n < 32) (hm : 256 + n ∈ ctl) (e : E) (hv : cutVar ctl sc (256 + n) = e) (hre : E.reloc ρ e = e) :
    cutVar ctl C (256 + n) = e := by
  have e1 := cut_word ρ hρ ctl sc C h (256 + n) (Or.inl (by omega))
  rw [hv, hre] at e1; exact e1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- **A bounce batch** of `w = min(c - j, V)` nodes: from the loop head after `j` nodes, `bSteps (c - j) len` steps
hash nodes `off + j .. off + j + w - 1` and reach the loop head after `j + w` nodes, or the exit. -/
theorem batchM {V : Nat} {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {t len : Nat} (hp : MProg prog t)
    (hV : 0 < V) (hV8 : V ≤ 8) (w : Nat) (B : MBody V rodata prog t w len)
    (mi mo off c : Nat) (input : Int → BitVec 64) (S0 S : State (BitVec 64)) (j : Nat) (hmi : mi < 8) (hmo : mo < 8)
    (ha7 : 0 < mi ||| mo) (hb : 64 * (off + c) + 512 ≤ 2 ^ 54) (hM : MidU mi mo off c input S0 S j 7) (hj : j < c)
    (hw : w = min (c - j) V) :
    MidU mi mo off c input S0 ((Riscv.isa V).run rodata prog (bSteps (c - j) len) S) (j + w)
      (if c - j - w = 0 then t + 14 else 7) := by
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hb55 : (2 : Int) ^ 55 = 36028797018963968 := rfl
  have h7 := or_lt8 mi mo hmi hmo
  have hw1 : 1 ≤ w := by omega
  have hwV : w ≤ V := by omega
  have hwr : w ≤ c - j := by omega
  -- the head and the copy into the buffer
  obtain ⟨R, s12, h28, hR⟩ := headM (V := V) (rodata := rodata) hp mi mo off c input S0 S j hmi hmo ha7 hM hj (by omega)
  obtain ⟨R', sH, hR'5, hR'⟩ := preM hp hV hV8 S _ S.vl R S.mem s12 (min ((c : Int) - j) 8) h28 (by omega) (by omega)
    (mi ||| mo) ((hR 17 (by decide) (by decide)).trans hM.a7) ha7 h7 ((mi : Int) + 64 * ((off + j : Nat) : Int))
    ((hR 11 (by decide) (by decide)).trans (hM.a1.trans (congrArg (fun o => gprWord ⟨rInput, o⟩) (by push_cast; omega))))
    (by omega) (by push_cast; omega) ((hR 2 (by decide) (by decide)).trans hM.sp) w (by omega)
  generalize hH : (Riscv.isa V).run rodata prog ((if c - j ≤ 8 then 4 else 5) + 7) S = H at sH
  have hHg : ∀ x, x < 32 → x ≠ 5 → x ≠ 28 → x ≠ 29 → H.getGD x = S.getGD x := by
    intro x hx h5 h28 h29; rw [sH.regs x hx, hR' x h5 h28, hR x h28 h29]
  -- the batch body's start cut
  have hρ := rho_ok 0
  have hc0 : relocState (rho 0) (cutOf B.ctl0 B.sc0) = cutOf B.ctl0 H := by
    apply relocState_cutOf (rho 0) B.ctl0 B.sc0 H
    · intro i hi
      rw [B.hctl0] at hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · rw [cutVar_ptr_of B.ctl0 H 258 ⟨rStack, SPv⟩ (by rw [B.hctl0]; decide)
          ((envOf_gdVar H 2 (by decide)).trans ((hHg 2 (by decide) (by decide) (by decide) (by decide)).trans hM.sp)) spv_wf (by decide),
          B.c258, reloc_ptr_stack]
      · rw [Riscv.cutVar_const_of B.ctl0 H 261 (BitVec.ofNat 64 w) (by rw [B.hctl0]; decide)
          ((envOf_gdVar H 5 (by decide)).trans ((sH.regs 5 (by decide)).trans hR'5)) (wordGpr_small w (by omega)), B.c261,
          rho_const]
      · rw [Riscv.cutVar_const_of B.ctl0 H 286 0x8000000000000000#64 (by rw [B.hctl0]; decide)
          ((envOf_gdVar H 30 (by decide)).trans ((hHg 30 (by decide) (by decide) (by decide) (by decide)).trans hM.t5)) (by decide),
          B.c286, rho_const]
    · intro i hi h; rw [B.hctl0] at hi; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
    · obtain ⟨g, k, z, cc, nf, v, d, -⟩ := sH.ctl
      obtain ⟨g', k', z', cc', nf', v', l', p', d'⟩ := B.hsc0
      exact ⟨g.trans g'.symm, k.trans k'.symm, z.trans z'.symm, cc.trans cc'.symm, nf.trans nf'.symm, v.trans v'.symm,
        sH.vl.trans l'.symm, sH.pc.trans p'.symm, d.trans d'.symm⟩
  have hokH : SliceCert.Ok H := sH.ctl.ok
  have sr := B.run H hc0 hokH
  have fr := B.frame H hc0 hokH
  have mv := B.moves H hc0 hokH
  -- the node words in the buffer
  have hbuf : ∀ l f, l < w → f < 8 → H.mem rStack (BUFq + (8 * l + f : Nat)) = nodeWordsB input mi (off + j + l) f := by
    intro l f hl hf
    rw [sH.mem, memStoreFrom_get, if_pos ⟨rfl, by omega, by simp; omega⟩]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    have hm : S.mem rInput = input := funext hM.msg
    rw [hm]
    unfold nodeWordsB
    congr 1
    push_cast; omega
  have dat := B.data H hc0 hokH (fun l f => nodeWordsB input mi (off + j + l) f) hbuf
  generalize hC : B.segAt H = C at sr fr mv dat
  obtain ⟨hrunC, hokC, hcutC⟩ := sr
  -- the state after the body
  have hCf := cut_fields _ _ _ _ hcutC
  have hCtl : CtlV C := by
    obtain ⟨g, k, z, cc, nf, v, l, p, d⟩ := hCf
    obtain ⟨g', k', z', cc', nf', v', l', p', d'⟩ := B.hscK
    exact ⟨g.trans g', k.trans k', z.trans z', cc.trans cc', nf.trans nf', v.trans v', d.trans d', hokC.1, hokC.2.1, hokC.2.2⟩
  have hCpc : C.pc = t := hCf.2.2.2.2.2.2.2.1.trans B.hscK.2.2.2.2.2.2.2.1
  have hCvl : C.vl = w := hCf.2.2.2.2.2.2.1.trans B.hscK.2.2.2.2.2.2.1
  have hC2 : C.getGD 2 = gprWord ⟨rStack, SPv⟩ := by
    have := cut_gd (rho 0) hρ B.ctlK B.scK C hcutC 2 (by decide) B.k258 _ B.d258 (reloc_ptr_stack 0 _)
    rw [← envOf_gdVar C 2 (by decide)]; exact cut_ptr B.ctlK C 258 B.k258 _ this
  have hC5 : C.getGD 5 = BitVec.ofNat 64 w := by
    have := cut_gd (rho 0) hρ B.ctlK B.scK C hcutC 5 (by decide) B.k261 _ B.d261 (rho_const 0 _)
    rw [← envOf_gdVar C 5 (by decide)]; exact cut_const B.ctlK C 261 B.k261 _ this
  have hC30 : C.getGD 30 = 0x8000000000000000#64 := by
    have := cut_gd (rho 0) hρ B.ctlK B.scK C hcutC 30 (by decide) B.k286 _ B.d286 (rho_const 0 _)
    rw [← envOf_gdVar C 30 (by decide)]; exact cut_const B.ctlK C 286 B.k286 _ this
  have hCmv : ∀ x, x = 10 ∨ x = 11 ∨ x = 12 ∨ x = 17 → C.getGD x = S.getGD x := by
    intro x hx
    have hx' : 256 + x ∈ ([266, 267, 268, 273] : List Nat) := by rcases hx with rfl | rfl | rfl | rfl <;> decide
    rw [← envOf_gdVar C x (by omega), mv _ hx', envOf_gdVar H x (by omega), hHg x (by omega) (by omega) (by omega) (by omega)]
  -- the tail
  obtain ⟨R'', sU, hU2, hU10, hU11, hU12, hU17, hU30⟩ := tailM hp hV hV8 C w hCtl hCpc hCvl hw1 hwV hC2 hC5
    ((mo : Int) + 32 * ((off + j : Nat) : Int)) ((hCmv 10 (by decide)).trans (hM.a0.trans (congrArg (fun o => gprWord ⟨rOutput, o⟩)
      (by push_cast; omega)))) (by omega) (by push_cast; omega)
    ((mi : Int) + 64 * ((off + j : Nat) : Int)) ((hCmv 11 (by decide)).trans (hM.a1.trans (congrArg (fun o => gprWord ⟨rInput, o⟩)
      (by push_cast; omega))))
    ((c : Int) - j) ((hCmv 12 (by decide)).trans hM.a2) (by omega) (by omega)
    (mi ||| mo) ((hCmv 17 (by decide)).trans hM.a7) ha7 h7
  have hrun : (Riscv.isa V).run rodata prog (bSteps (c - j) len) S = (Riscv.isa V).run rodata prog 12 C := by
    rw [show bSteps (c - j) len = ((if c - j ≤ 8 then 4 else 5) + 7) + len + 12 by unfold bSteps; split <;> omega,
      Isa.run_add, Isa.run_add, hH, hrunC]
  rw [hrun]
  generalize hU : (Riscv.isa V).run rodata prog 12 C = U at sU
  -- memory: the input region and the output bytes
  have hCmem : C.mem = H.mem := funext fun r => funext fun q => fr r q
  have hUin : ∀ q, U.mem rInput q = input q := by
    intro q
    rw [sU.mem, vstoreMem_other _ _ _ _ _ _ (by show rInput ≠ rOutput; decide), show bufOut C.mem C w rInput = C.mem rInput from
      memStoreFrom_other _ _ _ _ _ (by decide), hCmem, sH.mem, memStoreFrom_other _ _ _ _ _ (by decide), hM.msg]
  have hUout : ∀ x : Int, byteAt (U.mem rOutput) x =
      if (mo : Int) + 32 * ((off + j : Nat) : Int) ≤ x ∧ x < (mo : Int) + 32 * ((off + j : Nat) : Int) + 8 * ((4 * w : Nat) : Int)
      then (L (Spec.keccakF (absorbNode (nodeWordsB input mi (off + j + ((x - ((mo : Int) + 32 * ((off + j : Nat) : Int))) / 32).toNat))))
        (((x - ((mo : Int) + 32 * ((off + j : Nat) : Int))) / 8 % 4).toNat)).extractLsb'
          (8 * ((x - ((mo : Int) + 32 * ((off + j : Nat) : Int))) % 8).toNat) 8
      else byteAt (S.mem rOutput) x := by
    intro x
    rw [sU.mem, byteAt_vstoreMem _ _ _ _ (by simp) (by omega)]
    by_cases hx : (mo : Int) + 32 * ((off + j : Nat) : Int) ≤ x ∧ x < (mo : Int) + 32 * ((off + j : Nat) : Int) + 8 * ((4 * w : Nat) : Int)
    · rw [if_pos ⟨rfl, hx⟩, if_pos hx]
      generalize hk : ((x - ((mo : Int) + 32 * ((off + j : Nat) : Int))) / 8).toNat = k
      have hk4 : k < 4 * w := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk4]
      simp only [Option.map_some, Option.getD_some]
      rw [show SPv + 8 * (k : Int) = 8 * (BUFq + k) by unfold SPv BUFq; omega, wordAt_aligned]
      unfold bufOut
      rw [memStoreFrom_get, if_pos ⟨rfl, by omega, by simp; omega⟩, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [show (BUFq + (k : Int) - BUFq).toNat = k by omega]
      rw [Nat.zero_add, dat (k / 4) (k % 4) (by omega) (Nat.mod_lt _ (by decide))]
      have e1 : ((x - ((mo : Int) + 32 * ((off + j : Nat) : Int))) / 32).toNat = k / 4 := by omega
      have e2 : (((x - ((mo : Int) + 32 * ((off + j : Nat) : Int))) / 8 % 4).toNat) = k % 4 := by omega
      rw [e1, e2]
    · rw [if_neg (fun h => hx h.2), if_neg hx]
      unfold byteAt
      rw [show bufOut C.mem C w rOutput = C.mem rOutput from memStoreFrom_other _ _ _ _ _ (by decide), hCmem, sH.mem,
        memStoreFrom_other _ _ _ _ _ (by decide)]
  refine ⟨sU.ctl, ?_, sU.regs 2 (by decide) |>.trans hU2, ?_, ?_, ?_, ?_, ?_, hUin, fun x hx => ?_, fun n hn => ?_⟩
  · rw [sU.pc]
    by_cases hz : c - j - w = 0
    · rw [if_pos (by omega), if_pos hz]
    · rw [if_neg (by omega), if_neg hz]
  · rw [sU.regs 10 (by decide), hU10]; exact congrArg (fun o => gprWord ⟨rOutput, o⟩) (by push_cast; omega)
  · rw [sU.regs 11 (by decide), hU11]; exact congrArg (fun o => gprWord ⟨rInput, o⟩) (by push_cast; omega)
  · rw [sU.regs 12 (by decide), hU12]; exact congrArg (fun o => gprWord ⟨0, o⟩) (by push_cast; omega)
  · rw [sU.regs 17 (by decide), hU17]; exact (hCmv 17 (by decide)).trans hM.a7
  · rw [sU.regs 30 (by decide), hU30]; exact hC30
  · rw [hUout, if_neg (by push_cast; omega)]; exact hM.pre x hx
  · intro t' ht'
    by_cases hnj : n < j
    · rw [hUout, if_neg (by push_cast; omega)]; exact hM.dig n hnj t' ht'
    · rw [hUout, if_pos (by push_cast; omega)]
      have e0 : off + j + (((mo : Int) + 32 * ((off + n : Nat) : Int) + (t' : Int) - ((mo : Int) + 32 * ((off + j : Nat) : Int))) / 32).toNat
          = off + n := by push_cast; omega
      have e1 : ((((mo : Int) + 32 * ((off + n : Nat) : Int) + (t' : Int) - ((mo : Int) + 32 * ((off + j : Nat) : Int))) / 8 % 4).toNat)
          = t' / 8 := by push_cast; omega
      have e2 : (((mo : Int) + 32 * ((off + n : Nat) : Int) + (t' : Int) - ((mo : Int) + 32 * ((off + j : Nat) : Int))) % 8).toNat
          = t' % 8 := by push_cast; omega
      rw [e0, e1, e2, absorbNode_keccak, squeezeByte_eq]

end Keccaktree.Kernels.RvvCommonU




