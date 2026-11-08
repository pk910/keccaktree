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

end Keccaktree.Kernels.RvvCommonU
