import Keccaktree.Kernels.RiscvBytes
import Keccaktree.Asm.RiscvAliasTrace
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# In place: the access condition along concrete steps of the scalar RISC-V kernels

`StA S n p R M B0 B`: the concrete state after `n` steps from `S` (`RiscvBytes.St`), and the access
condition (`Riscv.AccessRun`) of those `n` steps from bound `B0`, now at `B`.  One lemma per
instruction form of `St` (the same arguments): loads and stores through a stack pointer and the
register/branch forms keep the bound; a store into the output (`sd_out`) raises it past the word.
-/
namespace Keccaktree.Kernels.RiscvAccSt
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Kernels.RiscvBytes
open Keccaktree.Asm.Riscv (wordOf byteOf gx_word)
open Keccaktree.Asm.Arm (gx addr withAddr)

section
variable {vlmax : Nat} {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {S : State (BitVec 64)} {n p : Nat}
  {R : Nat → BitVec 64} {M : Region → Int → BitVec 64}

theorem addr_off (T : State (BitVec 64)) (b : Nat) (off : Int) (a : Addr) (hb : T.getGD b = gprWord a) (hwf : a.wf) :
    addr T b off = some ⟨a.region, a.off + off⟩ := by
  show (Arm.gx T b).map (fun a => (⟨a.region, a.off + off⟩ : Addr)) = some _
  rw [gx_word T b a hb hwf]; rfl

/-- A larger final bound. -/
theorem accessRun_bf (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) :
    ∀ (n : Nat) (B Bf Bf' : Int) (S : State (BitVec 64)), Riscv.AccessRun vlmax rodata prog n B Bf S → Bf ≤ Bf' →
      Riscv.AccessRun vlmax rodata prog n B Bf' S := by
  intro n
  induction n with
  | zero => intro B Bf Bf' S h hf; exact Int.le_trans h hf
  | succ n ih =>
    intro B Bf Bf' S h hf
    simp only [Riscv.AccessRun, AlIsa.AccessRun] at h ⊢
    split
    · rename_i hh; rw [if_pos hh] at h; exact Int.le_trans h hf
    · rename_i hh; rw [if_neg hh] at h; exact ⟨h.1, h.2.1, ih _ _ _ _ h.2.2 hf⟩

/-- `n` concrete steps with their access condition. -/
structure StA (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (S : State (BitVec 64)) (n p : Nat)
    (R : Nat → BitVec 64) (M : Region → Int → BitVec 64) (B0 B : Int) : Prop where
  st : St ((Riscv.isa vlmax).run rodata prog n S) p R M
  acc : Riscv.AccessRun vlmax rodata prog n B0 B S

theorem StA.start (h : St ((Riscv.isa vlmax).run rodata prog 0 S) p R M) (B : Int) :
    StA vlmax rodata prog S 0 p R M B B :=
  ⟨h, Int.le_refl B⟩

/-- One step with neither input nor output cells. -/
theorem StA.quiet {B0 B : Int} {p' : Nat} {R' : Nat → BitVec 64} {M' : Region → Int → BitVec 64}
    (h : StA vlmax rodata prog S n p R M B0 B) (h' : St ((Riscv.isa vlmax).run rodata prog (n + 1) S) p' R' M')
    (hr : ∀ c ∈ Riscv.reads ((Riscv.isa vlmax).run rodata prog n S) (prog.getD p .nop), c.1 ≠ rInput)
    (hw : ∀ c ∈ Riscv.writes ((Riscv.isa vlmax).run rodata prog n S) (prog.getD p .nop), c.1 ≠ rInput ∧ c.1 ≠ rOutput) :
    StA vlmax rodata prog S (n + 1) p' R' M' B0 B := by
  refine ⟨h', ?_⟩
  apply Riscv.accessRun_add vlmax rodata prog n 1 B0 B B S h.acc
  have hh := h.st.ctl.halted
  have he : (Riscv.exec vlmax rodata (prog.getD p .nop) ((Riscv.isa vlmax).run rodata prog n S)).err = false := by
    have := h'.ctl.2.2.2.2.2.2.2.2.1
    rwa [Isa.run_add, St.step _ h.st rfl] at this
  rw [← h.st.pc] at hr hw he
  exact Riscv.accessRun_step vlmax rodata prog 0 B B _ hh he hr hw (Int.le_refl B)

theorem StA.ld {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (d b : Nat) (off : Int) (a : Addr) (q : Int)
    (v : BitVec 64) (hi : prog.getD p .nop = .ld d b off) (hd : d < 32) (hd0 : d ≠ 0) (hb : b < 32) (hR : R b = gprWord a)
    (hwf : a.wf) (hal : (a.off + off) % 8 = 0) (hr : a.region ≠ rRodata) (hq : (a.off + off) / 8 = q)
    (hv : M a.region q = v) (hin : a.region ≠ rInput) :
    StA vlmax rodata prog S (n + 1) (p + 1) (upd R d v) M B0 B := by
  apply h.quiet (h.st.ld d b off a q v hi hd hd0 hb hR hwf hal hr hq hv)
  · intro c hc
    rw [hi] at hc
    simp only [Riscv.reads, addr_off _ b off a ((h.st.regs b hb).trans hR) hwf, storeCells, List.range_one,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hc
    subst hc; exact hin
  · intro c hc; rw [hi] at hc; simp [Riscv.writes] at hc

theorem StA.sd {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (src b : Nat) (off : Int) (a : Addr) (q : Int)
    (v : BitVec 64) (hi : prog.getD p .nop = .sd src b off) (hs : src < 32) (hs0 : src ≠ 0) (hb : b < 32)
    (hR : R b = gprWord a) (hwf : a.wf) (hal : (a.off + off) % 8 = 0) (hr : a.region ≠ rRodata) (hq : (a.off + off) / 8 = q)
    (hv : R src = v) (hin : a.region ≠ rInput) (hout : a.region ≠ rOutput) :
    StA vlmax rodata prog S (n + 1) (p + 1) R (memStore M a.region q v) B0 B := by
  apply h.quiet (h.st.sd src b off a q v hi hs hs0 hb hR hwf hal hr hq hv)
  · intro c hc; rw [hi] at hc; simp [Riscv.reads] at hc
  · intro c hc
    rw [hi] at hc
    simp only [Riscv.writes, addr_off _ b off a ((h.st.regs b hb).trans hR) hwf, storeCells, List.range_one,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hc
    subst hc; exact ⟨hin, hout⟩

/-- A store into the output word `q`: the bound passes it. -/
theorem StA.sd_out {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (src b : Nat) (off : Int) (a : Addr) (q : Int)
    (v : BitVec 64) (hi : prog.getD p .nop = .sd src b off) (hs : src < 32) (hs0 : src ≠ 0) (hb : b < 32)
    (hR : R b = gprWord a) (hwf : a.wf) (hal : (a.off + off) % 8 = 0) (hr : a.region = rOutput) (hq : (a.off + off) / 8 = q)
    (hv : R src = v) :
    StA vlmax rodata prog S (n + 1) (p + 1) R (memStore M a.region q v) B0 (max B (q + 1)) := by
  have h' := h.st.sd src b off a q v hi hs hs0 hb hR hwf hal (by rw [hr]; decide) hq hv
  refine ⟨h', ?_⟩
  apply Riscv.accessRun_add vlmax rodata prog n 1 B0 B _ S h.acc
  have hh := h.st.ctl.halted
  have he : (Riscv.exec vlmax rodata (prog.getD p .nop) ((Riscv.isa vlmax).run rodata prog n S)).err = false := by
    have := h'.ctl.2.2.2.2.2.2.2.2.1
    rwa [Isa.run_add, St.step _ h.st rfl] at this
  have hA := addr_off _ b off a ((h.st.regs b hb).trans hR) hwf
  rw [← h.st.pc] at he hi
  simp only [Riscv.AccessRun, AlIsa.AccessRun, hh, Bool.false_eq_true, ↓reduceIte]
  refine ⟨he, ⟨fun c hc _ => by rw [hi] at hc; simp [Riscv.alIsa, Riscv.reads] at hc, fun c hc hc1 => ?_⟩, ?_⟩
  · rw [hi] at hc
    simp only [Riscv.alIsa, Riscv.writes, hA, storeCells, List.range_one, List.map_cons, List.map_nil, List.mem_cons,
      List.mem_nil_iff, or_false] at hc
    subst hc; simp only at hc1; rw [hr] at hc1; exact absurd hc1 (by decide)
  · show _ ≤ _
    rw [hi]
    simp only [AlIsa.bumpB, Riscv.alIsa, Riscv.writes, hA, storeCells, List.range_one, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, hr, ↓reduceIte, Int.ofNat_eq_natCast, Int.natCast_zero, Int.add_zero, hq]
    exact Int.le_refl _

theorem StA.addi {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (d s : Nat) (k : BitVec 64) (a : Addr) (o : Int)
    (hi : prog.getD p .nop = .opi d s .addi k) (hd : d < 32) (hd0 : d ≠ 0) (hs : s < 32) (hs0 : s ≠ 0) (hR : R s = gprWord a)
    (ho : a.off + k.toInt = o) :
    StA vlmax rodata prog S (n + 1) (p + 1) (upd R d (gprWord ⟨a.region, o⟩)) M B0 B :=
  h.quiet (h.st.addi d s k a o hi hd hd0 hs hs0 hR ho) (by intro c hc; rw [hi] at hc; simp [Riscv.reads] at hc)
    (by intro c hc; rw [hi] at hc; simp [Riscv.writes] at hc)

theorem StA.andi7 {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (d s : Nat) (a : Addr)
    (hi : prog.getD p .nop = .opi d s .andi 7#64) (hd : d < 32) (hd0 : d ≠ 0) (hs : s < 32) (hs0 : s ≠ 0) (hR : R s = gprWord a) :
    StA vlmax rodata prog S (n + 1) (p + 1) (upd R d (gprWord ⟨0, a.off % 8⟩)) M B0 B :=
  h.quiet (h.st.andi7 d s a hi hd hd0 hs hs0 hR) (by intro c hc; rw [hi] at hc; simp [Riscv.reads] at hc)
    (by intro c hc; rw [hi] at hc; simp [Riscv.writes] at hc)

theorem StA.mv {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (d s : Nat)
    (hi : prog.getD p .nop = .mv d s) (hd : d < 32) (hd0 : d ≠ 0) (hs : s < 32) (hs0 : s ≠ 0) :
    StA vlmax rodata prog S (n + 1) (p + 1) (upd R d (R s)) M B0 B :=
  h.quiet (h.st.mv d s hi hd hd0 hs hs0) (by intro c hc; rw [hi] at hc; simp [Riscv.reads] at hc)
    (by intro c hc; rw [hi] at hc; simp [Riscv.writes] at hc)

theorem StA.li {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (d : Nat) (imm : BitVec 64)
    (hi : prog.getD p .nop = .li d imm) (hd : d < 32) (hd0 : d ≠ 0) :
    StA vlmax rodata prog S (n + 1) (p + 1) (upd R d imm) M B0 B :=
  h.quiet (h.st.li d imm hi hd hd0) (by intro c hc; rw [hi] at hc; simp [Riscv.reads] at hc)
    (by intro c hc; rw [hi] at hc; simp [Riscv.writes] at hc)

theorem StA.brz {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (c : Riscv.BCond) (a t : Nat) (x : Int)
    (hi : prog.getD p .nop = .br c a 0 t) (ha : a < 32) (ha0 : a ≠ 0) (hR : R a = gprWord ⟨0, x⟩) (hx : (⟨0, x⟩ : Addr).wf) :
    StA vlmax rodata prog S (n + 1) (if Riscv.brHolds c x 0 then t else p + 1) R M B0 B :=
  h.quiet (h.st.brz c a t x hi ha ha0 hR hx) (by intro c hc; rw [hi] at hc; simp [Riscv.reads] at hc)
    (by intro c hc; rw [hi] at hc; simp [Riscv.writes] at hc)

theorem StA.j {B0 B : Int} (h : StA vlmax rodata prog S n p R M B0 B) (t : Nat) (hi : prog.getD p .nop = .j t) :
    StA vlmax rodata prog S (n + 1) t R M B0 B :=
  h.quiet (h.st.j t hi) (by intro c hc; rw [hi] at hc; simp [Riscv.reads] at hc)
    (by intro c hc; rw [hi] at hc; simp [Riscv.writes] at hc)

end

end Keccaktree.Kernels.RiscvAccSt
