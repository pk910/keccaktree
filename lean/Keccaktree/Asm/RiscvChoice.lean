import Keccaktree.Asm.RiscvEntryCtl
import Keccaktree.Asm.LibRv
import Keccaktree.Asm.RiscvSteps
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# RISC-V with any legal vector-length choice

`Riscv.exec vlmax` sets `vl = min(avl, VLMAX)` at a `vsetvli`.  RVV 1.0 (§6.3) allows more: for
`VLMAX < avl < 2·VLMAX` any `⌈avl/2⌉ ≤ vl ≤ VLMAX`.  `isaCh V ch` is the instruction set whose
`vsetvli` takes `vl = ch avl` for a choice function `ch`; `LegalVl V ch` is the RVV 1.0 constraint.
Every other instruction is `Riscv.exec V`.  Implementation: one step of `isaCh` is a step of
`Riscv.exec` with the per-step `vlmax := vlFor ch V i s` (`ch avl` at a `vsetvli`, a legal choice is
`≤ avl`, so `min avl (ch avl) = ch avl`), which gives the homomorphism, error, control-override
and successor lemmas from those of `Riscv.exec`.  `run_ovr_ann_ch`, `mkKernelRvCh` and `lib_rv_ch`
are the library layer for `isaCh`; `run_ch_of_pathOk` transfers a recorded `vsetvli`-free path of
`isa V` to `isaCh V ch`.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next

variable {α : Type} [LaneOps α]

/-- The vector length the hardware may choose: RVV 1.0 §6.3 constraints for `VLMAX = V`. -/
def LegalVl (V : Nat) (ch : Nat → Nat) : Prop :=
  ∀ avl, (avl ≤ V → ch avl = avl) ∧ (V < avl → avl < 2 * V → (avl + 1) / 2 ≤ ch avl ∧ ch avl ≤ V) ∧
    (2 * V ≤ avl → ch avl = V)

/-- The choice the deterministic model makes. -/
theorem legal_min (V : Nat) : LegalVl V (fun a => min a V) := by
  intro avl; dsimp only; refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩ <;> omega

/-- The `vlmax` a step of `isaCh` runs `Riscv.exec` with. -/
def vlFor (ch : Nat → Nat) (V : Nat) (i : Instr) (s : State α) : Nat :=
  match i with
  | .vsetvli _ a => match LaneOps.asConst (getR s a) with
    | some avl => ch avl.toNat
    | none => V
  | _ => V

def execCh (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (i : Instr) (s : State α) : State α :=
  exec (vlFor ch V i s) rodata i s

theorem vlFor_not_isVset (ch : Nat → Nat) (V : Nat) (i : Instr) (s : State α) (h : i.isVset = false) :
    vlFor ch V i s = V := by
  cases i <;> simp [Instr.isVset] at h <;> rfl

theorem vlFor_not_vset (ch : Nat → Nat) (V : Nat) (i : Instr) (s : State α) (h : i.usesVlmax = false) :
    vlFor ch V i s = V := vlFor_not_isVset ch V i s (Instr.isVset_of_usesVlmax i h)

theorem execCh_not_isVset (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (i : Instr) (s : State α)
    (h : i.isVset = false) : execCh V ch rodata i s = exec V rodata i s := by
  unfold execCh; rw [vlFor_not_isVset ch V i s h]

theorem execCh_not_vset (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (i : Instr) (s : State α)
    (h : i.usesVlmax = false) : execCh V ch rodata i s = exec V rodata i s := by
  unfold execCh; rw [vlFor_not_vset ch V i s h]

theorem execCh_halted (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (i : Instr) (s : State α)
    (hh : s.halted = true) : execCh V ch rodata i s = s := by
  unfold execCh; cases i <;> simp [exec, hh]

theorem execCh_map {β : Type} [LaneOps β] {f : α → β} (hf : IsHom f) (V : Nat) (ch : Nat → Nat)
    (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (hne : (execCh V ch rodata i st).err = false) :
    execCh V ch rodata i (mapState f st) = mapState f (execCh V ch rodata i st) := by
  cases hh : st.halted
  · cases hu : i.isVset
    · rw [execCh_not_isVset V ch rodata i _ hu, execCh_not_isVset V ch rodata i _ hu]
      rw [execCh_not_isVset V ch rodata i _ hu] at hne
      exact exec_map hf V rodata i st hne
    · cases i <;> simp [Instr.isVset] at hu
      rename_i d a
      unfold execCh at hne ⊢
      have hv : vlFor ch V (.vsetvli d a) (mapState f st) = vlFor ch V (.vsetvli d a) st := by
        simp only [vlFor, getR_map hf]
        rcases hx : LaneOps.asConst (getR st a) with _ | x
        · exfalso
          simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, vlFor, hx] at hne
          simp [State.fail] at hne
        · rw [hf.asConst _ _ hx]
      rw [hv]
      exact exec_map hf _ rodata _ st hne
  · rw [execCh_halted V ch rodata i _ (by rw [halted_map]; exact hh), execCh_halted V ch rodata i _ hh]

theorem err_execCh (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (i : Instr) (st : State α)
    (h : st.err = true) : (execCh V ch rodata i st).err = true := err_exec _ rodata i st h

/-- RISC-V with the vector-length choice `ch` at `vsetvli` (`VLMAX = V` otherwise unused). -/
@[reducible] def isaCh (V : Nat) (ch : Nat → Nat) : Isa where
  Instr := Instr
  nop := .nop
  exec := fun rodata i s => execCh V ch rodata i s
  exec_map := fun f hf rodata i st hne => execCh_map hf V ch rodata i st hne
  err_exec := fun rodata i st h => err_execCh V ch rodata i st h

/-- The deterministic model is the `min` choice. -/
theorem execCh_min (V : Nat) (rodata : Array (BitVec 64)) (i : Instr) (s : State α) :
    execCh V (fun a => min a V) rodata i s = exec V rodata i s := by
  cases hu : i.isVset
  · exact execCh_not_isVset V _ rodata i s hu
  · cases i <;> simp [Instr.isVset] at hu
    rename_i d a
    unfold execCh
    cases hh : s.halted
    · simp only [vlFor]
      rcases hx : LaneOps.asConst (getR s a) with _ | x
      · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, hx]
      · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, hx]
        have : min x.toNat (min x.toNat V) = min x.toNat V := by omega
        rw [this]
    · simp [exec, hh]

theorem run_min (V : Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (s : State α), (isaCh V (fun a => min a V)).run rodata prog n s = (isa V).run rodata prog n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    show (if s.halted then s else (isaCh V _).run rodata prog n (execCh V _ rodata (prog.getD s.pc .nop) s)) =
      (if s.halted then s else (isa V).run rodata prog n (exec V rodata (prog.getD s.pc .nop) s))
    rw [execCh_min, ih]

/-- A program without `vsetvli` runs the same under every choice. -/
theorem run_ch_scalar (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (prog : Array Instr)
    (h : prog.toList.all (fun i => !i.usesVlmax) = true) :
    ∀ (n : Nat) (s : State α), (isaCh V ch).run rodata prog n s = (isa V).run rodata prog n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    show (if s.halted then s else (isaCh V ch).run rodata prog n (execCh V ch rodata (prog.getD s.pc .nop) s)) =
      (if s.halted then s else (isa V).run rodata prog n (exec V rodata (prog.getD s.pc .nop) s))
    rw [execCh_not_vset V ch rodata _ s (getD_usesVlmax prog h s.pc), ih]

/-- A recorded `vsetvli`-free path of `isa V`, followed by a concrete state, is the same run under
every choice. -/
theorem run_ch_of_pathOk (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) (idx : List Nat)
    (env : Nat → BitVec 64) (t : State E) (h : (isa V).pathOk rodata prog idx t = true)
    (hv : idx.all (fun p => !(prog.getD p .nop).usesVlmax) = true) :
    (isaCh V ch).run rodata prog idx.length (mapState (E.eval env) t) =
      (isa V).run rodata prog idx.length (mapState (E.eval env) t) := by
  induction idx generalizing t with
  | nil => rfl
  | cons i rest ih =>
    simp only [Isa.pathOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨⟨⟨he, hh⟩, hpc⟩, hrest⟩ := h
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hv
    show (if (mapState (E.eval env) t).halted then _ else (isaCh V ch).run rodata prog rest.length
        (execCh V ch rodata (prog.getD (mapState (E.eval env) t).pc .nop) (mapState (E.eval env) t))) =
      (if (mapState (E.eval env) t).halted then _ else (isa V).run rodata prog rest.length
        (exec V rodata (prog.getD (mapState (E.eval env) t).pc .nop) (mapState (E.eval env) t)))
    simp only [halted_map, hh, Bool.false_eq_true, ↓reduceIte, pc_map, hpc]
    rw [execCh_not_vset V ch rodata _ _ hv.1,
      exec_map (E.eval_isHom env) V rodata _ t ((isa V).pathOk_err rodata prog rest _ hrest)]
    exact ih _ hrest hv.2

/-! ## Control override and successors, hence the library layer -/

theorem vlFor_ovr (ch : Nat → Nat) (V : Nat) (i : Instr) (D : Dom) (c : Ctl) (s : State α) :
    vlFor ch V i (ovr D c s) = vlFor ch V i s := by
  cases i <;> rfl

theorem execCh_ovr (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (D : Dom) (c : Ctl) (i : Instr) (s : State α)
    (hok : ctlOk D i = true) (hh : s.halted = false) (he : (execCh V ch rodata i s).err = false) :
    execCh V ch rodata i (ovr D c s) = ovr (ctlAfter D i) c (execCh V ch rodata i s) := by
  unfold execCh at he ⊢
  rw [vlFor_ovr]
  exact exec_ovr _ rodata D c i s hok hh he

theorem ch_run_err (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (s : State α), s.err = true → ((isaCh V ch).run rodata prog n s).err = true
  | 0, s, h => h
  | n + 1, s, h => by
    simp only [Isa.run]
    split
    · exact h
    · exact ch_run_err V ch rodata prog n _ (err_execCh V ch rodata _ s h)

/-- **A run from any vector length**, under any choice. -/
theorem run_ovr_ann_ch (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) (ann : Nat → Dom)
    (hann : AnnOk prog ann) :
    ∀ (n : Nat) (s : State α) (c : Ctl), ((isaCh V ch).run rodata prog n s).err = false →
      ∃ c' : Ctl, (isaCh V ch).run rodata prog n (ovr (ann s.pc) c s) =
        ovr (ann ((isaCh V ch).run rodata prog n s).pc) c' ((isaCh V ch).run rodata prog n s)
  | 0, s, c, _ => ⟨c, rfl⟩
  | n + 1, s, c, he => by
    cases hh : s.halted
    · have hs : ∀ t : State α, t.halted = false → (isaCh V ch).run rodata prog (n + 1) t =
          (isaCh V ch).run rodata prog n (execCh V ch rodata (prog.getD t.pc .nop) t) := by
        intro t ht; show (if t.halted then t else _) = _; rw [ht]; rfl
      rw [hs s hh] at he ⊢
      rw [hs _ (by rw [ovr_halted]; exact hh), ovr_pc]
      have he1 : (execCh V ch rodata (prog.getD s.pc .nop) s).err = false := by
        cases hc : (execCh V ch rodata (prog.getD s.pc .nop) s).err
        · rfl
        · rw [ch_run_err V ch rodata prog n _ hc] at he; exact absurd he (by decide)
      obtain ⟨hok, hsucc⟩ := hann s.pc
      rw [execCh_ovr V ch rodata _ c _ s hok hh he1]
      rcases exec_pc _ rodata _ s hh he1 with ⟨hh', hq⟩ | ⟨hh', hpc, hD⟩
      · obtain ⟨c1, hc1⟩ := Arm.ovr_mono _ _ (hsucc _ hq) c (execCh V ch rodata (prog.getD s.pc .nop) s)
        rw [hc1]
        exact run_ovr_ann_ch V ch rodata prog ann hann n _ c1 he
      · have hh2 : (execCh V ch rodata (prog.getD s.pc .nop) s).halted = true := hh'
        have hpc2 : (execCh V ch rodata (prog.getD s.pc .nop) s).pc = s.pc := hpc
        rw [hD, Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh2), Isa.run_halted _ _ _ _ _ hh2, hpc2]
        exact ⟨c, rfl⟩
    · rw [Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh), Isa.run_halted _ _ _ _ _ hh]
      exact ⟨c, rfl⟩

end Keccaktree.Asm.Riscv

namespace Keccaktree.Asm.LibRv
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibTable

/-- What a RISC-V kernel's all-count proof provides under the choice `ch`. -/
def NormThmRvCh (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (entry : Nat)
    (steps : Nat → Nat → Nat) (targets : List String) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryR off count input S → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    Library.Outcome EntryRv Digest targets off count input S ((Riscv.isaCh V ch).run rodata prog (steps off count) S)

/-- **A RISC-V kernel of the library under the vector-length choice `ch`** (any `vl` at entry). -/
def mkKernelRvCh (V : Nat) (ch : Nat → Nat) (name : String) (rank : Nat) (targets : List String)
    (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (entry : Nat) (steps : Nat → Nat → Nat) (ann : Nat → Dom)
    (hann : Riscv.AnnOk prog ann) (hentry : ann entry = Dom.all)
    (h : NormThmRvCh V ch rodata prog entry steps targets) : Library.KernelThm (Riscv.isaCh V ch) EntryRv Digest where
  name := name
  rank := rank
  targets := targets
  rodata := rodata
  prog := prog
  entry := entry
  steps := steps
  thm := fun off count input S hS => by
    obtain ⟨hE, hb⟩ := hS
    have h0 := h off count input { normCtl S with pc := entry } (hE.with_pc entry) hb rfl
    obtain ⟨c', hc'⟩ := Riscv.run_ovr_ann_ch V ch rodata prog ann hann (steps off count) { normCtl S with pc := entry }
      (Ctl.of { S with pc := entry }) h0.2.1
    have hS1 : ovr (ann ({ normCtl S with pc := entry } : State (BitVec 64)).pc) (Ctl.of { S with pc := entry })
        { normCtl S with pc := entry } = { S with pc := entry } := by
      show ovr (ann entry) _ (normCtl { S with pc := entry }) = _
      rw [hentry, ovr_normCtl]
    rw [hS1] at hc'
    rw [hc']
    exact outcome_ovr_rv targets off count input _ _ _ _ _ rfl h0

/-- **The RISC-V library under any vector-length choice.** -/
theorem lib_rv_ch (V : Nat) (ch : Nat → Nat) (T : Library.Table (Riscv.isaCh V ch) EntryRv Digest)
    (hT : T.shape = rvShape) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryRv K.name off count input S → Library.LibOk T K off count input S :=
  lib_of_shape T rvShape hT rvShape_ok

end Keccaktree.Asm.LibRv

namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next

theorem run_one_ch (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) (S : State (BitVec 64))
    (hh : S.halted = false) : (isaCh V ch).run rodata prog 1 S = execCh V ch rodata (prog.getD S.pc .nop) S := by
  show (if S.halted then S else (isaCh V ch).run rodata prog 0 (execCh V ch rodata (prog.getD S.pc .nop) S)) = _
  rw [hh]; rfl

/-- `vsetvli d, a` with `a` holding the number `r`, under the choice `ch` (a choice never exceeds the
requested length). -/
theorem execCh_vsetvli_num (V : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d a : Nat)
    (r : Int) (hh : S.halted = false) (ha : getR S a = gprWord ⟨0, r⟩) (h0 : 0 ≤ r) (h1 : r < 2 ^ 55)
    (hle : ch r.toNat ≤ r.toNat) :
    execCh V ch rodata (.vsetvli d a) S = next { setR S d (BitVec.ofNat 64 (ch r.toNat)) with vl := ch r.toNat } := by
  have hv : vlFor ch V (.vsetvli d a) S = ch r.toNat := by
    show (match LaneOps.asConst (getR S a) with | some avl => ch avl.toNat | none => V) = _
    rw [ha]; show ch (gprWord ⟨0, r⟩).toNat = _; rw [gprWord_num_toNat r h0 h1]
  unfold execCh
  rw [hv, exec_vsetvli_num _ rodata S d a r hh ha h0 h1, Nat.min_eq_right hle]

/-- A legal choice never exceeds the requested length, and is at least one for a non-empty request
(given `VLMAX ≥ 1`). -/
theorem LegalVl.bounds {V : Nat} {ch : Nat → Nat} (h : LegalVl V ch) (hV : 1 ≤ V) (r : Nat) (hr : 1 ≤ r) :
    1 ≤ ch r ∧ ch r ≤ r ∧ ch r ≤ V := by
  obtain ⟨h1, h2, h3⟩ := h r
  by_cases a : r ≤ V
  · have := h1 a; omega
  · by_cases b : r < 2 * V
    · have := h2 (by omega) b; omega
    · have := h3 (by omega); omega

end Keccaktree.Asm.Riscv

namespace Keccaktree.Asm
open Keccaktree.Asm.X86

/-- **A certified `vsetvli`-free slice runs the same under every vector-length choice**, at every
relocated position. -/
theorem SliceCert.run_ch {V : Nat} (ch : Nat → Nat) {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {B : Int}
    (C : SliceCert (Riscv.isa V) (Riscv.isaReloc V) rodata prog B)
    (hv : C.idx.all (fun p => !(prog.getD p .nop).usesVlmax) = true) (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B)
    (S : State (BitVec 64)) (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) (hs : SliceCert.Ok S) :
    (Riscv.isaCh V ch).run rodata prog C.idx.length S = (Riscv.isa V).run rodata prog C.idx.length S := by
  have hok := C.dec_ok ρ hρ hw
  have hpath := pathOk_reloc (Riscv.isaReloc V) ρ hρ rodata prog C.idx C.cut C.path hok
  have he : mapState (E.eval (envOf S)) (relocState ρ C.cut) = S := by
    show mapState (E.eval (envOf S)) (relocState ρ (cutOf C.ctl C.sc)) = S
    rw [hc]; exact eval_cutOf C.ctl S hs
  have := Riscv.run_ch_of_pathOk V ch rodata prog C.idx (envOf S) _ hpath hv
  rw [he] at this
  exact this

end Keccaktree.Asm
