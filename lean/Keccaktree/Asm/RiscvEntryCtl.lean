import Keccaktree.Asm.ArmEntryCtl
import Keccaktree.Asm.RiscvHom
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# RISC-V: the vector length at entry

The RISC-V ABI leaves `vl`/`vtype` unspecified at a call.  The model reads `vl`
only in the vector instructions and writes it only in `vsetvli`; flags and
masks are never touched.  As for AArch64 (no calls, static successors), a
dirty-set annotation checked by the kernel gives `run_ovr_ann`: the run from any
`vl` is the run from the normalised state, up to the components still dirty.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 (State Dom Ctl ovr ovr_v ovr_g ovr_gd ovr_mem ovr_pc ovr_depth ovr_err ovr_halted
  ovr_tail getV_ovr getGD_ovr loadWords_ovr read_ovr fail_ovr)
open Keccaktree.Asm.Arm (withAddr addr gx setX)
open LaneOps

variable {α : Type} [LaneOps α]

def isVec : Instr → Bool
  | .vop .. | .vnot .. | .vshifti .. | .vshiftx .. | .vxorx .. | .vmvi .. | .vmvx .. | .vmvv .. | .vlseg ..
  | .vsseg .. => true
  | _ => false

def ctlOk (D : Dom) (i : Instr) : Bool := !(isVec i && D.vl)

def ctlAfter (D : Dom) : Instr → Dom
  | .vsetvli _ _ => { D with vl := false }
  | _ => D

def succs (p : Nat) : Instr → List Nat
  | .j t => [t]
  | .br _ _ _ t => [t, p + 1]
  | .ret | .unsupported _ => []
  | _ => [p + 1]

theorem setActive_ovr (zf cf nf vf : Bool) (k : List Nat) (c : Ctl) (s : State α) (d : Nat) (f : Nat → α) :
    setActive (ovr ⟨zf, cf, nf, vf, false, k⟩ c s) d f = ovr ⟨zf, cf, nf, vf, false, k⟩ c (setActive s d f) := rfl

theorem foldl_setActive_ovr (zf cf nf vf : Bool) (k : List Nat) (c : Ctl) (g : Nat → Nat → α) (d : Nat) :
    ∀ (l : List Nat) (s : State α),
      l.foldl (fun s' f => setActive s' (d + f) (g f)) (ovr ⟨zf, cf, nf, vf, false, k⟩ c s) =
        ovr ⟨zf, cf, nf, vf, false, k⟩ c (l.foldl (fun s' f => setActive s' (d + f) (g f)) s)
  | [], s => rfl
  | f :: l, s => by
    simp only [List.foldl_cons]
    rw [setActive_ovr]
    exact foldl_setActive_ovr zf cf nf vf k c g d l _

theorem storeWords_ovr' (D : Dom) (c : Ctl) (s : State α) (a : Addr) (vs : List α) :
    (ovr D c s).storeWords a vs = (s.storeWords a vs).map (ovr D c) := X86.storeWords_ovr D c s a vs

set_option hygiene false in
macro "rv_ovr_gen" : tactic => `(tactic| (
  try simp only [withAddr, addr, gx, getR, setR, storeWords_ovr', loadWords_ovr, getGD_ovr, fail_ovr] at he ⊢
  try simp only [ovr_v, ovr_g, ovr_gd, ovr_mem, ovr_pc, ovr_depth, ovr_err, ovr_halted, ovr_tail, hh] at he ⊢
  repeat' split
  all_goals (try simp_all only [↓reduceIte, Option.map_some, Option.map_none])
  all_goals (repeat' split)
  all_goals (try simp_all only [↓reduceIte])
  all_goals (try simp only [Option.some.injEq] at *)
  all_goals (try subst_vars)
  all_goals first | rfl | (simp_all [State.fail, next]; done) | (simp_all only [ovr_halted]; rfl)))

set_option maxHeartbeats 4000000 in
theorem exec_ovr (vlmax : Nat) (rodata : Array (BitVec 64)) (D : Dom) (c : Ctl) (i : Instr) (s : State α)
    (hok : ctlOk D i = true) (hh : s.halted = false) (he : (exec vlmax rodata i s).err = false) :
    exec vlmax rodata i (ovr D c s) = ovr (ctlAfter D i) c (exec vlmax rodata i s) := by
  cases i
  case vlseg d b nf =>
    obtain ⟨zf, cf, nf', vf, vl, k⟩ := D
    simp only [ctlOk, isVec, Bool.true_and, Bool.not_eq_true'] at hok
    subst hok
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, withAddr, addr, gx, getGD_ovr,
      fail_ovr] at he ⊢
    split
    · rename_i a _
      have e : (ovr ⟨zf, cf, nf', vf, false, k⟩ c s).loadWords rodata a (nf * (ovr ⟨zf, cf, nf', vf, false, k⟩ c s).vl) =
          s.loadWords rodata a (nf * s.vl) := rfl
      rw [e]
      rcases hl : s.loadWords rodata a (nf * s.vl) with _ | ws
      · rfl
      · show next (List.foldl _ (ovr _ c s) _) = _
        rw [foldl_setActive_ovr]; rfl
    · rfl
  case vsseg src b nf =>
    obtain ⟨zf, cf, nf', vf, vl, k⟩ := D
    simp only [ctlOk, isVec, Bool.true_and, Bool.not_eq_true'] at hok
    subst hok
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, withAddr, addr, gx, getGD_ovr,
      fail_ovr] at he ⊢
    split
    · rename_i a _
      have e : (ovr ⟨zf, cf, nf', vf, false, k⟩ c s).storeWords a
          ((List.range (nf * (ovr ⟨zf, cf, nf', vf, false, k⟩ c s).vl)).map fun q =>
            lane (ovr ⟨zf, cf, nf', vf, false, k⟩ c s) (src + q % nf) (q / nf)) =
          (s.storeWords a ((List.range (nf * s.vl)).map fun q => lane s (src + q % nf) (q / nf))).map
            (ovr ⟨zf, cf, nf', vf, false, k⟩ c) := storeWords_ovr' _ c s a _
      rw [e]
      rcases (s.storeWords a ((List.range (nf * s.vl)).map fun q => lane s (src + q % nf) (q / nf))) with _ | s' <;> rfl
    · rfl
  case vsetvli d a =>
    obtain ⟨zf, cf, nf', vf, vl, k⟩ := D
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter] at he ⊢
    have e : getR (ovr ⟨zf, cf, nf', vf, vl, k⟩ c s) a = getR s a := rfl
    rw [e]
    split
    · simp only [setR]; split <;> rfl
    · rename_i h; simp [h, State.fail] at he
  all_goals first
    | (obtain ⟨zf, cf, nf', vf, vl, k⟩ := D
       simp only [ctlOk, isVec, Bool.true_and, Bool.not_eq_true'] at hok
       subst hok
       simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter] at he ⊢
       rv_ovr_gen)
    | (simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, ctlOk] at he hok ⊢
       rv_ovr_gen)

section
variable (s : State α)
@[simp] theorem next_pc' : (next s).pc = s.pc + 1 := rfl
@[simp] theorem next_halted' : (next s).halted = s.halted := rfl
@[simp] theorem setR_pc' (n : Nat) (x : α) : (setR s n x).pc = s.pc := by unfold setR; split <;> rfl
@[simp] theorem setR_halted' (n : Nat) (x : α) : (setR s n x).halted = s.halted := by unfold setR; split <;> rfl
@[simp] theorem setActive_pc' (d : Nat) (f : Nat → α) : (setActive s d f).pc = s.pc := rfl
@[simp] theorem setActive_halted' (d : Nat) (f : Nat → α) : (setActive s d f).halted = s.halted := rfl
@[simp] theorem setX_pc'' (n : Nat) (a : Addr) : (setX s n a).pc = s.pc := rfl
@[simp] theorem setX_halted'' (n : Nat) (a : Addr) : (setX s n a).halted = s.halted := rfl
theorem foldl_setActive_pc (g : Nat → Nat → α) (d : Nat) : ∀ (l : List Nat) (s : State α),
    (l.foldl (fun s' f => setActive s' (d + f) (g f)) s).pc = s.pc ∧
    (l.foldl (fun s' f => setActive s' (d + f) (g f)) s).halted = s.halted
  | [], s => ⟨rfl, rfl⟩
  | f :: l, s => foldl_setActive_pc g d l _
end

set_option maxHeartbeats 1000000 in
theorem exec_pc (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (s : State α) (hh : s.halted = false)
    (he : (exec vlmax rodata i s).err = false) :
    ((exec vlmax rodata i s).halted = false ∧ (exec vlmax rodata i s).pc ∈ succs s.pc i) ∨
    ((exec vlmax rodata i s).halted = true ∧ (exec vlmax rodata i s).pc = s.pc ∧ ∀ D, ctlAfter D i = D) := by
  cases i
  case sd src b off =>
    simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr] at he ⊢
    rcases ha : addr s b off with _ | a
    · simp [ha, State.fail] at he
    · simp only [ha] at he ⊢
      rcases hst : s.storeWords a [getR s src] with _ | s'
      · simp [hst, State.fail] at he
      · simp only [hst]
        obtain ⟨h1, h2⟩ := X86.storeWords_some _ _ _ _ hst
        left; exact ⟨by simp [h1, hh], by simp [succs, h2]⟩
  case vsseg src b nf =>
    simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr] at he ⊢
    rcases ha : addr s b 0 with _ | a
    · simp [ha, State.fail] at he
    · simp only [ha] at he ⊢
      rcases hst : s.storeWords a ((List.range (nf * s.vl)).map fun q => lane s (src + q % nf) (q / nf)) with _ | s'
      · simp [hst, State.fail] at he
      · simp only [hst]
        obtain ⟨h1, h2⟩ := X86.storeWords_some _ _ _ _ hst
        left; exact ⟨by simp [h1, hh], by simp [succs, h2]⟩
  all_goals simp only [exec, hh, Bool.false_eq_true, ↓reduceIte] at he ⊢
  all_goals (try simp only [withAddr, addr] at he ⊢)
  all_goals (repeat' split)
  all_goals (try (simp only [State.fail] at he; exact absurd he (by decide)))
  all_goals (try subst_vars)
  all_goals first
    | (left; refine ⟨?_, ?_⟩ <;> simp_all [succs, foldl_setActive_pc] <;> done)
    | (right; exact ⟨trivial, trivial, fun D => rfl⟩)
    | (exfalso; simp_all [State.fail] <;> done)
    | (exfalso; (repeat' split at he) <;> simp_all [State.fail, next] <;> done)

def AnnOk (prog : Array Instr) (ann : Nat → Dom) : Prop :=
  ∀ p, ctlOk (ann p) (prog.getD p .nop) = true ∧
    ∀ q ∈ succs p (prog.getD p .nop), (ctlAfter (ann p) (prog.getD p .nop)).le (ann q) = true

theorem rv_run_err (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (s : State α), s.err = true → ((isa vlmax).run rodata prog n s).err = true
  | 0, s, h => h
  | n + 1, s, h => by
    simp only [Isa.run]
    split
    · exact h
    · exact rv_run_err vlmax rodata prog n _ (err_exec vlmax rodata _ s h)

/-- **A run from any vector length** (RISC-V), with a consistent annotation. -/
theorem run_ovr_ann (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Instr) (ann : Nat → Dom)
    (hann : AnnOk prog ann) :
    ∀ (n : Nat) (s : State α) (c : Ctl), ((isa vlmax).run rodata prog n s).err = false →
      ∃ c' : Ctl, (isa vlmax).run rodata prog n (ovr (ann s.pc) c s) =
        ovr (ann ((isa vlmax).run rodata prog n s).pc) c' ((isa vlmax).run rodata prog n s)
  | 0, s, c, _ => ⟨c, rfl⟩
  | n + 1, s, c, he => by
    cases hh : s.halted
    · have hs : ∀ t : State α, t.halted = false → (isa vlmax).run rodata prog (n + 1) t =
          (isa vlmax).run rodata prog n (exec vlmax rodata (prog.getD t.pc .nop) t) := by
        intro t ht; show (if t.halted then t else _) = _; rw [ht]; rfl
      rw [hs s hh] at he ⊢
      rw [hs _ (by rw [ovr_halted]; exact hh), ovr_pc]
      have he1 : (exec vlmax rodata (prog.getD s.pc .nop) s).err = false := by
        cases hc : (exec vlmax rodata (prog.getD s.pc .nop) s).err
        · rfl
        · rw [rv_run_err vlmax rodata prog n _ hc] at he; exact absurd he (by decide)
      obtain ⟨hok, hsucc⟩ := hann s.pc
      rw [exec_ovr vlmax rodata _ c _ s hok hh he1]
      rcases exec_pc vlmax rodata _ s hh he1 with ⟨hh', hq⟩ | ⟨hh', hpc, hD⟩
      · obtain ⟨c1, hc1⟩ := Arm.ovr_mono _ _ (hsucc _ hq) c (exec vlmax rodata (prog.getD s.pc .nop) s)
        rw [hc1]
        exact run_ovr_ann vlmax rodata prog ann hann n _ c1 he
      · rw [hD, Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh'), Isa.run_halted _ _ _ _ _ hh', hpc]
        exact ⟨c, rfl⟩
    · rw [Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh), Isa.run_halted _ _ _ _ _ hh]
      exact ⟨c, rfl⟩

/-- `vl` dirty on the intervals `I`; flags and masks dirty everywhere (never read by RISC-V). -/
def vlAnn (I : List (Nat × Nat)) (p : Nat) : Dom :=
  if I.any (fun (a, b) => decide (a ≤ p ∧ p < b)) then Dom.all else { Dom.all with vl := false }

def vlAnnOkL (I : List (Nat × Nat)) : List Instr → Nat → Bool
  | [], _ => true
  | i :: l, p =>
    (ctlOk (vlAnn I p) i && (succs p i).all fun q => (ctlAfter (vlAnn I p) i).le (vlAnn I q)) &&
      vlAnnOkL I l (p + 1)

theorem vlAnnOkL_at (I : List (Nat × Nat)) :
    ∀ (l : List Instr) (p : Nat), vlAnnOkL I l p = true → ∀ j (hj : j < l.length),
      ctlOk (vlAnn I (p + j)) l[j] = true ∧
      ∀ q ∈ succs (p + j) l[j], (ctlAfter (vlAnn I (p + j)) l[j]).le (vlAnn I q) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | i :: l, p, h, j, hj => by
    simp only [vlAnnOkL, Bool.and_eq_true, List.all_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := vlAnnOkL_at I l (p + 1) h.2 j (by simpa using hj)
      simpa [show p + (j + 1) = p + 1 + j by omega] using this

def vlAnnOk (prog : Array Instr) (I : List (Nat × Nat)) : Bool :=
  I.all (fun (_, b) => decide (b ≤ prog.size)) && vlAnnOkL I prog.toList 0

theorem vlAnnOk_sound (prog : Array Instr) (I : List (Nat × Nat)) (h : vlAnnOk prog I = true) :
    AnnOk prog (vlAnn I) := by
  simp only [vlAnnOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hI, hp⟩ := h
  intro p
  by_cases hps : p < prog.size
  · have := vlAnnOkL_at I prog.toList 0 hp p (by simpa using hps)
    have hg : prog.getD p .nop = prog.toList[p]'(by simpa using hps) := by
      simp [Array.getD, hps]
    rw [hg]; simpa using this
  · have hn : ∀ q, prog.size ≤ q → vlAnn I q = { Dom.all with vl := false } := by
      intro q hq
      have : (I.any fun (a, b) => decide (a ≤ q ∧ q < b)) = false := by
        rw [Bool.eq_false_iff]
        intro hc
        simp only [List.any_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨a, b⟩, hx, h1, h2⟩ := hc
        have := hI _ hx
        simp only [decide_eq_true_eq] at this
        omega
      simp only [vlAnn, this, Bool.false_eq_true, ↓reduceIte]
    have h1 : prog.getD p .nop = .nop := by simp only [Array.getD, show ¬ p < prog.size by omega, dite_false]
    rw [h1, hn p (by omega)]
    refine ⟨rfl, ?_⟩
    intro q hq
    simp only [succs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    rw [hn (p + 1) (by omega)]
    exact X86.Dom.le_refl _

/-- One pass of the may-dirty analysis. -/
def annPass (prog : Array Instr) (ann : Array Dom) : Array Dom :=
  (List.range prog.size).foldl (fun a p =>
    let i := prog.getD p .nop
    let D' := ctlAfter (a.getD p Dom.none) i
    (succs p i).foldl (fun a q => if q < a.size then a.set! q ((a.getD q Dom.none).join D') else a) a) ann

def annotate (prog : Array Instr) (entry : Nat) (fuel : Nat := 64) : List Dom :=
  let a0 := (Array.replicate prog.size Dom.none).set! entry Dom.all
  (fuel.fold (fun _ _ a => annPass prog a) a0).toList

def vlIntervals (ann : List Dom) : List (Nat × Nat) :=
  let rec go : List Dom → Nat → Option Nat → List (Nat × Nat)
    | [], p, some a => [(a, p)]
    | [], _, none => []
    | d :: ds, p, st =>
      match st, d.vl with
      | none, true => go ds (p + 1) (some p)
      | some a, false => (a, p) :: go ds (p + 1) none
      | st, _ => go ds (p + 1) st
  go ann 0 none

end Keccaktree.Asm.Riscv
