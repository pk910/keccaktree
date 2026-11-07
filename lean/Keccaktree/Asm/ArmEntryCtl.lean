import Keccaktree.Asm.EntryCtl
import Keccaktree.Asm.ArmHom
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# AArch64: flags left behind by a tail call (or unspecified at a call)

The AArch64 model reads NZCV only in `csel` and `b.cond` and writes all four in
`cmp`/`subs`; it never touches the mask registers or `vl`.  `exec_ovr`
(as on x86): an instruction that does not read a dirty flag commutes with the
override.  The AArch64 kernels have no internal calls (`ret` halts), so their
control flow is static: a per-instruction annotation of dirty sets `ann`,
checked by the kernel (`annOk`: no instruction reads a flag dirty at its index,
and the dirty set after it is included in every successor's), gives
`run_ovr_ann`: the run from any flags is the run from the normalised state up to
the components still dirty.
-/
namespace Keccaktree.Asm.Arm
open Keccaktree.Asm
open Keccaktree.Asm.X86 (State Dom Ctl ovr ovr_v ovr_g ovr_gd ovr_mem ovr_pc ovr_depth ovr_err ovr_halted
  ovr_tail getV_ovr getGD_ovr loadWords_ovr read_ovr storeWords_ovr withStore_ovr fail_ovr)
open LaneOps

variable {α : Type} [LaneOps α]

def condReads (D : Dom) : Cond → Bool
  | .eq | .ne => !D.zf
  | .cs | .cc => !D.cf
  | .gt => !D.zf && !D.nf && !D.vf

def ctlOk (D : Dom) : Instr → Bool
  | .csel _ _ _ c | .bcond c _ => condReads D c
  | _ => true

def ctlAfter (D : Dom) : Instr → Dom
  | .cmp _ _ | .subs _ _ _ => { D with zf := false, cf := false, nf := false, vf := false }
  | _ => D

theorem condHolds_ovr (D : Dom) (c : Ctl) (s : State α) (cnd : Cond) (h : condReads D cnd = true) :
    condHolds (X86.ovr D c s) cnd = condHolds s cnd := by
  cases D with
  | mk zf cf nf vf vl k =>
    cases cnd <;> simp only [condReads, Bool.not_eq_true', Bool.and_eq_true] at h <;>
      simp_all [condHolds, X86.ovr]

section
variable (D : Dom) (c : Ctl) (s : State α)
@[simp] theorem gx_ovr (n : Nat) : gx (X86.ovr D c s) n = gx s n := rfl
@[simp] theorem addr_ovr (b : Nat) (o : Int) : addr (X86.ovr D c s) b o = addr s b o := rfl
@[simp] theorem lane_ovr (n l : Nat) : lane (X86.ovr D c s) n l = lane s n l := rfl
@[simp] theorem regWords_ovr (r : LReg) : regWords (X86.ovr D c s) r = regWords s r := by cases r <;> rfl
theorem loadReg_ovr (r : LReg) (ws : List α) : loadReg (X86.ovr D c s) r ws = X86.ovr D c (loadReg s r ws) := by
  cases r <;> rfl
theorem setX_ovr (n : Nat) (a : Addr) : setX (X86.ovr D c s) n a = X86.ovr D c (setX s n a) := rfl
theorem next_ovr : next (X86.ovr D c s) = X86.ovr D c (next s) := rfl
end

set_option hygiene false in
macro "arm_ovr_gen" : tactic => `(tactic| (
  try simp only [withX, withAddr, gx_ovr, addr_ovr, lane_ovr, regWords_ovr, loadWords_ovr, getGD_ovr,
    fail_ovr, setFlags, vop1, vop2, vop3] at he ⊢
  try simp only [ovr_v, ovr_g, ovr_gd, ovr_mem, ovr_pc, ovr_depth, ovr_err, ovr_halted, ovr_tail, hh] at he ⊢
  repeat' split
  all_goals (try simp_all only [↓reduceIte])
  all_goals (repeat' split)
  all_goals (try simp_all only [↓reduceIte])
  all_goals (try simp only [ovr_v, ovr_g, ovr_gd, ovr_mem, ovr_pc, ovr_depth, ovr_err, ovr_halted, ovr_tail, hh,
    loadReg_ovr, setX_ovr, next_ovr])
  all_goals (try simp only [Option.some.injEq] at *)
  all_goals (try subst_vars)
  all_goals first | rfl | (simp_all [State.fail, next]; done) | (simp_all only [ovr_halted]; rfl)))

theorem storeWords_ovr' (D : Dom) (c : Ctl) (s : State α) (a : Addr) (vs : List α) :
    (X86.ovr D c s).storeWords a vs = (s.storeWords a vs).map (X86.ovr D c) := X86.storeWords_ovr D c s a vs

set_option maxHeartbeats 4000000 in
theorem exec_ovr (rodata : Array (BitVec 64)) (D : Dom) (c : Ctl) (i : Instr) (s : State α)
    (hok : ctlOk D i = true) (hh : s.halted = false) (he : (exec rodata i s).err = false) :
    exec rodata i (X86.ovr D c s) = X86.ovr (ctlAfter D i) c (exec rodata i s) := by
  cases i
  case csel d a b cnd =>
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, condHolds_ovr D c s cnd hok]; rfl
  case bcond cnd t =>
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, condHolds_ovr D c s cnd hok]; rfl
  case str r b o =>
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, withAddr, addr_ovr, regWords_ovr,
      storeWords_ovr', fail_ovr] at he ⊢
    split
    · rename_i a _
      rcases hst : s.storeWords a (regWords s r) with _ | s'
      · simp only [hst, Option.map_none] <;> rfl
      · simp only [hst, Option.map_some]; rfl
    · rfl
  case stp r1 r2 b o wb =>
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, withAddr, addr_ovr, regWords_ovr,
      storeWords_ovr', fail_ovr] at he ⊢
    split
    · rename_i a _
      rcases hst : s.storeWords a (regWords s r1 ++ regWords s r2) with _ | s'
      · simp only [hst, Option.map_none] <;> rfl
      · simp only [hst, Option.map_some]; split <;> rfl
    · rfl
  all_goals simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, ctlOk] at he hok ⊢
  all_goals arm_ovr_gen

/-! ## Static control flow and dirty-set annotations -/

/-- The successors of instruction `i` at index `p` (the AArch64 kernels make no calls). -/
def succs (p : Nat) : Instr → List Nat
  | .b t => [t]
  | .bcond _ t | .cbz _ t => [t, p + 1]
  | .tailcall _ | .ret | .data => []
  | _ => [p + 1]

section
variable (s : State α)
@[simp] theorem next_pc' : (next s).pc = s.pc + 1 := rfl
@[simp] theorem next_halted' : (next s).halted = s.halted := rfl
@[simp] theorem setGD_pc' (n : Nat) (x : α) : (s.setGD n x).pc = s.pc := rfl
@[simp] theorem setGD_halted' (n : Nat) (x : α) : (s.setGD n x).halted = s.halted := rfl
@[simp] theorem setX_pc' (n : Nat) (a : Addr) : (setX s n a).pc = s.pc := rfl
@[simp] theorem setX_halted' (n : Nat) (a : Addr) : (setX s n a).halted = s.halted := rfl
@[simp] theorem setLanes_pc' (n : Nat) (lo hi : α) : (setLanes s n lo hi).pc = s.pc := rfl
@[simp] theorem setLanes_halted' (n : Nat) (lo hi : α) : (setLanes s n lo hi).halted = s.halted := rfl
@[simp] theorem loadReg_pc' (r : LReg) (ws : List α) : (loadReg s r ws).pc = s.pc := by cases r <;> rfl
@[simp] theorem loadReg_halted' (r : LReg) (ws : List α) : (loadReg s r ws).halted = s.halted := by cases r <;> rfl
end

set_option maxHeartbeats 1000000 in
/-- Where a successful step goes: a successor, or it halts in place (`ret`, tail call). -/
theorem exec_pc (rodata : Array (BitVec 64)) (i : Instr) (s : State α) (hh : s.halted = false)
    (he : (exec rodata i s).err = false) :
    ((exec rodata i s).halted = false ∧ (exec rodata i s).pc ∈ succs s.pc i) ∨
    ((exec rodata i s).halted = true ∧ (exec rodata i s).pc = s.pc ∧ ∀ D, ctlAfter D i = D) := by
  cases i <;> simp only [exec, hh, Bool.false_eq_true, ↓reduceIte] at he ⊢
  all_goals (try simp only [withX, withAddr, setFlags, vop1, vop2, vop3, State.storeWords] at he ⊢)
  all_goals (repeat' split)
  all_goals (try (simp only [State.fail] at he; exact absurd he (by decide)))
  all_goals (try simp only [Option.ite_none_right_eq_some, Option.some.injEq] at *)
  all_goals (try (obtain ⟨_, rfl⟩ := ‹_ ∧ _›))
  all_goals first
    | (left; refine ⟨?_, ?_⟩ <;> simp_all [succs] <;> done)
    | (right; exact ⟨trivial, trivial, fun D => rfl⟩)
    | (exfalso; simp_all [State.fail] <;> done)
    | (exfalso; (repeat' split at he) <;> simp_all [State.fail, next] <;> done)

def _root_.Keccaktree.Asm.X86.Dom.le (D D' : Dom) : Bool :=
  (!D.zf || D'.zf) && (!D.cf || D'.cf) && (!D.nf || D'.nf) && (!D.vf || D'.vf) && (!D.vl || D'.vl) &&
    D.k.all (D'.k.contains ·)

theorem _root_.Keccaktree.Asm.X86.Dom.le_refl (D : Dom) : D.le D = true := by
  simp [Dom.le, List.all_eq_true]

theorem ovr_mono (D D' : Dom) (h : D.le D' = true) (c : Ctl) (s : State α) :
    ∃ c' : Ctl, X86.ovr D c s = X86.ovr D' c' s := by
  refine ⟨⟨bif D.zf then c.zf else s.zf, bif D.cf then c.cf else s.cf, bif D.nf then c.nf else s.nf,
    bif D.vf then c.vf else s.vf, Vector.ofFn (fun j : Fin 8 => bif D.k.contains j.val then c.k[j.val]'j.isLt else s.k[j.val]'j.isLt),
    bif D.vl then c.vl else s.vl⟩, ?_⟩
  simp only [Dom.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hz, hc⟩, hn⟩, hv⟩, hvl⟩, hk⟩ := h
  simp only [X86.ovr]
  congr 1
  all_goals first
    | (apply Vector.ext; intro i hi
       simp only [Vector.getElem_ofFn]
       cases h1 : D.k.contains i
       · cases D'.k.contains i <;> rfl
       · have := hk i (by simpa using h1)
         rw [this]; rfl)
    | (rcases hz with hz | hz <;> simp [hz] <;> done)
    | (rcases hc with hc | hc <;> simp [hc] <;> done)
    | (rcases hn with hn | hn <;> simp [hn] <;> done)
    | (rcases hv with hv | hv <;> simp [hv] <;> done)
    | (rcases hvl with hvl | hvl <;> simp [hvl] <;> done)

/-- The annotation is consistent: no instruction reads a component dirty at its index, and the
dirty set after it is included in each successor's. -/
def annOk (prog : Array Instr) (ann : List Dom) : Bool :=
  (List.range (max prog.size ann.length)).all fun p =>
    ctlOk (ann.getD p Dom.all) (prog.getD p .nop) &&
    (succs p (prog.getD p .nop)).all fun q => (ctlAfter (ann.getD p Dom.all) (prog.getD p .nop)).le (ann.getD q Dom.all)

theorem annOk_at (prog : Array Instr) (ann : List Dom) (h : annOk prog ann = true) (p : Nat) :
    ctlOk (ann.getD p Dom.all) (prog.getD p .nop) = true ∧
    ∀ q ∈ succs p (prog.getD p .nop), (ctlAfter (ann.getD p Dom.all) (prog.getD p .nop)).le (ann.getD q Dom.all) = true := by
  by_cases hp : p < max prog.size ann.length
  · have := List.all_eq_true.mp h p (List.mem_range.mpr hp)
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    exact this
  · have hp1 : prog.size ≤ p := by simp only [Nat.max_def] at hp; split at hp <;> omega
    have hp2 : ann.length ≤ p := by simp only [Nat.max_def] at hp; split at hp <;> omega
    have h1 : prog.getD p .nop = .nop := by simp only [Array.getD, show ¬ p < prog.size by omega, dite_false]
    have h2 : ann.getD p Dom.all = Dom.all := by simp [List.getD, List.getElem?_eq_none hp2]
    rw [h1, h2]
    refine ⟨rfl, ?_⟩
    intro q hq
    simp only [succs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    have h3 : ann.getD (p + 1) Dom.all = Dom.all := by
      simp [List.getD, List.getElem?_eq_none (show ann.length ≤ p + 1 by omega)]
    rw [h3]; exact Dom.le_refl _

theorem arm_run_err (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (s : State α), s.err = true → (isa.run rodata prog n s).err = true
  | 0, s, h => h
  | n + 1, s, h => by
    simp only [Isa.run]
    split
    · exact h
    · exact arm_run_err rodata prog n _ (err_exec rodata _ s h)

/-- A consistent annotation (as a function of the instruction index). -/
def AnnOk (prog : Array Instr) (ann : Nat → Dom) : Prop :=
  ∀ p, ctlOk (ann p) (prog.getD p .nop) = true ∧
    ∀ q ∈ succs p (prog.getD p .nop), (ctlAfter (ann p) (prog.getD p .nop)).le (ann q) = true

theorem annOk_AnnOk (prog : Array Instr) (ann : List Dom) (h : annOk prog ann = true) :
    AnnOk prog (fun p => ann.getD p Dom.all) := fun p => annOk_at prog ann h p

/-- **A run from any flags** (AArch64): with a consistent annotation, the run from the state with
the components dirty at its index overridden is the run up to the components dirty at the end. -/
theorem run_ovr_ann (rodata : Array (BitVec 64)) (prog : Array Instr) (ann : Nat → Dom) (hann : AnnOk prog ann) :
    ∀ (n : Nat) (s : State α) (c : Ctl), (isa.run rodata prog n s).err = false →
      ∃ c' : Ctl, isa.run rodata prog n (X86.ovr (ann s.pc) c s) =
        X86.ovr (ann (isa.run rodata prog n s).pc) c' (isa.run rodata prog n s)
  | 0, s, c, _ => ⟨c, rfl⟩
  | n + 1, s, c, he => by
    cases hh : s.halted
    · have hs : ∀ t : State α, t.halted = false → isa.run rodata prog (n + 1) t =
          isa.run rodata prog n (exec rodata (prog.getD t.pc .nop) t) := by
        intro t ht; show (if t.halted then t else _) = _; rw [ht]; rfl
      rw [hs s hh] at he ⊢
      rw [hs _ (by rw [ovr_halted]; exact hh), ovr_pc]
      have he1 : (exec rodata (prog.getD s.pc .nop) s).err = false := by
        cases hc : (exec rodata (prog.getD s.pc .nop) s).err
        · rfl
        · rw [arm_run_err rodata prog n _ hc] at he; exact absurd he (by decide)
      obtain ⟨hok, hsucc⟩ := hann s.pc
      rw [exec_ovr rodata _ c _ s hok hh he1]
      rcases exec_pc rodata _ s hh he1 with ⟨hh', hq⟩ | ⟨hh', hpc, hD⟩
      · obtain ⟨c1, hc1⟩ := ovr_mono _ _ (hsucc _ hq) c (exec rodata (prog.getD s.pc .nop) s)
        rw [hc1]
        exact run_ovr_ann rodata prog ann hann n _ c1 he
      · rw [hD, Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh'), Isa.run_halted _ _ _ _ _ hh', hpc]
        exact ⟨c, rfl⟩
    · rw [Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh), Isa.run_halted _ _ _ _ _ hh]
      exact ⟨c, rfl⟩

/-! ## Computing an annotation (the fixpoint of the may-dirty analysis; checked by `annOk`) -/

def _root_.Keccaktree.Asm.X86.Dom.join (D D' : Dom) : Dom :=
  ⟨D.zf || D'.zf, D.cf || D'.cf, D.nf || D'.nf, D.vf || D'.vf, D.vl || D'.vl, D.k ++ D'.k.filter (!D.k.contains ·)⟩

/-- One pass over the program, propagating dirty sets along the static edges. -/
def annPass (prog : Array Instr) (ann : Array Dom) : Array Dom :=
  (List.range prog.size).foldl (fun a p =>
    let i := prog.getD p .nop
    let D' := ctlAfter (a.getD p Dom.none) i
    (succs p i).foldl (fun a q => if q < a.size then a.set! q ((a.getD q Dom.none).join D') else a) a) ann

/-- The may-dirty annotation from `entry` (everything dirty there), by `fuel` passes. -/
def annotate (prog : Array Instr) (entry : Nat) (fuel : Nat := 64) : List Dom :=
  let a0 := (Array.replicate prog.size Dom.none).set! entry Dom.all
  (fuel.fold (fun _ _ a => annPass prog a) a0).toList

/-! ## Compact annotations: the flags are dirty on a set of index intervals -/

/-- Flags dirty on the intervals `I` (`[a, b)`), the masks and `vl` dirty everywhere (AArch64 never
writes them). -/
def flagAnn (I : List (Nat × Nat)) (p : Nat) : Dom :=
  if I.any (fun (a, b) => decide (a ≤ p ∧ p < b)) then Dom.all
  else { Dom.all with zf := false, cf := false, nf := false, vf := false }

def flagAnnOkL (I : List (Nat × Nat)) : List Instr → Nat → Bool
  | [], _ => true
  | i :: l, p =>
    (ctlOk (flagAnn I p) i && (succs p i).all fun q => (ctlAfter (flagAnn I p) i).le (flagAnn I q)) &&
      flagAnnOkL I l (p + 1)

theorem flagAnnOkL_at (I : List (Nat × Nat)) :
    ∀ (l : List Instr) (p : Nat), flagAnnOkL I l p = true → ∀ j (hj : j < l.length),
      ctlOk (flagAnn I (p + j)) l[j] = true ∧
      ∀ q ∈ succs (p + j) l[j], (ctlAfter (flagAnn I (p + j)) l[j]).le (flagAnn I q) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | i :: l, p, h, j, hj => by
    simp only [flagAnnOkL, Bool.and_eq_true, List.all_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := flagAnnOkL_at I l (p + 1) h.2 j (by simpa using hj)
      simpa [show p + (j + 1) = p + 1 + j by omega] using this

def flagAnnOk (prog : Array Instr) (I : List (Nat × Nat)) : Bool :=
  I.all (fun (_, b) => decide (b ≤ prog.size)) && flagAnnOkL I prog.toList 0

theorem flagAnnOk_sound (prog : Array Instr) (I : List (Nat × Nat)) (h : flagAnnOk prog I = true) :
    AnnOk prog (flagAnn I) := by
  simp only [flagAnnOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hI, hp⟩ := h
  intro p
  by_cases hps : p < prog.size
  · have := flagAnnOkL_at I prog.toList 0 hp p (by simpa using hps)
    have hg : prog.getD p .nop = prog.toList[p]'(by simpa using hps) := by
      simp [Array.getD, hps]
    rw [hg]; simpa using this
  · have hn : ∀ q, prog.size ≤ q → flagAnn I q = { Dom.all with zf := false, cf := false, nf := false, vf := false } := by
      intro q hq
      have : (I.any fun (a, b) => decide (a ≤ q ∧ q < b)) = false := by
        rw [Bool.eq_false_iff]
        intro hc
        simp only [List.any_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨a, b⟩, hx, h1, h2⟩ := hc
        have := hI _ hx
        simp only [decide_eq_true_eq] at this
        omega
      simp only [flagAnn, this, Bool.false_eq_true, ↓reduceIte]
    have h1 : prog.getD p .nop = .nop := by simp only [Array.getD, show ¬ p < prog.size by omega, dite_false]
    rw [h1, hn p (by omega)]
    refine ⟨rfl, ?_⟩
    intro q hq
    simp only [succs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    rw [hn (p + 1) (by omega)]
    exact X86.Dom.le_refl _

/-- The dirty intervals of an annotation (for generating `flagAnn` certificates). -/
def dirtyIntervals (ann : List Dom) : List (Nat × Nat) :=
  let rec go : List Dom → Nat → Option Nat → List (Nat × Nat)
    | [], p, some a => [(a, p)]
    | [], _, none => []
    | d :: ds, p, st =>
      let dirty := d.zf || d.cf || d.nf || d.vf
      match st, dirty with
      | none, true => go ds (p + 1) (some p)
      | some a, false => (a, p) :: go ds (p + 1) none
      | st, _ => go ds (p + 1) st
  go ann 0 none

end Keccaktree.Asm.Arm
