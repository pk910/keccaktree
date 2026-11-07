import Keccaktree.Asm.Trace
import Keccaktree.Asm.X86Steps
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Control state left behind by a previous kernel

A kernel is entered either by a call (fresh flags) or by a tail call from
another kernel, which leaves its flags (x86 ZF/CF, AArch64 NZCV), mask
registers (`k`) and vector length behind.  The kernels' proofs start from a
normalised control state; this file shows that the run does not depend on
those components until the program has overwritten them.

`ovr D c s` overrides the components in the *dirty set* `D` with the values `c`.
For an instruction that does not read a dirty component (`ctlOk D i`),
executing it commutes with the override, and the components it overwrites
leave the dirty set (`ctlAfter D i`):

  `exec i (ovr D c s) = ovr (ctlAfter D i) c (exec i s)`.

Three ways to use it: `execTrace_ovr` over a recorded path (a segment),
`run_ovr_prefix` over a straight-line prefix of the program from the entry,
and `run_ovr_static` when no instruction of the program touches the dirty
components at all (e.g. `k` in a kernel without AVX-512 masks, `nf`/`vf` on x86).
-/
namespace Keccaktree.Asm.X86

variable {α : Type} [LaneOps α]

/-- Values for the control components. -/
structure Ctl where
  zf : Bool
  cf : Bool
  nf : Bool
  vf : Bool
  k : Vector Nat 8
  vl : Nat

/-- The control components of a state. -/
def Ctl.of (s : State α) : Ctl := ⟨s.zf, s.cf, s.nf, s.vf, s.k, s.vl⟩

/-- A dirty set: the flags, the vector length, and the mask registers listed in `k`. -/
structure Dom where
  zf : Bool := false
  cf : Bool := false
  nf : Bool := false
  vf : Bool := false
  vl : Bool := false
  k : List Nat := []
  deriving DecidableEq, Repr

/-- Every component dirty. -/
def Dom.all : Dom := ⟨true, true, true, true, true, [0, 1, 2, 3, 4, 5, 6, 7]⟩
/-- Nothing dirty. -/
def Dom.none : Dom := {}

/-- Override the dirty components of `s` with `c`. -/
def ovr (D : Dom) (c : Ctl) (s : State α) : State α :=
  { s with zf := bif D.zf then c.zf else s.zf, cf := bif D.cf then c.cf else s.cf,
           nf := bif D.nf then c.nf else s.nf, vf := bif D.vf then c.vf else s.vf,
           vl := bif D.vl then c.vl else s.vl,
           k := Vector.ofFn fun j : Fin 8 => bif D.k.contains j.val then c.k[j.val]'j.isLt else s.k[j.val]'j.isLt }

@[simp] theorem ovr_v (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).v = s.v := rfl
@[simp] theorem ovr_g (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).g = s.g := rfl
@[simp] theorem ovr_gd (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).gd = s.gd := rfl
@[simp] theorem ovr_mem (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).mem = s.mem := rfl
@[simp] theorem ovr_pc (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).pc = s.pc := rfl
@[simp] theorem ovr_depth (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).depth = s.depth := rfl
@[simp] theorem ovr_err (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).err = s.err := rfl
@[simp] theorem ovr_halted (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).halted = s.halted := rfl
@[simp] theorem ovr_tail (D : Dom) (c : Ctl) (s : State α) : (ovr D c s).tail = s.tail := rfl

theorem ovr_zf_clean (D : Dom) (c : Ctl) (s : State α) (h : D.zf = false) : (ovr D c s).zf = s.zf := by
  simp [ovr, h]
theorem ovr_cf_clean (D : Dom) (c : Ctl) (s : State α) (h : D.cf = false) : (ovr D c s).cf = s.cf := by
  simp [ovr, h]

theorem ovr_k_getD (D : Dom) (c : Ctl) (s : State α) (j : Nat) (h : D.k.contains j = false) :
    (ovr D c s).k.getD j 0 = s.k.getD j 0 := by
  have h' : j ∉ D.k := by simpa using h
  simp only [ovr, Vector.getD]
  by_cases hj : j < 8
  · simp [hj, h']
  · simp [hj]

/-- Nothing dirty: no change. -/
theorem ovr_none (c : Ctl) (s : State α) : ovr Dom.none c s = s := by
  cases s
  simp only [ovr, Dom.none, Bool.cond_false, List.contains_nil, State.mk.injEq, true_and, and_true]
  apply Vector.ext; intro i hi; simp

/-! ## Helpers commute with the override -/

section
variable (D : Dom) (c : Ctl) (s : State α)
@[simp] theorem getV_ovr (n : Nat) : (ovr D c s).getV n = s.getV n := rfl
@[simp] theorem getGD_ovr (n : Nat) : (ovr D c s).getGD n = s.getGD n := rfl
@[simp] theorem gx_ovr (n : Nat) : gx (ovr D c s) n = gx s n := rfl
@[simp] theorem memAddr_ovr (m : MemOp) : memAddr? (ovr D c s) m = memAddr? s m := by cases m <;> rfl
@[simp] theorem read_ovr (rodata : Array (BitVec 64)) (r : Region) (q : Int) :
    (ovr D c s).read rodata r q = s.read rodata r q := rfl
@[simp] theorem loadWords_ovr (rodata : Array (BitVec 64)) (a : Addr) (n : Nat) :
    (ovr D c s).loadWords rodata a n = s.loadWords rodata a n := rfl
@[simp] theorem readSrc_ovr (rodata : Array (BitVec 64)) (lanes : Nat) (b : Src) :
    readSrc rodata (ovr D c s) lanes b = readSrc rodata s lanes b := by
  cases b <;> simp [readSrc]
theorem storeWords_ovr (a : Addr) (vs : List α) :
    (ovr D c s).storeWords a vs = (s.storeWords a vs).map (ovr D c) := by
  simp only [State.storeWords]; split <;> rfl
@[simp] theorem fail_ovr : (ovr D c s).fail = ovr D c s.fail := rfl
theorem next_ovr : next (ovr D c s) = ovr D c (next s) := rfl
theorem setGD_ovr (n : Nat) (x : α) : (ovr D c s).setGD n x = ovr D c (s.setGD n x) := rfl
theorem setX_ovr (n : Nat) (a : Addr) : setX (ovr D c s) n a = ovr D c (setX s n a) := rfl
theorem writeV_ovr (n lanes : Nat) (vs : List α) : writeV (ovr D c s) n lanes vs = ovr D c (writeV s n lanes vs) := rfl
end

/-- `withStore` on an overridden state: the continuation sees the overridden store result. -/
theorem withStore_ovr (D : Dom) (c : Ctl) (s : State α) (a : Addr) (vs : List α) (k : State α → State α) :
    withStore (ovr D c s) a vs k =
      match s.storeWords a vs with
      | some s' => k (ovr D c s')
      | none => ovr D c s.fail := by
  simp only [withStore, storeWords_ovr]
  cases s.storeWords a vs <;> rfl

/-! ## The x86 instructions -/

def condReadsZ : Cond → Bool
  | .e | .ne | .a | .be => true
  | _ => false
def condReadsC : Cond → Bool
  | .b | .a | .ae | .be => true
  | _ => false

theorem condHolds_ovr (D : Dom) (c : Ctl) (s : State α) (cnd : Cond)
    (hz : !(D.zf && condReadsZ cnd) = true) (hc : !(D.cf && condReadsC cnd) = true) :
    condHolds (ovr D c s) cnd = condHolds s cnd := by
  cases D with
  | mk zf cf nf vf vl k =>
    cases zf <;> cases cf <;> cases cnd <;> simp_all [condHolds, ovr, condReadsZ, condReadsC]

/-- The instruction reads no dirty component (and does not conditionally write one). -/
def ctlOk (D : Dom) : Instr → Bool
  | .jcc cnd _ | .jcct cnd _ => !(D.zf && condReadsZ cnd) && !(D.cf && condReadsC cnd)
  | .sub _ _ => !D.zf && !D.cf
  | .vmov _ _ _ (some j) => !D.k.contains j
  | _ => true

/-- The dirty set after the instruction (it overwrites the components it always writes). -/
def ctlAfter (D : Dom) : Instr → Dom
  | .test _ _ | .cmpi _ _ | .cmpr _ _ | .cmpm _ _ | .cmprm _ _ | .xorz _ => { D with zf := false, cf := false }
  | .dec _ | .decm _ => { D with zf := false }
  | .bt _ _ => { D with cf := false }
  | .kmovw j _ => { D with k := D.k.filter (· != j) }
  | _ => D

/-- The instruction is not a control transfer: on success it goes to the next instruction. -/
def straight : Instr → Bool
  | .jcc _ _ | .jmp _ | .jcct _ _ | .call _ | .ret | .tailcall _ => false
  | _ => true

theorem kmovw_k (D : Dom) (c : Ctl) (s : State α) (j : Nat) (v : Nat) :
    (ovr D c s).k.setIfInBounds j v = (ovr { D with k := D.k.filter (· != j) } c { s with k := s.k.setIfInBounds j v }).k := by
  apply Vector.ext
  intro i hi
  simp only [ovr, Vector.getElem_ofFn, Vector.getElem_setIfInBounds]
  by_cases hij : j = i
  · subst hij; simp
  · have : (i != j) = true := by simp; omega
    simp [hij, List.mem_filter, this]


theorem setFlagsSub_ovr_clean (D : Dom) (c : Ctl) (s : State α) (a b : Addr) (hz : D.zf = false) (hc : D.cf = false) :
    setFlagsSub (ovr D c s) a b = ovr D c (setFlagsSub s a b) := by
  simp only [setFlagsSub]
  split
  · simp [ovr, hz, hc]
  · rfl

-- The generic case: unfold the helpers, split every decision, and compare.
set_option hygiene false in
macro "ovr_gen" : tactic => `(tactic| (
  try simp only [withX, withMem, withSrc, withLoad, readG, binop, gx_ovr, memAddr_ovr, readSrc_ovr,
    loadWords_ovr, getV_ovr, getGD_ovr, withStore_ovr, fail_ovr, setFlagsSub, repBody] at he ⊢
  try simp only [withStore] at he ⊢
  try simp only [ovr_v, ovr_g, ovr_gd, ovr_mem, ovr_pc, ovr_depth, ovr_err, ovr_halted, ovr_tail, setX_ovr, setGD_ovr, writeV_ovr, next_ovr, hh] at he ⊢
  repeat' split
  all_goals (try simp_all only [↓reduceIte])
  all_goals (repeat' split)
  all_goals (try simp_all only [↓reduceIte])
  all_goals (try simp only [ovr_v, ovr_g, ovr_gd, ovr_mem, ovr_pc, ovr_depth, ovr_err, ovr_halted, ovr_tail, setX_ovr, setGD_ovr, writeV_ovr, next_ovr, hh])
  all_goals (try simp only [Option.some.injEq] at *)
  all_goals (try subst_vars)
  all_goals first | rfl | (simp_all [State.fail, next]; done) | (simp_all only [ovr_halted]; rfl)))

set_option maxHeartbeats 2000000 in
theorem exec_ovr (rodata : Array (BitVec 64)) (D : Dom) (c : Ctl) (i : Instr) (s : State α)
    (hok : ctlOk D i = true) (hh : s.halted = false) (he : (exec rodata i s).err = false) :
    exec rodata i (ovr D c s) = ovr (ctlAfter D i) c (exec rodata i s) := by
  cases i
  case jcc cnd t =>
    simp only [ctlOk, Bool.and_eq_true] at hok
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, condHolds_ovr D c s cnd hok.1 hok.2]
    split <;> rfl
  case jcct cnd n =>
    simp only [ctlOk, Bool.and_eq_true] at hok
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, condHolds_ovr D c s cnd hok.1 hok.2]
    split <;> rfl
  case sub d imm =>
    simp only [ctlOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, withX, gx_ovr, fail_ovr, setX_ovr,
      setFlagsSub_ovr_clean D c _ _ _ hok.1 hok.2] at he ⊢
    repeat' split
    all_goals rfl
  case kmovw j m =>
    simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, withMem, memAddr_ovr, read_ovr,
      fail_ovr] at he ⊢
    repeat' split
    all_goals (try simp_all only [])
    all_goals first | rfl | (simp only [kmovw_k]; rfl) | simp_all [State.fail, next]
  case vmov lanes dst src mask =>
    cases mask with
    | none =>
      simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, ctlOk] at he hok ⊢
      ovr_gen
    | some j =>
      simp only [ctlOk, Bool.not_eq_true'] at hok
      simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, ovr_k_getD D c s j hok] at he ⊢
      ovr_gen
  all_goals simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ctlAfter, ctlOk] at he hok ⊢
  all_goals ovr_gen

/-- `sub` on a pointer register writes no flag (the model sets flags only for plain numbers). -/
theorem exec_ovr_sub_ptr (rodata : Array (BitVec 64)) (D : Dom) (c : Ctl) (s : State α) (d : Gpr) (imm : Int)
    (a : Addr) (ha : gx s d = some a) (hr : a.region ≠ 0) :
    exec rodata (.sub d imm) (ovr D c s) = ovr D c (exec rodata (.sub d imm) s) := by
  cases hh : s.halted
  · simp only [exec, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, withX, gx_ovr, ha, hr]; rfl
  · simp only [exec, ovr_halted, hh, ↓reduceIte]

/-! ## Runs -/

theorem x86_run_err (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (s : State α), s.err = true → (X86.isa.run rodata prog n s).err = true
  | 0, s, h => h
  | n + 1, s, h => by
    simp only [Isa.run]
    split
    · exact h
    · exact x86_run_err rodata prog n _ (X86.err_exec rodata _ s h)

theorem ovr_ovr_same (D : Dom) (c : Ctl) (s : State α) : ovr D c (ovr D c s) = ovr D c s := by
  simp only [ovr]
  congr 1
  · apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]; cases D.k.contains i <;> rfl
  all_goals (cases D.zf <;> cases D.cf <;> cases D.nf <;> cases D.vf <;> cases D.vl <;> rfl)

def ctlOkTrace : Dom → List Instr → Bool
  | _, [] => true
  | D, i :: l => ctlOk D i && ctlOkTrace (ctlAfter D i) l

def ctlAfterTrace : Dom → List Instr → Dom
  | D, [] => D
  | D, i :: l => ctlAfterTrace (ctlAfter D i) l

/-- **Along a path.** If the run of `s` visits the instruction indices `idx` (never halted
before a step) and no instruction of the path reads a dirty component, the run of the
overridden state is the overridden run. -/
theorem run_ovr_path (rodata : Array (BitVec 64)) (prog : Array Instr) (D : Dom) (c : Ctl) :
    ∀ (idx : List Nat) (s : State α),
    (∀ j, j < idx.length → (X86.isa.run rodata prog j s).halted = false ∧ (X86.isa.run rodata prog j s).pc = idx.getD j 0) →
    ctlOkTrace D (idx.map (prog.getD · .nop)) = true →
    (X86.isa.run rodata prog idx.length s).err = false →
    X86.isa.run rodata prog idx.length (ovr D c s) = ovr (ctlAfterTrace D (idx.map (prog.getD · .nop))) c (X86.isa.run rodata prog idx.length s)
  | [], s, _, _, _ => rfl
  | p :: rest, s, hpath, hok, he => by
    have h0 := hpath 0 (by simp)
    simp only [Isa.run, List.getD_cons_zero] at h0
    simp only [List.map_cons, ctlOkTrace, ctlAfterTrace, Bool.and_eq_true] at hok ⊢
    simp only [List.length_cons, Isa.run, ovr_halted, h0.1, Bool.false_eq_true, ↓reduceIte, ovr_pc, h0.2] at he ⊢
    have he1 : (exec rodata (prog.getD p .nop) s).err = false := by
      cases hc : (exec rodata (prog.getD p .nop) s).err
      · rfl
      · have := x86_run_err rodata prog rest.length _ hc
        rw [this] at he; exact absurd he (by decide)
    show X86.isa.run rodata prog rest.length (exec rodata (prog.getD p .nop) (ovr D c s)) = _
    rw [exec_ovr rodata D c _ s hok.1 h0.1 he1]
    apply run_ovr_path rodata prog (ctlAfter D (prog.getD p .nop)) c rest _ _ hok.2 he
    intro j hj
    have := hpath (j + 1) (by simp; omega)
    simp only [Isa.run, h0.1, Bool.false_eq_true, ↓reduceIte, h0.2, List.getD_cons_succ] at this
    exact this

/-- **No instruction of the program touches the dirty components** (e.g. `k` in a kernel without
masked moves, `nf`/`vf`/`vl` on x86): every run commutes with the override. -/
theorem run_ovr_static (rodata : Array (BitVec 64)) (prog : Array Instr) (D : Dom) (c : Ctl)
    (hprog : (prog.all fun i => ctlOk D i && ctlAfter D i == D) = true) :
    ∀ (n : Nat) (s : State α), (X86.isa.run rodata prog n s).err = false →
      X86.isa.run rodata prog n (ovr D c s) = ovr D c (X86.isa.run rodata prog n s)
  | 0, s, _ => rfl
  | n + 1, s, he => by
    cases hh : s.halted
    · simp only [Isa.run, ovr_halted, ovr_pc, hh, Bool.false_eq_true, ↓reduceIte] at he ⊢
      have hi : ctlOk D (prog.getD s.pc .nop) = true ∧ ctlAfter D (prog.getD s.pc .nop) = D := by
        simp only [Array.getD]
        split
        · rename_i hlt
          have := (Array.all_eq_true.mp hprog) s.pc hlt
          simp only [Bool.and_eq_true, beq_iff_eq] at this
          exact this
        · exact ⟨rfl, rfl⟩
      have he1 : (exec rodata (prog.getD s.pc .nop) s).err = false := by
        cases hc : (exec rodata (prog.getD s.pc .nop) s).err
        · rfl
        · have := x86_run_err rodata prog n _ hc
          rw [this] at he; exact absurd he (by decide)
      show X86.isa.run rodata prog n (exec rodata (prog.getD s.pc .nop) (ovr D c s)) = _
      rw [exec_ovr rodata D c _ s hi.1 hh he1, hi.2]
      exact run_ovr_static rodata prog D c hprog n _ he
    · simp only [Isa.run, ovr_halted, hh, ↓reduceIte]

/-! ## The entry prefix: frame set-up, then a flag-writing compare -/

/-- Frame set-up instructions allowed before the first compare (they keep `rsp` a pointer). -/
def prefixInstrOk : Instr → Bool
  | .push _ => true
  | .mov d _ => d != 4
  | .sub d _ => d == 4
  | .andi d _ => d == 4
  | _ => false

/-- A compare that writes both ZF and CF. -/
def flagWriter : Instr → Bool
  | .test _ _ | .cmpi _ _ | .cmpr _ _ => true
  | _ => false

/-- The stack offset after a set-up instruction (`rsp` as `⟨rStack, o⟩`). -/
def prefixRsp : Instr → Int → Int
  | .push _, o => o - 8
  | .sub _ imm, o => o - imm
  | .andi _ _, o => o - o % 64
  | _, o => o

/-- The `m` instructions from `p` are set-up instructions keeping `rsp` a representable stack
pointer (from offset `o`), then a compare. -/
def prefixOk (prog : Array Instr) (p : Nat) (o : Int) : Nat → Bool
  | 0 => false
  | 1 => flagWriter (prog.getD p .nop)
  | m + 2 =>
    let i := prog.getD p .nop
    prefixInstrOk i && decide (0 ≤ prefixRsp i o ∧ prefixRsp i o < 2 ^ 55) && prefixOk prog (p + 1) (prefixRsp i o) (m + 1)

theorem getGD_setGD_same (s : State α) (n : Nat) (x : α) (hn : n < 32) : (s.setGD n x).getGD n = x := by
  simp [State.getGD, State.setGD, Vector.getD, hn]

theorem getGD_setGD_other (s : State α) (n m : Nat) (x : α) (h : n ≠ m) : (s.setGD n x).getGD m = s.getGD m := by
  simp only [State.getGD, State.setGD, Vector.getD]
  by_cases hm : m < 32
  · simp [hm, Vector.getElem_setIfInBounds, h]
  · simp [hm]

theorem x86_run_succ (rodata : Array (BitVec 64)) (prog : Array Instr) (n : Nat) (t : State α) (h : t.halted = false) :
    X86.isa.run rodata prog (n + 1) t = X86.isa.run rodata prog n (exec rodata (prog.getD t.pc .nop) t) := by
  show (if t.halted then t else _) = _
  rw [h]; rfl

theorem storeWords_some (s : State α) (a : Addr) (vs : List α) (s' : State α) (h : s.storeWords a vs = some s') :
    s'.halted = s.halted ∧ s'.pc = s.pc := by
  unfold State.storeWords at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem prefix_step (rodata : Array (BitVec 64)) (D : Dom) (c : Ctl) (i : Instr) (s : State (BitVec 64)) (o : Int)
    (hi : prefixInstrOk i = true) (hh : s.halted = false) (hsp : s.getGD 4 = gprWord ⟨rStack, o⟩)
    (hwf : 0 ≤ o ∧ o < 2 ^ 55) (hwf' : 0 ≤ prefixRsp i o ∧ prefixRsp i o < 2 ^ 55)
    (he : (exec rodata i s).err = false) :
    exec rodata i (ovr D c s) = ovr D c (exec rodata i s) ∧ (exec rodata i s).halted = false ∧
      (exec rodata i s).pc = s.pc + 1 ∧ (exec rodata i s).getGD 4 = gprWord ⟨rStack, prefixRsp i o⟩ := by
  have hg := gx_of_word s 4 ⟨rStack, o⟩ hsp ⟨hwf.1, hwf.2⟩
  have hr0 : (rStack : Region) ≠ 0 := by decide
  cases i <;> simp only [prefixInstrOk, Bool.false_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hi
  case push src =>
    refine ⟨exec_ovr rodata D c _ s rfl hh he, ?_⟩
    simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg, withStore] at he ⊢
    split
    · rename_i s' hst
      obtain ⟨h1, h2⟩ := storeWords_some _ _ _ _ hst
      simp only [next, setX, prefixRsp]
      exact ⟨h1.trans hh, by rw [← h2]; rfl, getGD_setGD_same _ 4 _ (by decide)⟩
    · rename_i hc; simp only [hc, State.fail] at he; exact absurd he (by decide)
  case mov d src =>
    refine ⟨exec_ovr rodata D c _ s rfl hh he, ?_⟩
    simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, next, prefixRsp]
    exact ⟨hh, rfl, (getGD_setGD_other s d 4 _ hi).trans hsp⟩
  case sub d imm =>
    subst hi
    refine ⟨exec_ovr_sub_ptr rodata D c s 4 imm _ hg hr0, ?_⟩
    simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg, hr0, next, setX, prefixRsp]
    exact ⟨hh, rfl, getGD_setGD_same _ 4 _ (by decide)⟩
  case andi d imm =>
    subst hi
    refine ⟨exec_ovr rodata D c _ s rfl hh he, ?_⟩
    simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg] at he ⊢
    split
    · simp only [next, setX, prefixRsp]
      exact ⟨hh, rfl, getGD_setGD_same _ 4 _ (by decide)⟩
    · rename_i hc; simp only [hc, ↓reduceIte, State.fail] at he; exact absurd he (by decide)

theorem flagWriter_after (D : Dom) (i : Instr) (h : flagWriter i = true) :
    ctlAfter D i = { D with zf := false, cf := false } := by
  cases i <;> simp_all [flagWriter, ctlAfter]

/-- **The entry prefix.** From the entry `p` with `rsp = ⟨rStack, o⟩`, the `m` instructions of a
valid prefix (`prefixOk`) run the same on the overridden state, and the final compare cleans the
flags: afterwards only the other dirty components (masks, `nf`/`vf`, `vl`) can differ. -/
theorem run_ovr_prefix (rodata : Array (BitVec 64)) (prog : Array Instr) (D : Dom) (c : Ctl) :
    ∀ (m p : Nat) (o : Int) (s : State (BitVec 64)), prefixOk prog p o m = true → s.pc = p → s.halted = false →
    s.getGD 4 = gprWord ⟨rStack, o⟩ → 0 ≤ o ∧ o < 2 ^ 55 → (X86.isa.run rodata prog m s).err = false →
    X86.isa.run rodata prog m (ovr D c s) = ovr { D with zf := false, cf := false } c (X86.isa.run rodata prog m s)
  | 0, p, o, s, h, _, _, _, _, _ => by simp [prefixOk] at h
  | 1, p, o, s, h, hpc, hh, hsp, hwf, he => by
    simp only [prefixOk] at h
    simp only [Isa.run, ovr_halted, hh, Bool.false_eq_true, ↓reduceIte, ovr_pc, hpc] at he ⊢
    show exec rodata (prog.getD p .nop) (ovr D c s) = ovr _ c (exec rodata (prog.getD p .nop) s)
    rw [exec_ovr rodata D c _ s (by cases hi : prog.getD p .nop <;> simp_all [flagWriter, ctlOk]) hh he,
      flagWriter_after D _ h]
  | m + 2, p, o, s, h, hpc, hh, hsp, hwf, he => by
    simp only [prefixOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, hwf'⟩, hrest⟩ := h
    rw [x86_run_succ rodata prog (m + 1) s hh, hpc] at he
    rw [x86_run_succ rodata prog (m + 1) s hh, x86_run_succ rodata prog (m + 1) _ (by rw [ovr_halted]; exact hh),
      ovr_pc, hpc]
    have he1 : (exec rodata (prog.getD p .nop) s).err = false := by
      cases hc : (exec rodata (prog.getD p .nop) s).err
      · rfl
      · have := x86_run_err rodata prog (m + 1) _ hc
        rw [this] at he; exact absurd he (by decide)
    obtain ⟨h1, h2, h3, h4⟩ := prefix_step rodata D c _ s o hi hh hsp hwf hwf' he1
    rw [h1]
    exact run_ovr_prefix rodata prog D c (m + 1) (p + 1) _ _ hrest (by rw [h3, hpc]) h2 h4 hwf' he

/-! ## Normalised entry states -/

/-- The control part of a fresh call: flags clear, masks zero, `vl = 0`. -/
def ctl0 : Ctl := ⟨false, false, false, false, Vector.replicate 8 0, 0⟩

/-- The state with the control components of a fresh call (the kernels' proofs start here). -/
def normCtl (s : State α) : State α := ovr Dom.all ctl0 s

@[simp] theorem normCtl_zf (s : State α) : (normCtl s).zf = false := rfl
@[simp] theorem normCtl_cf (s : State α) : (normCtl s).cf = false := rfl
@[simp] theorem normCtl_nf (s : State α) : (normCtl s).nf = false := rfl
@[simp] theorem normCtl_vf (s : State α) : (normCtl s).vf = false := rfl
@[simp] theorem normCtl_vl (s : State α) : (normCtl s).vl = 0 := rfl
theorem normCtl_k (s : State α) : (normCtl s).k = Vector.replicate 8 0 := by
  apply Vector.ext; intro i hi
  simp only [normCtl, ovr, Dom.all, ctl0, Vector.getElem_ofFn]
  have : [0, 1, 2, 3, 4, 5, 6, 7].contains i = true := by
    simp only [List.contains_iff_mem]; simp; omega
  rw [this]; rfl

/-- Any state is its normalised state with its own control components put back. -/
theorem ovr_normCtl (s : State α) : ovr Dom.all (Ctl.of s) (normCtl s) = s := by
  cases s
  simp only [normCtl, ovr, Dom.all, Ctl.of, cond_true, State.mk.injEq, and_true, true_and]
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  have : [0, 1, 2, 3, 4, 5, 6, 7].contains i = true := by
    simp only [List.contains_iff_mem]; simp; omega
  rw [this]; rfl

theorem normCtl_pc (s : State α) (p : Nat) : normCtl { s with pc := p } = { normCtl s with pc := p } := rfl

theorem x86_run_err_add (rodata : Array (BitVec 64)) (prog : Array Instr) (a b : Nat) (s : State α)
    (h : (X86.isa.run rodata prog (a + b) s).err = false) : (X86.isa.run rodata prog a s).err = false := by
  rw [Isa.run_add] at h
  cases hc : (X86.isa.run rodata prog a s).err
  · rfl
  · rw [x86_run_err rodata prog b _ hc] at h; exact absurd h (by decide)

/-- **A kernel run from any control state.** If the program begins (at `p = s.pc`, `rsp` a stack
pointer at offset `o`) with a prefix that writes the flags before reading them (`prefixOk`) and
no instruction touches the other control components (`static`), then every run from `s` is the
run from the normalised state with the leftover components (masks, `nf`/`vf`, `vl`) put back. -/
theorem run_normCtl (rodata : Array (BitVec 64)) (prog : Array Instr) (m : Nat) (o : Int) (n : Nat)
    (s : State (BitVec 64))
    (hpre : prefixOk prog s.pc o m = true)
    (hstatic : (prog.all fun i => ctlOk { Dom.all with zf := false, cf := false } i &&
      ctlAfter { Dom.all with zf := false, cf := false } i == { Dom.all with zf := false, cf := false }) = true)
    (hm : m ≤ n) (hh : s.halted = false) (hsp : s.getGD 4 = gprWord ⟨rStack, o⟩) (hwf : 0 ≤ o ∧ o < 2 ^ 55)
    (he : (X86.isa.run rodata prog n (normCtl s)).err = false) :
    X86.isa.run rodata prog n s =
      ovr { Dom.all with zf := false, cf := false } (Ctl.of s) (X86.isa.run rodata prog n (normCtl s)) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = m + r := ⟨n - m, by omega⟩
  conv => lhs; rw [← ovr_normCtl s]
  rw [Isa.run_add, Isa.run_add]
  rw [run_ovr_prefix rodata prog Dom.all (Ctl.of s) m s.pc o (normCtl s) hpre rfl hh hsp hwf
    (x86_run_err_add rodata prog m r _ he)]
  rw [Isa.run_add] at he
  exact run_ovr_static rodata prog _ (Ctl.of s) hstatic r _ he

end Keccaktree.Asm.X86
