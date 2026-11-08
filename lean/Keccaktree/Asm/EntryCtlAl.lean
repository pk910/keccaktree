import Keccaktree.Asm.AliasTrace
import Keccaktree.Asm.EntryCtl
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Control state left by a tail call, on the aliased x86 machine

`EntryCtl.lean` shows that a kernel's run does not depend on the flags, mask registers and vector
length a previous kernel left behind, until the program overwrites them.  The same holds on the
aliased machine (`X86.isaAl`, one buffer for input and output): an aliased step is the ordinary
step on the joined view, with the stored output words copied into the buffer; which cells are
stored (`writes`) does not depend on the control components (`writes_ovr`), so

* `execAl_ovr`: `execAl i (ovr D c t) = ovr (ctlAfter D i) c (execAl i t)` (from `exec_ovr`),
* `run_ovr_static_al`, `run_ovr_prefix_al`, `run_normCtl_al`: the run lemmas of `EntryCtl.lean`
  for `X86.isaAl`.

`LibAlias.mkKernelAl` uses `run_normCtl_al` to enter an in-place kernel from any control state.
-/
namespace Keccaktree.Asm.X86

variable {α : Type} [LaneOps α]

theorem writes_ovr (D : Dom) (c : Ctl) (s : State α) (i : Instr) : writes (ovr D c s) i = writes s i := by
  cases i <;> simp only [writes, memAddr_ovr, gx_ovr, getV_ovr]

theorem joined_ovr (D : Dom) (c : Ctl) (t : State α) :
    ({ ovr D c t with mem := joinMem (ovr D c t).mem } : State α) = ovr D c { t with mem := joinMem t.mem } := rfl

/-- An aliased step commutes with an override when the ordinary step on the joined view does. -/
theorem execAl_ovr_of (rodata : Array (BitVec 64)) (D D' : Dom) (c : Ctl) (i : Instr) (t : State α)
    (hh : t.halted = false)
    (h : exec rodata i (ovr D c ({ t with mem := joinMem t.mem } : State α)) =
      ovr D' c (exec rodata i ({ t with mem := joinMem t.mem } : State α))) :
    execAl rodata i (ovr D c t) = ovr D' c (execAl rodata i t) := by
  have hh' : (ovr D c t).halted = false := hh
  rw [execAl_eq rodata i _ hh', execAl_eq rodata i t hh, joined_ovr, h]
  have hm : mirror (ovr D c ({ t with mem := joinMem t.mem } : State α))
      (ovr D' c (exec rodata i ({ t with mem := joinMem t.mem } : State α))) i =
      mirror ({ t with mem := joinMem t.mem } : State α) (exec rodata i ({ t with mem := joinMem t.mem } : State α)) i := by
    funext r q; simp only [mirror, writes_ovr, ovr_mem]
  rw [hm]; rfl

theorem execAl_err (rodata : Array (BitVec 64)) (i : Instr) (t : State α) (hh : t.halted = false) :
    (execAl rodata i t).err = (exec rodata i ({ t with mem := joinMem t.mem } : State α)).err := by
  rw [execAl_eq rodata i t hh]

/-- **One aliased step from an overridden state** (`exec_ovr` on the aliased machine). -/
theorem execAl_ovr (rodata : Array (BitVec 64)) (D : Dom) (c : Ctl) (i : Instr) (t : State α)
    (hok : ctlOk D i = true) (hh : t.halted = false) (he : (execAl rodata i t).err = false) :
    execAl rodata i (ovr D c t) = ovr (ctlAfter D i) c (execAl rodata i t) :=
  execAl_ovr_of rodata D _ c i t hh
    (exec_ovr rodata D c i _ hok hh (by rw [execAl_err rodata i t hh] at he; exact he))

/-! ## Runs of the aliased machine -/

theorem al_run_err (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (s : State α), s.err = true → (isaAl.run rodata prog n s).err = true
  | 0, s, h => h
  | n + 1, s, h => by
    simp only [Isa.run]
    split
    · exact h
    · exact al_run_err rodata prog n _ (err_execAl rodata _ s h)

theorem al_run_succ (rodata : Array (BitVec 64)) (prog : Array Instr) (n : Nat) (t : State α) (h : t.halted = false) :
    isaAl.run rodata prog (n + 1) t = isaAl.run rodata prog n (execAl rodata (prog.getD t.pc .nop) t) := by
  show (if t.halted then t else _) = _
  rw [h]; rfl

theorem al_run_err_add (rodata : Array (BitVec 64)) (prog : Array Instr) (a b : Nat) (s : State α)
    (h : (isaAl.run rodata prog (a + b) s).err = false) : (isaAl.run rodata prog a s).err = false := by
  rw [Isa.run_add] at h
  cases hc : (isaAl.run rodata prog a s).err
  · rfl
  · rw [al_run_err rodata prog b _ hc] at h; exact absurd h (by decide)

theorem al_err_first (rodata : Array (BitVec 64)) (prog : Array Instr) (n : Nat) (t : State α) (i : Instr)
    (he : (isaAl.run rodata prog n (execAl rodata i t)).err = false) : (execAl rodata i t).err = false := by
  cases hc : (execAl rodata i t).err
  · rfl
  · rw [al_run_err rodata prog n _ hc] at he; exact absurd he (by decide)

/-- **No instruction of the program touches the dirty components**: every aliased run commutes with
the override (`run_ovr_static` on the aliased machine). -/
theorem run_ovr_static_al (rodata : Array (BitVec 64)) (prog : Array Instr) (D : Dom) (c : Ctl)
    (hprog : (prog.all fun i => ctlOk D i && ctlAfter D i == D) = true) :
    ∀ (n : Nat) (s : State α), (isaAl.run rodata prog n s).err = false →
      isaAl.run rodata prog n (ovr D c s) = ovr D c (isaAl.run rodata prog n s)
  | 0, s, _ => rfl
  | n + 1, s, he => by
    cases hh : s.halted
    · rw [al_run_succ rodata prog n s hh] at he
      rw [al_run_succ rodata prog n s hh, al_run_succ rodata prog n _ (by rw [ovr_halted]; exact hh), ovr_pc]
      have hi : ctlOk D (prog.getD s.pc .nop) = true ∧ ctlAfter D (prog.getD s.pc .nop) = D := by
        simp only [Array.getD]
        split
        · rename_i hlt
          have := (Array.all_eq_true.mp hprog) s.pc hlt
          simp only [Bool.and_eq_true, beq_iff_eq] at this
          exact this
        · exact ⟨rfl, rfl⟩
      have he1 := al_err_first rodata prog n s _ he
      rw [execAl_ovr rodata D c _ s hi.1 hh he1, hi.2]
      exact run_ovr_static_al rodata prog D c hprog n _ he
    · rw [Isa.run_halted _ _ _ _ _ (by rw [ovr_halted]; exact hh), Isa.run_halted _ _ _ _ _ hh]

/-- A frame set-up step on the aliased machine (`prefix_step`). -/
theorem prefix_step_al (rodata : Array (BitVec 64)) (D : Dom) (c : Ctl) (i : Instr) (t : State (BitVec 64)) (o : Int)
    (hi : prefixInstrOk i = true) (hh : t.halted = false) (hsp : t.getGD 4 = gprWord ⟨rStack, o⟩)
    (hwf : 0 ≤ o ∧ o < 2 ^ 55) (hwf' : 0 ≤ prefixRsp i o ∧ prefixRsp i o < 2 ^ 55)
    (he : (execAl rodata i t).err = false) :
    execAl rodata i (ovr D c t) = ovr D c (execAl rodata i t) ∧ (execAl rodata i t).halted = false ∧
      (execAl rodata i t).pc = t.pc + 1 ∧ (execAl rodata i t).getGD 4 = gprWord ⟨rStack, prefixRsp i o⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := prefix_step rodata D c i ({ t with mem := joinMem t.mem } : State (BitVec 64)) o hi hh hsp
    hwf hwf' (by rw [execAl_err rodata i t hh] at he; exact he)
  refine ⟨execAl_ovr_of rodata D D c i t hh h1, ?_, ?_, ?_⟩
  · rw [execAl_eq rodata i t hh]; exact h2
  · rw [execAl_eq rodata i t hh]; exact h3
  · rw [execAl_eq rodata i t hh]; exact h4

/-- **The entry prefix on the aliased machine** (`run_ovr_prefix`). -/
theorem run_ovr_prefix_al (rodata : Array (BitVec 64)) (prog : Array Instr) (D : Dom) (c : Ctl) :
    ∀ (m p : Nat) (o : Int) (s : State (BitVec 64)), prefixOk prog p o m = true → s.pc = p → s.halted = false →
    s.getGD 4 = gprWord ⟨rStack, o⟩ → 0 ≤ o ∧ o < 2 ^ 55 → (isaAl.run rodata prog m s).err = false →
    isaAl.run rodata prog m (ovr D c s) = ovr { D with zf := false, cf := false } c (isaAl.run rodata prog m s)
  | 0, p, o, s, h, _, _, _, _, _ => by simp [prefixOk] at h
  | 1, p, o, s, h, hpc, hh, hsp, hwf, he => by
    simp only [prefixOk] at h
    rw [al_run_succ rodata prog 0 s hh, hpc] at he
    rw [al_run_succ rodata prog 0 s hh, al_run_succ rodata prog 0 _ (by rw [ovr_halted]; exact hh), ovr_pc, hpc]
    show execAl rodata (prog.getD p .nop) (ovr D c s) = ovr _ c (execAl rodata (prog.getD p .nop) s)
    rw [execAl_ovr rodata D c _ s (by cases hi : prog.getD p .nop <;> simp_all [flagWriter, ctlOk]) hh he,
      flagWriter_after D _ h]
  | m + 2, p, o, s, h, hpc, hh, hsp, hwf, he => by
    simp only [prefixOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, hwf'⟩, hrest⟩ := h
    rw [al_run_succ rodata prog (m + 1) s hh, hpc] at he
    rw [al_run_succ rodata prog (m + 1) s hh, al_run_succ rodata prog (m + 1) _ (by rw [ovr_halted]; exact hh),
      ovr_pc, hpc]
    have he1 := al_err_first rodata prog (m + 1) s _ he
    obtain ⟨h1, h2, h3, h4⟩ := prefix_step_al rodata D c _ s o hi hh hsp hwf hwf' he1
    rw [h1]
    exact run_ovr_prefix_al rodata prog D c (m + 1) (p + 1) _ _ hrest (by rw [h3, hpc]) h2 h4 hwf' he

/-- **An aliased kernel run from any control state** (`run_normCtl` on the aliased machine): with a
flag-writing entry prefix and no other instruction touching the control components, the run from
`s` is the run from the normalised state with the leftover components put back. -/
theorem run_normCtl_al (rodata : Array (BitVec 64)) (prog : Array Instr) (m : Nat) (o : Int) (n : Nat)
    (s : State (BitVec 64))
    (hpre : prefixOk prog s.pc o m = true)
    (hstatic : (prog.all fun i => ctlOk { Dom.all with zf := false, cf := false } i &&
      ctlAfter { Dom.all with zf := false, cf := false } i == { Dom.all with zf := false, cf := false }) = true)
    (hm : m ≤ n) (hh : s.halted = false) (hsp : s.getGD 4 = gprWord ⟨rStack, o⟩) (hwf : 0 ≤ o ∧ o < 2 ^ 55)
    (he : (isaAl.run rodata prog n (normCtl s)).err = false) :
    isaAl.run rodata prog n s =
      ovr { Dom.all with zf := false, cf := false } (Ctl.of s) (isaAl.run rodata prog n (normCtl s)) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = m + r := ⟨n - m, by omega⟩
  conv => lhs; rw [← ovr_normCtl s]
  rw [Isa.run_add, Isa.run_add]
  rw [run_ovr_prefix_al rodata prog Dom.all (Ctl.of s) m s.pc o (normCtl s) hpre rfl hh hsp hwf
    (al_run_err_add rodata prog m r _ he)]
  rw [Isa.run_add] at he
  exact run_ovr_static_al rodata prog _ (Ctl.of s) hstatic r _ he

/-! ## Overrides and the views of the aliased machine -/

theorem normCtl_ovr (D : Dom) (c : Ctl) (X : State α) : normCtl (ovr D c X) = normCtl X := by
  simp only [normCtl, ovr, Dom.all, Bool.cond_true, State.mk.injEq, and_true, true_and]
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  have : [0, 1, 2, 3, 4, 5, 6, 7].contains i = true := by
    simp only [List.contains_iff_mem]; simp; omega
  rw [this]; rfl

theorem dupState_ovr (D : Dom) (c : Ctl) (X : State α) : dupState (ovr D c X) = ovr D c (dupState X) := rfl

theorem dupState_normCtl (X : State α) : dupState (normCtl X) = normCtl (dupState X) := rfl

end Keccaktree.Asm.X86
