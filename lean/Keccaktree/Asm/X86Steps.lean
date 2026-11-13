import Keccaktree.Asm.Iter
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Concrete x86 steps on counts

The count-dependent instructions of a kernel's frame (the tests, compares and
decrements of the node count) run on concrete states whose count is any number:
they cannot be part of a symbolic slice (the count would have to be a control
constant).  These lemmas give their effect for every count value.
-/
namespace Keccaktree.Asm.X86
open Keccaktree.Asm

theorem ofInt_eq_zero_iff (c : Int) (h0 : 0 ≤ c) (h1 : c < 2 ^ 55) : BitVec.ofInt 64 c = (0 : BitVec 64) ↔ c = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, c = n := ⟨c.toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [BitVec.ofInt_natCast]
  constructor
  · intro h
    have h2 : (BitVec.ofNat 64 n).toNat = 0 := by rw [h]; rfl
    simp only [BitVec.toNat_ofNat] at h2
    have : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
    omega
  · intro h
    have : n = 0 := by omega
    subst this; rfl

theorem gx_of_word (S : State (BitVec 64)) (n : Nat) (a : Addr) (h : S.getGD n = gprWord a) (hwf : a.wf) :
    gx S n = some a := by
  simp only [gx, h]
  show some (wordGpr (gprWord a)) = some a
  rw [wordGpr_gprWord a hwf]

/-- `test r, r` on a register holding the number `c`. -/
theorem exec_test_num (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (n : Nat) (c : Int)
    (hh : S.halted = false) (h : S.getGD n = gprWord ⟨0, c⟩) (hwf : (⟨0, c⟩ : Addr).wf) :
    exec rodata (.test n n) S = next { S with zf := decide (c = 0), cf := false } := by
  have hg := gx_of_word S n ⟨0, c⟩ h hwf
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg, and_self]
  have := ofInt_eq_zero_iff c hwf.1 hwf.2
  simp only [BitVec.and_self, this]

theorem exec_jcc_eq (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (c : Cond) (t : Nat) (hh : S.halted = false) :
    exec rodata (.jcc c t) S = { S with pc := if condHolds S c then t else S.pc + 1 } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

/-- `dec qword ptr [base + d]` on a memory word holding the number `n`. -/
theorem exec_decm_num (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (b : Nat) (d : Int) (sp : Addr) (n : Int)
    (hh : S.halted = false) (hsp : gx S b = some sp) (hal : (sp.off + d) % 8 = 0) (hr : sp.region ≠ rRodata)
    (hv : S.mem sp.region ((sp.off + d) / 8) = gprWord ⟨0, n⟩) (hwf : (⟨0, n⟩ : Addr).wf) :
    exec rodata (.decm (.base b d)) S =
      next { S with mem := memStore S.mem sp.region ((sp.off + d) / 8) (gprWord ⟨0, n - 1⟩), zf := decide (n - 1 = 0) } := by
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withMem, memAddr?, hsp, Option.map_some, withLoad,
    State.loadWords, hal, List.range_one, List.map_cons, List.map_nil, State.read, hr, Int.ofNat_eq_natCast,
    Int.natCast_zero, Int.add_zero, hv, List.headD_cons]
  show (match some (wordGpr (gprWord ⟨0, n⟩)) with
    | some v => if v.region = 0 then withStore S _ [LaneOps.ptr ⟨v.region, v.off - 1⟩] (fun s' => next { s' with zf := decide (v.off - 1 = 0) }) else S.fail
    | none => S.fail) = _
  rw [wordGpr_gprWord _ hwf]
  simp only [↓reduceIte, withStore, State.storeWords, hal, ne_eq, hr, not_false_eq_true, and_self, memStoreFrom, hh]
  rfl

end Keccaktree.Asm.X86
