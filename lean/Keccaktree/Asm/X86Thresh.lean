import Keccaktree.Asm.X86Kernel
import Keccaktree.Asm.Rodata
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Runtime thresholds: the kernels for every value of a `.data` word

avx2_x4 and avx2_x10 compare the remaining count with word 112 of their constant image (a
threshold the library calibrates at run time).  The generated segments are proved for the default
image; none of them loads word 112 (`pathW`, checked per slice), so each runs the same under every
image that differs only there (`SliceCert.run_agree`).  The policy compare itself is a count step
(`Fr.cmprm`) whose flags `setWord_flags` states for every value.
-/
namespace Keccaktree.Asm.X86K
open Keccaktree.Asm Keccaktree.Asm.X86

theorem agree_setWord (r : Array (BitVec 64)) (w v : Nat) : AgreeExcept r (setWord r w v) w := by
  intro q hq
  simp only [setWord, Array.set!]
  by_cases hs : q < r.size
  · simp [Array.getD, hs, Array.getElem_setIfInBounds, Ne.symm hq]
  · simp [Array.getD, hs]

/-- **A slice that never loads word `w` runs the same under an image differing only there**, at
every relocated position. -/
theorem SliceCert.run_agree {rodata r2 : Array (BitVec 64)} {prog : Array Instr} {B : Int} {w : Nat}
    (C : SliceCert X86.isa X86.isaReloc rodata prog B) (hr : AgreeExcept rodata r2 w)
    (hW : pathW rodata prog w C.idx (cutOf C.ctl C.sc) = true)
    (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S : State (BitVec 64))
    (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) (hs : SliceCert.Ok S) :
    X86.isa.run r2 prog C.idx.length S = X86.isa.run rodata prog C.idx.length S := by
  have hok := C.dec_ok ρ hρ hw
  have hW' := pathW_reloc ρ hρ rodata prog w C.idx (cutOf C.ctl C.sc) hW (fun e he => hok e he)
  have he : mapState (E.eval (envOf S)) (relocState ρ (cutOf C.ctl C.sc)) = S := by
    rw [hc]; exact eval_cutOf C.ctl S hs
  have := pathW_run hr prog C.idx _ hW' (envOf S)
  rw [he] at this
  exact this

/-- The flags of the policy compare `cmp r, [rip + 896]` against word 112 set to `v`. -/
theorem setWord_flags (rodata : Array (BitVec 64)) (r : Int) (v : Nat) (h0 : 0 ≤ r) (h1 : r < 2 ^ 55)
    (hv : v < 2 ^ 64) (hsz : 112 < rodata.size) :
    decide (BitVec.ofInt 64 r = (setWord rodata 112 v).getD (((896 : Nat) : Int) / 8).toNat 0#64) = decide (r = v) ∧
    decide ((BitVec.ofInt 64 r).toNat < ((setWord rodata 112 v).getD (((896 : Nat) : Int) / 8).toNat 0#64).toNat) =
      decide (r < v) := by
  have e112 : ((((896 : Nat) : Int) / 8).toNat) = 112 := by decide
  rw [e112, setWord_getD rodata 112 v hsz]
  obtain ⟨x, rfl⟩ : ∃ x : Nat, r = x := ⟨r.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hx64 : x < 2 ^ 64 := by omega
  rw [BitVec.ofInt_natCast]
  constructor
  · apply decide_eq_decide.mpr
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hv] at this; omega
    · intro h; have : x = v := by omega
      rw [this]
  · apply decide_eq_decide.mpr
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hv]; omega

end Keccaktree.Asm.X86K
