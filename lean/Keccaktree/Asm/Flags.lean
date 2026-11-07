import Keccaktree.Asm.Iter
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Flag-oblivious runs

A slice certificate fixes the whole control part of its start cut, the four condition flags
included.  Code that neither reads nor writes the flags (most of a kernel: the loop body, the
frame) runs the same from any flags: `SliceCert.step_flags` runs a certified slice from a state
whose flags are arbitrary, using the certificate at the state with the recorded flags.  Needed
where one cut is reached with different flags (an AArch64 loop head: entry vs. `subs` back edge;
a kernel entered by a tail call).
-/
namespace Keccaktree.Asm
open X86

/-- The state with the four condition flags replaced. -/
def X86.State.withFlags {α : Type} (s : State α) (z c n v : Bool) : State α :=
  { s with zf := z, cf := c, nf := n, vf := v }

theorem withFlags_withFlags {α : Type} (s : State α) (z c n v z' c' n' v' : Bool) :
    (s.withFlags z c n v).withFlags z' c' n' v' = s.withFlags z' c' n' v' := rfl

theorem withFlags_self {α : Type} (s : State α) : s.withFlags s.zf s.cf s.nf s.vf = s := rfl

/-- An instruction set whose `free` instructions neither read nor write the flags. -/
structure Isa.FlagObl (isa : Isa) where
  free : isa.Instr → Bool
  exec_flags : ∀ (rodata : Array (BitVec 64)) (i : isa.Instr) (s : State (BitVec 64)) (z c n v : Bool),
    free i = true → isa.exec rodata i (s.withFlags z c n v) = (isa.exec rodata i s).withFlags z c n v

/-- A concrete state follows the instruction indices `idx` (running, at the right `pc`). -/
def Isa.cpath (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) : List Nat → State (BitVec 64) → Prop
  | [], _ => True
  | i :: rest, s => s.halted = false ∧ s.pc = i ∧ isa.cpath rodata prog rest (isa.exec rodata (prog.getD i isa.nop) s)

theorem Isa.run_of_cpath (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (idx : List Nat)
    (s : State (BitVec 64)) (h : isa.cpath rodata prog idx s) :
    isa.run rodata prog idx.length s = isa.execTrace rodata (idx.map (prog.getD · isa.nop)) s := by
  induction idx generalizing s with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨hh, hpc, hr⟩ := h
    simp only [List.length_cons, List.map_cons, Isa.run, Isa.execTrace, List.foldl_cons, hh,
      Bool.false_eq_true, ↓reduceIte, hpc]
    exact ih _ hr

theorem Isa.cpath_of_pathOk (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (idx : List Nat)
    (env : Nat → BitVec 64) (t : State E) (h : isa.pathOk rodata prog idx t = true) :
    isa.cpath rodata prog idx (mapState (E.eval env) t) := by
  induction idx generalizing t with
  | nil => trivial
  | cons i rest ih =>
    simp only [Isa.pathOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨⟨⟨he, hh⟩, hpc⟩, hrest⟩ := h
    refine ⟨by simpa using hh, by simpa using hpc, ?_⟩
    rw [isa.exec_map _ (E.eval_isHom env) rodata _ t (isa.pathOk_err rodata prog rest _ hrest)]
    exact ih _ hrest

theorem Isa.cpath_flags (isa : Isa) (F : isa.FlagObl) (rodata : Array (BitVec 64)) (prog : Array isa.Instr)
    (idx : List Nat) (hfree : (idx.map (prog.getD · isa.nop)).all F.free = true)
    (s : State (BitVec 64)) (z c n v : Bool) (h : isa.cpath rodata prog idx s) :
    isa.cpath rodata prog idx (s.withFlags z c n v) ∧
      isa.execTrace rodata (idx.map (prog.getD · isa.nop)) (s.withFlags z c n v) =
        (isa.execTrace rodata (idx.map (prog.getD · isa.nop)) s).withFlags z c n v := by
  induction idx generalizing s with
  | nil => exact ⟨trivial, rfl⟩
  | cons i rest ih =>
    obtain ⟨hh, hpc, hr⟩ := h
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hfree
    have he := F.exec_flags rodata (prog.getD i isa.nop) s z c n v hfree.1
    obtain ⟨h1, h2⟩ := ih hfree.2 _ hr
    refine ⟨⟨hh, hpc, ?_⟩, ?_⟩
    · rw [he]; exact h1
    · simp only [List.map_cons, Isa.execTrace, List.foldl_cons] at h2 ⊢
      rw [he]; exact h2

namespace SliceCert
variable {isa : Isa} {R : isa.Relocatable} {rodata : Array (BitVec 64)} {prog : Array isa.Instr} {B : Int}
variable (C : SliceCert isa R rodata prog B)

/-- The concrete state at a relocated cut follows the slice's path. -/
theorem cpath_at (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S : State (BitVec 64))
    (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) (hs : Ok S) : isa.cpath rodata prog C.idx S := by
  have hok := C.dec_ok ρ hρ hw
  have hpath := pathOk_reloc R ρ hρ rodata prog C.idx C.cut C.path hok
  have hcp := isa.cpath_of_pathOk rodata prog C.idx (envOf S) _ hpath
  have he : mapState (E.eval (envOf S)) (relocState ρ C.cut) = S := by
    show mapState _ (relocState ρ (cutOf C.ctl C.sc)) = _
    rw [hc]; exact eval_cutOf C.ctl _ hs
  rw [he] at hcp
  exact hcp

/-- **A flag-free slice from any flags**: if the state with the recorded flags is at the relocated
cut, the state itself runs the slice, ending in the same state up to its own flags. -/
theorem step_flags (F : isa.FlagObl) (hfree : C.slice.all F.free = true) (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B)
    (S : State (BitVec 64)) (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl (S.withFlags C.sc.zf C.sc.cf C.sc.nf C.sc.vf))
    (hs : Ok S) :
    isa.run rodata prog C.idx.length S = isa.execTrace rodata C.slice S ∧
    isa.execTrace rodata C.slice S =
      (isa.execTrace rodata C.slice (S.withFlags C.sc.zf C.sc.cf C.sc.nf C.sc.vf)).withFlags S.zf S.cf S.nf S.vf := by
  have hok := C.dec_ok ρ hρ hw
  have hpath := pathOk_reloc R ρ hρ rodata prog C.idx C.cut C.path hok
  have hcp := isa.cpath_of_pathOk rodata prog C.idx (envOf (S.withFlags C.sc.zf C.sc.cf C.sc.nf C.sc.vf)) _ hpath
  have he : mapState (E.eval (envOf (S.withFlags C.sc.zf C.sc.cf C.sc.nf C.sc.vf))) (relocState ρ C.cut) =
      S.withFlags C.sc.zf C.sc.cf C.sc.nf C.sc.vf := by
    show mapState _ (relocState ρ (cutOf C.ctl C.sc)) = _
    rw [hc]; exact eval_cutOf C.ctl _ hs
  rw [he] at hcp
  obtain ⟨h1, h2⟩ := isa.cpath_flags F rodata prog C.idx hfree _ S.zf S.cf S.nf S.vf hcp
  rw [withFlags_withFlags, withFlags_self] at h1 h2
  exact ⟨isa.run_of_cpath rodata prog C.idx S h1, h2⟩

end SliceCert

/-- `cutOf` at a state with its flags replaced. -/
theorem cutOf_withFlags (ctl : List Nat) (S : State (BitVec 64)) (z c n v : Bool) :
    cutOf ctl (S.withFlags z c n v) = (cutOf ctl S).withFlags z c n v := rfl

theorem envOf_withFlags (S : State (BitVec 64)) (z c n v : Bool) (i : Nat) :
    envOf (S.withFlags z c n v) i = envOf S i := rfl

end Keccaktree.Asm
