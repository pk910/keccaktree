import Keccaktree.Asm.Hom
/-!
An instruction set, abstractly: the instruction type, its semantics on the
shared machine state (polymorphic in the lane type, so the same `exec` is the
concrete interpreter and the symbolic executor), and the two facts the
composition needs — `exec` commutes with lane homomorphisms on non-failing
steps, and a failed state stays failed.  `X86.isa`, `Arm.isa` and
`Riscv.isa` instantiate it; everything in `Compose`/`Final` is stated once,
for any `Isa`.
-/
namespace Keccaktree.Asm
open X86

structure Isa where
  Instr : Type
  nop : Instr
  exec : {α : Type} → [LaneOps α] → Array (BitVec 64) → Instr → State α → State α
  exec_map : ∀ {α β : Type} [LaneOps α] [LaneOps β] (f : α → β), IsHom f →
    ∀ (rodata : Array (BitVec 64)) (i : Instr) (st : State α), (exec rodata i st).err = false →
      exec rodata i (mapState f st) = mapState f (exec rodata i st)
  err_exec : ∀ {α : Type} [LaneOps α] (rodata : Array (BitVec 64)) (i : Instr) (st : State α),
    st.err = true → (exec rodata i st).err = true

variable {α β : Type} [LaneOps α] [LaneOps β]

/-- Run a list of instructions (a slice). -/
def Isa.execTrace (isa : Isa) (rodata : Array (BitVec 64)) (l : List isa.Instr) (s : State α) : State α :=
  l.foldl (fun s i => isa.exec rodata i s) s

theorem Isa.err_execTrace (isa : Isa) (rodata : Array (BitVec 64)) (l : List isa.Instr) (st : State α)
    (h : st.err = true) : (isa.execTrace rodata l st).err = true := by
  induction l generalizing st with
  | nil => exact h
  | cons i l ih => simp only [Isa.execTrace, List.foldl_cons]; exact ih _ (isa.err_exec rodata i st h)

theorem Isa.execTrace_map (isa : Isa) {f : α → β} (hf : IsHom f) (rodata : Array (BitVec 64))
    (l : List isa.Instr) (st : State α) (hne : (isa.execTrace rodata l st).err = false) :
    isa.execTrace rodata l (mapState f st) = mapState f (isa.execTrace rodata l st) := by
  induction l generalizing st with
  | nil => rfl
  | cons i l ih =>
    simp only [Isa.execTrace, List.foldl_cons] at hne ⊢
    have h1 : (isa.exec rodata i st).err = false := by
      cases hc : (isa.exec rodata i st).err
      · rfl
      · have := isa.err_execTrace rodata l _ hc
        simp only [Isa.execTrace] at this
        rw [this] at hne; exact absurd hne (by decide)
    rw [isa.exec_map f hf rodata i st h1]
    exact ih _ hne

/-- The fetch-execute loop: `n` steps, stopping when halted. -/
def Isa.run (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) : Nat → State α → State α
  | 0, s => s
  | n + 1, s => if s.halted then s else isa.run rodata prog n (isa.exec rodata (prog.getD s.pc isa.nop) s)

theorem Isa.run_halted (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (n : Nat) (s : State α)
    (h : s.halted = true) : isa.run rodata prog n s = s := by
  cases n with
  | zero => rfl
  | succ n => simp only [Isa.run, h, ↓reduceIte]

theorem Isa.run_add (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (n m : Nat) (s : State α) :
    isa.run rodata prog (n + m) s = isa.run rodata prog m (isa.run rodata prog n s) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add]; rfl
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [Isa.run]
    split
    · rw [isa.run_halted rodata prog m s ‹_›]
    · exact ih _

/-- The symbolic state follows the recorded instruction path `idx` without
failing or halting (a kernel-checkable Boolean). -/
def Isa.pathOk (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) : List Nat → State E → Bool
  | [], s => !s.err
  | i :: rest, s => !s.err && !s.halted && s.pc == i && isa.pathOk rodata prog rest (isa.exec rodata (prog.getD i isa.nop) s)

theorem Isa.pathOk_err (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (idx : List Nat) (s : State E)
    (h : isa.pathOk rodata prog idx s = true) : s.err = false := by
  cases idx <;> simp only [Isa.pathOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  · exact h
  · exact h.1.1.1

/-- A concrete state that evaluates a symbolic one follows the symbolic path:
`idx.length` steps of the fetch-execute loop are the trace of the path's
instructions. -/
theorem Isa.run_of_pathOk (isa : Isa) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (idx : List Nat)
    (env : Nat → BitVec 64) (t : State E) (h : isa.pathOk rodata prog idx t = true) :
    isa.run rodata prog idx.length (mapState (E.eval env) t) =
      isa.execTrace rodata (idx.map (prog.getD · isa.nop)) (mapState (E.eval env) t) := by
  induction idx generalizing t with
  | nil => rfl
  | cons i rest ih =>
    simp only [Isa.pathOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨⟨⟨he, hh⟩, hpc⟩, hrest⟩ := h
    simp only [List.length_cons, List.map_cons, Isa.run, Isa.execTrace, List.foldl_cons, halted_map, hh,
      Bool.false_eq_true, ↓reduceIte, pc_map, hpc]
    rw [isa.exec_map _ (E.eval_isHom env) rodata _ t (isa.pathOk_err rodata prog rest _ hrest)]
    exact ih _ hrest

/-- The x86-64 instruction set. -/
def X86.isa : Isa where
  Instr := X86.Instr
  nop := .nop
  exec := X86.exec
  exec_map := fun f hf rodata i st hne => X86.exec_map hf rodata i st hne
  err_exec := fun rodata i st h => X86.err_exec rodata i st h

theorem X86.isa_execTrace (rodata : Array (BitVec 64)) (l : List X86.Instr) (s : State α) :
    X86.isa.execTrace rodata l s = X86.execTrace rodata l s := rfl

end Keccaktree.Asm
