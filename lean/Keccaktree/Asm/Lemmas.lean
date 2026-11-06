import Keccaktree.Asm.X86
/-!
Generic lemmas about the machine model:

* `E.subst` / `E.eval` are lane-operation homomorphisms;
* `mapState` applies one to a whole state;
* evaluation after substitution is evaluation in the composed environment.

The commutation of `exec` with `mapState` (the one lemma per instruction
that links the symbolic executor to the concrete one, and one cut to the
next) is in `Keccaktree.Asm.Hom`.
-/
namespace Keccaktree.Asm

def E.subst (σ : Nat → E) : E → E
  | .var i => σ i
  | .const v => .const v
  | .xor a b => .xor (a.subst σ) (b.subst σ)
  | .and a b => .and (a.subst σ) (b.subst σ)
  | .or a b => .or (a.subst σ) (b.subst σ)
  | .not a => .not (a.subst σ)
  | .shl a n => .shl (a.subst σ) n
  | .shr a n => .shr (a.subst σ) n
  | .rol a n => .rol (a.subst σ) n
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .ternlog imm a b c => .ternlog imm (a.subst σ) (b.subst σ) (c.subst σ)

theorem E.eval_subst (env : Nat → BitVec 64) (σ : Nat → E) (e : E) :
    (e.subst σ).eval env = e.eval (fun i => (σ i).eval env) := by
  induction e <;> simp_all [E.subst, E.eval]

/-- A closed expression evaluates to its value under any environment. -/
theorem E.closed_eval (env : Nat → BitVec 64) (e : E) (v : BitVec 64) (h : e.closed = some v) :
    e.eval env = v := by
  induction e generalizing v with
  | var i => simp [E.closed] at h
  | const c => simp [E.closed] at h; simp [E.eval, h]
  | xor a b iha ihb =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›, ihb _ ‹_›]
    · exact absurd h (by simp)
  | and a b iha ihb =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›, ihb _ ‹_›]
    · exact absurd h (by simp)
  | or a b iha ihb =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›, ihb _ ‹_›]
    · exact absurd h (by simp)
  | add a b iha ihb =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›, ihb _ ‹_›]
    · exact absurd h (by simp)
  | not a iha =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›]
    · exact absurd h (by simp)
  | shl a n iha =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›]
    · exact absurd h (by simp)
  | shr a n iha =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›]
    · exact absurd h (by simp)
  | rol a n iha =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›]
    · exact absurd h (by simp)
  | ternlog imm a b c iha ihb ihc =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.eval, iha _ ‹_›, ihb _ ‹_›, ihc _ ‹_›]
    · exact absurd h (by simp)

/-- Substitution keeps closed expressions closed, with their value. -/
theorem E.closed_subst (σ : Nat → E) (e : E) (v : BitVec 64) (h : e.closed = some v) :
    (e.subst σ).closed = some v := by
  induction e generalizing v with
  | var i => simp [E.closed] at h
  | const c => simpa [E.closed, E.subst] using h
  | xor a b iha ihb =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›, ihb _ ‹_›]
    · exact absurd h (by simp)
  | and a b iha ihb =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›, ihb _ ‹_›]
    · exact absurd h (by simp)
  | or a b iha ihb =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›, ihb _ ‹_›]
    · exact absurd h (by simp)
  | add a b iha ihb =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›, ihb _ ‹_›]
    · exact absurd h (by simp)
  | not a iha =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›]
    · exact absurd h (by simp)
  | shl a n iha =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›]
    · exact absurd h (by simp)
  | shr a n iha =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›]
    · exact absurd h (by simp)
  | rol a n iha =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›]
    · exact absurd h (by simp)
  | ternlog imm a b c iha ihb ihc =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp [E.subst, E.closed, iha _ ‹_›, ihb _ ‹_›, ihc _ ‹_›]
    · exact absurd h (by simp)

namespace X86

/-- Apply a lane-value map to every lane of a state (registers and memory). -/
def mapState (f : α → β) (s : State α) : State β :=
  { v := s.v.map (·.map f), g := s.g, gd := s.gd.map f, k := s.k, zf := s.zf, cf := s.cf, nf := s.nf, vf := s.vf, vl := s.vl,
    mem := fun r q => f (s.mem r q), pc := s.pc, depth := s.depth, err := s.err,
    halted := s.halted, tail := s.tail }

theorem mapState_comp (f : α → β) (g : β → γ) (s : State α) :
    mapState g (mapState f s) = mapState (g ∘ f) s := by
  simp [mapState, Vector.map_map, Function.comp_def]

end X86
end Keccaktree.Asm
