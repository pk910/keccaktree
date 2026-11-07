import Std.Tactic.BVDecide
import Keccaktree.Asm.X86
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
Generic lemmas about the machine model:

* `E.subst` / `E.eval` are lane-operation homomorphisms;
* `mapState` applies one to a whole state;
* evaluation after substitution is evaluation in the composed environment;
* the pointer encoding (`gprWord`/`wordGpr`) and the address decoding
  (`E.addr`) agree with evaluation.

The commutation of `exec` with `mapState` (the one lemma per instruction
that links the symbolic executor to the concrete one, and one cut to the
next) is in `Keccaktree.Asm.Hom`.
-/
namespace Keccaktree.Asm

def E.subst (σ : Nat → E) : E → E
  | .var i => σ i
  | .const v => .const v
  | .ptr a => .ptr a
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

/-! ## The pointer encoding -/

theorem ofInt_nonneg (o : Int) (h : 0 ≤ o) : BitVec.ofInt 64 o = BitVec.ofNat 64 o.toNat := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, o = n := ⟨o.toNat, (Int.toNat_of_nonneg h).symm⟩
  simp [BitVec.ofInt_natCast]

theorem ofNat_lt_ofNat {n m : Nat} (h : n < m) (hm : m < 2 ^ 64) : BitVec.ofNat 64 n < BitVec.ofNat 64 m := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt hm]
  exact h

/-- A number word (top byte zero) decodes and re-encodes to itself. -/
theorem gprWord_wordGpr_num (w : BitVec 64) (h : w >>> 56 = 0#64) : gprWord (wordGpr w) = w := by
  unfold gprWord wordGpr
  simp only [h, BitVec.toNat_ofNat, Nat.zero_mod, ↓reduceIte, Fin.isValue, BitVec.ofInt_toInt]

/-- The low 3 bits of a pointer's word are those of its offset. -/
theorem gprWord_low3 (a : Addr) : gprWord a &&& 7#64 = BitVec.ofInt 64 a.off &&& 7#64 := by
  unfold gprWord
  split
  · rfl
  · generalize BitVec.ofInt 64 a.off = x
    generalize BitVec.ofNat 64 a.region.val = r
    bv_decide

theorem wordGpr_gprWord (a : Addr) (h : a.wf) : wordGpr (gprWord a) = a := by
  rcases a with ⟨r, o⟩
  simp only [Addr.wf] at h
  obtain ⟨n, rfl⟩ : ∃ n : Nat, o = n := ⟨o.toNat, (Int.toNat_of_nonneg h.1).symm⟩
  have hn : n < 2 ^ 55 := by omega
  have hx : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := BitVec.ofInt_natCast 64 n
  have hxn : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt (by omega)
  have hxlt : BitVec.ofNat 64 n < 0x0080000000000000#64 := ofNat_lt_ofNat hn (by decide)
  unfold gprWord wordGpr
  simp only [hx]
  rcases r with ⟨r, hr⟩
  by_cases h0 : r = 0
  · subst h0
    simp only [Fin.isValue, ↓reduceIte]
    have h1 : (BitVec.ofNat 64 n >>> 56) = 0#64 := by generalize BitVec.ofNat 64 n = x at hxlt; bv_decide
    have h2 : (BitVec.ofNat 64 n).toInt = (n : Int) := by
      rw [BitVec.toInt_eq_toNat_cond, hxn]
      simp only [show 2 * n < 2 ^ 64 by omega, ↓reduceIte]
    simp [h1, h2]
  · have hne : (⟨r, hr⟩ : Fin 8) ≠ 0 := by simp [Fin.ext_iff, h0]
    simp only [hne, ↓reduceIte]
    have hr8 : BitVec.ofNat 64 r < 8#64 := ofNat_lt_ofNat hr (by decide)
    have h1 : (BitVec.ofNat 64 r <<< 56 + BitVec.ofNat 64 n) >>> 56 = BitVec.ofNat 64 r := by
      generalize BitVec.ofNat 64 n = x at hxlt; generalize BitVec.ofNat 64 r = y at hr8; bv_decide
    have h2 : (BitVec.ofNat 64 r <<< 56 + BitVec.ofNat 64 n) &&& 0x00ffffffffffffff#64 = BitVec.ofNat 64 n := by
      generalize BitVec.ofNat 64 n = x at hxlt; generalize BitVec.ofNat 64 r = y at hr8; bv_decide
    have hrn : (BitVec.ofNat 64 r).toNat = r := Nat.mod_eq_of_lt (by omega)
    simp only [h1, hrn, h0, ↓reduceIte, h2, hxn, Addr.mk.injEq, Fin.mk.injEq, Nat.mod_eq_of_lt hr, and_self]

/-- A word with a valid region tag is the encoding of its decoding. -/
theorem gprWord_wordGpr (w : BitVec 64) (h : (w >>> 56).toNat < 8) : gprWord (wordGpr w) = w := by
  unfold gprWord wordGpr
  simp only
  split
  · rename_i h0; simp only [Fin.isValue, ↓reduceIte, BitVec.ofInt_toInt]
  · rename_i h0
    have hm : (w >>> 56).toNat % 8 = (w >>> 56).toNat := Nat.mod_eq_of_lt h
    simp only [hm]
    have hne : (⟨(w >>> 56).toNat, h⟩ : Fin 8) ≠ 0 := fun hc => h0 (Fin.ext_iff.mp hc)
    simp only [hne, ↓reduceIte, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_decide

/-! ## Closed expressions -/

/-- `low3` is right about the low 3 bits. -/
theorem E.low3_eval (env : Nat → BitVec 64) (e : E) (l : BitVec 64) (h : e.low3 = some l) :
    e.eval env &&& 7#64 = l &&& 7#64 := by
  induction e generalizing l with
  | var i => simp [E.low3] at h
  | const c => simp [E.low3] at h; subst h; rfl
  | ptr a => simp [E.low3] at h; subst h; simp only [E.eval]; exact gprWord_low3 a
  | xor a b iha ihb =>
    simp only [E.low3] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp only [E.eval]
      have := iha _ ‹_›; have := ihb _ ‹_›; bv_decide
    · exact absurd h (by simp)
  | and a b iha ihb =>
    simp only [E.low3] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp only [E.eval]
      have := iha _ ‹_›; have := ihb _ ‹_›; bv_decide
    · exact absurd h (by simp)
  | or a b iha ihb =>
    simp only [E.low3] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp only [E.eval]
      have := iha _ ‹_›; have := ihb _ ‹_›; bv_decide
    · exact absurd h (by simp)
  | not a iha =>
    simp only [E.low3] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp only [E.eval]
      have := iha _ ‹_›; bv_decide
    · exact absurd h (by simp)
  | shl a n iha => simp [E.low3] at h
  | shr a n iha => simp [E.low3] at h
  | rol a n iha => simp [E.low3] at h
  | add a b iha ihb =>
    simp only [E.low3] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp only [E.eval]
      have := iha _ ‹_›; have := ihb _ ‹_›; bv_decide
    · exact absurd h (by simp)
  | ternlog imm a b c iha ihb ihc => simp [E.low3] at h

/-- A closed expression evaluates to its value under any environment. -/
theorem E.closed_eval (env : Nat → BitVec 64) (e : E) (v : BitVec 64) (h : e.closed = some v) :
    e.eval env = v := by
  induction e generalizing v with
  | var i => simp [E.closed] at h
  | const c => simp [E.closed] at h; simp [E.eval, h]
  | ptr a =>
    simp only [E.closed] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; simp only [E.eval, gprWord, ‹a.region = 0›, ↓reduceIte]
    · exact absurd h (by simp)
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

/-! ## Addresses -/

theorem addrPlus_wf (p : Addr) (y : BitVec 64) (r : Addr) (h : addrPlus p y = some r) : r.wf := by
  unfold addrPlus at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i hc; exact hc.2.2
  · exact absurd h (by simp)

theorem addrPlus_region (p : Addr) (y : BitVec 64) (r : Addr) (h : addrPlus p y = some r) : r.region = p.region := by
  unfold addrPlus at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem addrPlus_eq (p : Addr) (y : BitVec 64) (r : Addr) (h : addrPlus p y = some r) :
    p.region ≠ 0 ∧ p.wf ∧ r = ⟨p.region, p.off + y.toInt⟩ := by
  unfold addrPlus at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i hc; exact ⟨hc.1, hc.2.1, rfl⟩
  · exact absurd h (by simp)

/-- The word of a pointer plus a constant is the encoding of the sum (offsets wrap like the machine). -/
theorem addrPlus_gprWord (p : Addr) (y : BitVec 64) (r : Addr) (h : addrPlus p y = some r) :
    gprWord p + y = gprWord r := by
  obtain ⟨hr0, _, rfl⟩ := addrPlus_eq p y r h
  simp only [gprWord, hr0, ↓reduceIte, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc]

/-- A number word (top byte zero) decodes to a number. -/
theorem wordGpr_region_num (v : BitVec 64) (h : v >>> 56 = 0#64) : (wordGpr v).region = 0 := by
  simp [wordGpr, h]

theorem E.addrP_wf (e : E) (a : Addr) (h : e.addrP = some a) : a.wf := by
  induction e generalizing a with
  | ptr p => simp only [E.addrP] at h; split at h <;> simp_all
  | add x y ihx ihy =>
    simp only [E.addrP] at h
    split at h
    · obtain ⟨p, hp, hpl⟩ := Option.bind_eq_some_iff.mp h; exact addrPlus_wf _ _ _ hpl
    · obtain ⟨p, hp, hpl⟩ := Option.bind_eq_some_iff.mp h; exact addrPlus_wf _ _ _ hpl
    · simp at h
  | and x y ihx ihy =>
    cases y with
    | const m =>
      simp only [E.addrP] at h
      split at h
      · rcases hl : x.low3 with _ | l
        · simp [hl] at h
        · simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
          rename_i hm
          have h8 : (l &&& m) < 8#64 := by bv_decide
          have h9 : (l &&& m).toNat < 8 := by have := BitVec.lt_def.mp h8; simpa using this
          simp only [Addr.wf, Addr.num]; omega
      · simp at h
    | _ => simp [E.addrP] at h
  | _ => simp [E.addrP] at h

/-- An address an expression denotes is representable. -/
theorem E.addr_wf (e : E) (a : Addr) (h : e.addr = some a) : a.wf := by
  simp only [E.addr] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rename_i hr; exact hr.2
    · simp at h
  · exact E.addrP_wf e a h

theorem E.addrP_eval (env : Nat → BitVec 64) (e : E) (a : Addr) (h : e.addrP = some a) :
    e.eval env = gprWord a := by
  induction e generalizing a with
  | ptr p =>
    simp only [E.addrP] at h; split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  | add x y ihx ihy =>
    simp only [E.addrP] at h
    split at h
    · rename_i hx hy
      obtain ⟨p, hp, hpl⟩ := Option.bind_eq_some_iff.mp h
      simp only [E.eval, ihx p hp, E.closed_eval env y _ hy]
      exact addrPlus_gprWord p _ a hpl
    · rename_i hx hy
      obtain ⟨p, hp, hpl⟩ := Option.bind_eq_some_iff.mp h
      simp only [E.eval, ihy p hp, E.closed_eval env x _ hx]
      rw [BitVec.add_comm]
      exact addrPlus_gprWord p _ a hpl
    · simp at h
  | and x y ihx ihy =>
    cases y with
    | const m =>
      simp only [E.addrP] at h
      split at h
      · rcases hl : x.low3 with _ | l
        · simp [hl] at h
        · simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
          rename_i hm
          simp only [E.eval, gprWord, Addr.num, Fin.isValue, ↓reduceIte, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
            BitVec.setWidth_eq]
          have := E.low3_eval env x l hl
          bv_decide
      · simp at h
    | _ => simp [E.addrP] at h
  | _ => simp [E.addrP] at h

/-- An expression that denotes an address evaluates to its encoding. -/
theorem E.addr_eval (env : Nat → BitVec 64) (e : E) (a : Addr) (h : e.addr = some a) :
    e.eval env = gprWord a := by
  simp only [E.addr] at h
  split at h
  · rename_i hc; split at h
    · simp only [Option.some.injEq] at h; subst h; rename_i hr
      rw [E.closed_eval env _ _ hc]
      exact (gprWord_wordGpr_num _ hr.1).symm
    · simp at h
  · exact E.addrP_eval env e a h

/-! ## Variable-free expressions are fixed by substitution -/

def E.noVars : E → Bool
  | .var _ => false
  | .const _ => true
  | .ptr _ => true
  | .xor a b => a.noVars && b.noVars
  | .and a b => a.noVars && b.noVars
  | .or a b => a.noVars && b.noVars
  | .not a => a.noVars
  | .shl a _ => a.noVars
  | .shr a _ => a.noVars
  | .rol a _ => a.noVars
  | .add a b => a.noVars && b.noVars
  | .ternlog _ a b c => a.noVars && b.noVars && c.noVars

theorem E.subst_noVars (σ : Nat → E) (e : E) (h : e.noVars = true) : e.subst σ = e := by
  induction e <;> simp_all [E.noVars, E.subst]

theorem E.closed_noVars (e : E) (v : BitVec 64) (h : e.closed = some v) : e.noVars = true := by
  induction e generalizing v with
  | var i => simp [E.closed] at h
  | const c => rfl
  | ptr a => rfl
  | not a iha => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]
  | shl a n iha => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]
  | shr a n iha => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]
  | rol a n iha => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]
  | xor a b iha ihb => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]
  | and a b iha ihb => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]
  | or a b iha ihb => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]
  | add a b iha ihb => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]
  | ternlog imm a b c iha ihb ihc => simp only [E.closed] at h; split at h <;> simp_all [E.noVars]

theorem E.low3_noVars (e : E) (l : BitVec 64) (h : e.low3 = some l) : e.noVars = true := by
  induction e generalizing l with
  | var i => simp [E.low3] at h
  | const c => rfl
  | ptr a => rfl
  | not a iha => simp only [E.low3] at h; split at h <;> simp_all [E.noVars]
  | shl a n iha => simp [E.low3] at h
  | shr a n iha => simp [E.low3] at h
  | rol a n iha => simp [E.low3] at h
  | xor a b iha ihb => simp only [E.low3] at h; split at h <;> simp_all [E.noVars]
  | and a b iha ihb => simp only [E.low3] at h; split at h <;> simp_all [E.noVars]
  | or a b iha ihb => simp only [E.low3] at h; split at h <;> simp_all [E.noVars]
  | add a b iha ihb => simp only [E.low3] at h; split at h <;> simp_all [E.noVars]
  | ternlog imm a b c iha ihb ihc => simp [E.low3] at h

theorem E.addrP_noVars (e : E) (a : Addr) (h : e.addrP = some a) : e.noVars = true := by
  induction e generalizing a with
  | ptr p => rfl
  | add x y ihx ihy =>
    simp only [E.addrP] at h
    split at h
    · rename_i hx hy
      obtain ⟨p, hp, _⟩ := Option.bind_eq_some_iff.mp h
      simp [E.noVars, ihx p hp, E.closed_noVars _ _ hy]
    · rename_i hx hy
      obtain ⟨p, hp, _⟩ := Option.bind_eq_some_iff.mp h
      simp [E.noVars, ihy p hp, E.closed_noVars _ _ hx]
    · simp at h
  | and x y ihx ihy =>
    cases y with
    | const m =>
      simp only [E.addrP] at h
      split at h
      · rcases hl : x.low3 with _ | l
        · simp [hl] at h
        · simp [E.noVars, E.low3_noVars _ _ hl]
      · simp at h
    | _ => simp [E.addrP] at h
  | _ => simp [E.addrP] at h

theorem E.addr_noVars (e : E) (a : Addr) (h : e.addr = some a) : e.noVars = true := by
  simp only [E.addr] at h
  split at h
  · rename_i hc; exact E.closed_noVars _ _ hc
  · exact E.addrP_noVars e a h

/-- Substitution keeps closed expressions closed, with their value. -/
theorem E.closed_subst (σ : Nat → E) (e : E) (v : BitVec 64) (h : e.closed = some v) :
    (e.subst σ).closed = some v := by
  rw [E.subst_noVars σ e (E.closed_noVars e v h)]; exact h

/-- Substitution keeps denoted addresses. -/
theorem E.addr_subst (σ : Nat → E) (e : E) (a : Addr) (h : e.addr = some a) : (e.subst σ).addr = some a := by
  rw [E.subst_noVars σ e (E.addr_noVars e a h)]; exact h

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
