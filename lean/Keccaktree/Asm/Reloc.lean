import Keccaktree.Asm.Compose
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Relocation of symbolic runs

A batch of a kernel reads its nodes through the input pointer and writes the
digests through the output pointer; the next batch is the same instruction
trace with both pointers advanced.  A *relocation* `ρ` shifts the offsets of
the pointers into a region by a constant (`δ r`, a multiple of 8, zero for
the stack, the constants and plain numbers) and the memory words of that
region accordingly.  On symbolic states the pointers are `E.ptr` leaves and
the memory words `E.var (memVar r q)` leaves, so a relocation is a leaf
substitution (`E.reloc`, `relocState`), and `exec` commutes with it
(`exec_reloc`): the symbolic run of a batch, proved once at offset 0, is the
symbolic run of every batch.

The semantics draw from an address only its region and offset (`asAddr`), so
the proof is the combinator proof of `Hom.lean` again, with one side
condition: the relocated addresses an instruction decodes must still be
representable (`Addr.wf`, offsets below `2^55`).  `decodedAddrs` lists the
addresses a step decodes; `traceAddrsBelow` checks them along a (closed)
symbolic trace, so a single kernel-checked bound covers every relocation up to
the remaining headroom.
-/
namespace Keccaktree.Asm
open X86

structure Reloc where
  δ : Region → Int

namespace Reloc

/-- A relocation moves input/output regions only, by multiples of 8 bytes, forwards. -/
def ok (ρ : Reloc) : Prop :=
  ρ.δ 0 = 0 ∧ ρ.δ rStack = 0 ∧ ρ.δ rRodata = 0 ∧ ∀ r, 0 ≤ ρ.δ r ∧ (8 : Int) ∣ ρ.δ r

def addr (ρ : Reloc) (a : Addr) : Addr := ⟨a.region, a.off + ρ.δ a.region⟩

/-- The shift of the word indices of a region. -/
def wshift (ρ : Reloc) (r : Region) : Int := ρ.δ r / 8

/-- The cut variable a cut variable moves to: memory words of a shifted region. -/
def var (ρ : Reloc) (i : Nat) : Nat :=
  if i < 288 then i else memVar (memVarRegion i) (memVarIndex i + ρ.wshift (memVarRegion i))

@[simp] theorem addr_region (ρ : Reloc) (a : Addr) : (ρ.addr a).region = a.region := rfl

theorem δ_eq (ρ : Reloc) (h : ρ.ok) (r : Region) : ρ.δ r = 8 * ρ.wshift r := by
  obtain ⟨k, hk⟩ := (h.2.2.2 r).2
  simp only [wshift, hk, Int.mul_ediv_cancel_left _ (by decide : (8 : Int) ≠ 0)]

theorem addr_num (ρ : Reloc) (h : ρ.ok) (n : Int) : ρ.addr (Addr.num n) = Addr.num n := by
  simp [addr, Addr.num, h.1]

theorem addr_region0 (ρ : Reloc) (h : ρ.ok) (a : Addr) (ha : a.region = 0) : ρ.addr a = a := by
  rcases a with ⟨r, o⟩; simp only at ha; subst ha; simp [addr, h.1]

theorem addr_stack (ρ : Reloc) (h : ρ.ok) (a : Addr) (ha : a.region = rStack) : ρ.addr a = a := by
  rcases a with ⟨r, o⟩; simp only at ha; subst ha; simp [addr, h.2.1]

theorem addr_rodata (ρ : Reloc) (h : ρ.ok) (a : Addr) (ha : a.region = rRodata) : ρ.addr a = a := by
  rcases a with ⟨r, o⟩; simp only at ha; subst ha; simp [addr, h.2.2.1]

theorem addr_add (ρ : Reloc) (a : Addr) (n : Int) :
    ρ.addr ⟨a.region, a.off + n⟩ = ⟨a.region, (ρ.addr a).off + n⟩ := by
  simp only [addr, Addr.mk.injEq, true_and]; omega

theorem addr_mod8 (ρ : Reloc) (h : ρ.ok) (a : Addr) : (ρ.addr a).off % 8 = a.off % 8 := by
  simp only [addr, ρ.δ_eq h a.region]; omega

theorem addr_div8 (ρ : Reloc) (h : ρ.ok) (a : Addr) : (ρ.addr a).off / 8 = a.off / 8 + ρ.wshift a.region := by
  simp only [addr, ρ.δ_eq h a.region]; omega

theorem var_memVar (ρ : Reloc) (r : Region) (q : Int) :
    ρ.var (memVar r q) = memVar r (q + ρ.wshift r) := by
  have := memVar_ge r q
  simp only [var, show ¬ memVar r q < 288 by omega, ↓reduceIte, memVarRegion_memVar, memVarIndex_memVar]

theorem var_lt (ρ : Reloc) (i : Nat) (h : i < 288) : ρ.var i = i := by simp [var, h]

end Reloc

/-- Relocate the leaves of an expression. -/
def E.reloc (ρ : Reloc) : E → E
  | .var i => .var (ρ.var i)
  | .const v => .const v
  | .ptr a => .ptr (ρ.addr a)
  | .xor a b => .xor (a.reloc ρ) (b.reloc ρ)
  | .and a b => .and (a.reloc ρ) (b.reloc ρ)
  | .or a b => .or (a.reloc ρ) (b.reloc ρ)
  | .not a => .not (a.reloc ρ)
  | .shl a n => .shl (a.reloc ρ) n
  | .shr a n => .shr (a.reloc ρ) n
  | .rol a n => .rol (a.reloc ρ) n
  | .add a b => .add (a.reloc ρ) (b.reloc ρ)
  | .ternlog imm a b c => .ternlog imm (a.reloc ρ) (b.reloc ρ) (c.reloc ρ)

/-- The addresses decoded while decoding an expression: the address of every
sub-expression that has one (pointer leaves, intermediate pointer sums). -/
def E.addrs (e : E) : List Addr :=
  (e.addrP).toList ++ match e with
    | .xor a b | .and a b | .or a b | .add a b => a.addrs ++ b.addrs
    | .not a | .shl a _ | .shr a _ | .rol a _ => a.addrs
    | .ternlog _ a b c => a.addrs ++ b.addrs ++ c.addrs
    | _ => []

theorem E.addrP_mem (e : E) (a : Addr) (h : e.addrP = some a) : a ∈ e.addrs := by
  cases e <;> simp [E.addrs, h]

/-- Every decoded address of an expression stays representable under `ρ`. -/
def E.relocOk (ρ : Reloc) (e : E) : Prop := ∀ p ∈ e.addrs, (ρ.addr p).wf

section E
variable (ρ : Reloc) (hρ : ρ.ok)
include hρ

theorem E.closed_reloc (e : E) : (e.reloc ρ).closed = e.closed := by
  induction e with
  | ptr a =>
    simp only [E.reloc, E.closed, Reloc.addr_region]
    split
    · rename_i h; simp [Reloc.addr, h, hρ.1]
    · rename_i h; simp [h]
  | _ => simp_all [E.reloc, E.closed]

theorem ofInt_add_δ_low3 (o : Int) (r : Region) : BitVec.ofInt 64 (o + ρ.δ r) &&& 7#64 = BitVec.ofInt 64 o &&& 7#64 := by
  rw [ρ.δ_eq hρ r, BitVec.ofInt_add, BitVec.ofInt_mul]
  generalize BitVec.ofInt 64 o = x
  generalize BitVec.ofInt 64 (ρ.wshift r) = k
  have : BitVec.ofInt 64 8 = 8#64 := rfl
  rw [this]
  bv_decide

/-- `low3` of a relocated expression agrees on the low 3 bits. -/
theorem E.low3_reloc (e : E) :
    (e.low3 = none → (e.reloc ρ).low3 = none) ∧
    (∀ l, e.low3 = some l → ∃ l', (e.reloc ρ).low3 = some l' ∧ l' &&& 7#64 = l &&& 7#64) := by
  induction e with
  | var i => simp [E.low3, E.reloc]
  | const v => simp [E.low3, E.reloc]
  | ptr a =>
    simp only [E.low3, E.reloc, Reloc.addr, reduceCtorEq, false_implies, Option.some.injEq, true_and]
    intro l hl; subst hl
    exact ⟨_, rfl, ofInt_add_δ_low3 ρ hρ a.off a.region⟩
  | xor a b iha ihb =>
    constructor
    · intro h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [iha.1 ha]
      · rcases hb : b.low3 with _ | y
        · simp [ihb.1 hb]
        · simp [ha, hb] at h
    · intro l h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [ha] at h
      · rcases hb : b.low3 with _ | y
        · simp [ha, hb] at h
        · simp only [ha, hb, Option.some.injEq] at h; subst h
          obtain ⟨x', hx', hx⟩ := iha.2 x ha; obtain ⟨y', hy', hy⟩ := ihb.2 y hb
          refine ⟨x' ^^^ y', by simp [hx', hy'], ?_⟩; bv_decide
  | and a b iha ihb =>
    constructor
    · intro h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [iha.1 ha]
      · rcases hb : b.low3 with _ | y
        · simp [ihb.1 hb]
        · simp [ha, hb] at h
    · intro l h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [ha] at h
      · rcases hb : b.low3 with _ | y
        · simp [ha, hb] at h
        · simp only [ha, hb, Option.some.injEq] at h; subst h
          obtain ⟨x', hx', hx⟩ := iha.2 x ha; obtain ⟨y', hy', hy⟩ := ihb.2 y hb
          refine ⟨x' &&& y', by simp [hx', hy'], ?_⟩; bv_decide
  | or a b iha ihb =>
    constructor
    · intro h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [iha.1 ha]
      · rcases hb : b.low3 with _ | y
        · simp [ihb.1 hb]
        · simp [ha, hb] at h
    · intro l h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [ha] at h
      · rcases hb : b.low3 with _ | y
        · simp [ha, hb] at h
        · simp only [ha, hb, Option.some.injEq] at h; subst h
          obtain ⟨x', hx', hx⟩ := iha.2 x ha; obtain ⟨y', hy', hy⟩ := ihb.2 y hb
          refine ⟨x' ||| y', by simp [hx', hy'], ?_⟩; bv_decide
  | add a b iha ihb =>
    constructor
    · intro h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [iha.1 ha]
      · rcases hb : b.low3 with _ | y
        · simp [ihb.1 hb]
        · simp [ha, hb] at h
    · intro l h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [ha] at h
      · rcases hb : b.low3 with _ | y
        · simp [ha, hb] at h
        · simp only [ha, hb, Option.some.injEq] at h; subst h
          obtain ⟨x', hx', hx⟩ := iha.2 x ha; obtain ⟨y', hy', hy⟩ := ihb.2 y hb
          refine ⟨x' + y', by simp [hx', hy'], ?_⟩; bv_decide
  | not a iha =>
    constructor
    · intro h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [iha.1 ha]
      · simp [ha] at h
    · intro l h; simp only [E.low3, E.reloc] at h ⊢
      rcases ha : a.low3 with _ | x
      · simp [ha] at h
      · simp only [ha, Option.some.injEq] at h; subst h
        obtain ⟨x', hx', hx⟩ := iha.2 x ha
        refine ⟨~~~x', by simp [hx'], ?_⟩; bv_decide
  | shl a n iha => simp [E.low3, E.reloc]
  | shr a n iha => simp [E.low3, E.reloc]
  | rol a n iha => simp [E.low3, E.reloc]
  | ternlog imm a b c => simp [E.low3, E.reloc]

theorem addrPlus_reloc (p : Addr) (y : BitVec 64) (r : Addr) (h : addrPlus p y = some r)
    (hp : (ρ.addr p).wf) (hr : (ρ.addr r).wf) : addrPlus (ρ.addr p) y = some (ρ.addr r) := by
  obtain ⟨hr0, hpwf, rfl⟩ := addrPlus_eq p y r h
  simp only [addrPlus, Reloc.addr_region, hr0, hp, ne_eq, not_false_eq_true, true_and]
  simp only [Reloc.addr] at hr ⊢
  have e : p.off + y.toInt + ρ.δ p.region = p.off + ρ.δ p.region + y.toInt := by omega
  simp only [e] at hr
  simp only [hr, ↓reduceIte, Option.some.injEq, Addr.mk.injEq, true_and]
  omega

theorem E.addrP_reloc (e : E) (a : Addr) (h : e.addrP = some a) (hok : e.relocOk ρ) :
    (e.reloc ρ).addrP = some (ρ.addr a) := by
  induction e generalizing a with
  | ptr p =>
    simp only [E.addrP, E.reloc] at h ⊢
    split at h
    · simp only [Option.some.injEq] at h; subst h
      have := hok p (E.addrP_mem _ p (by simp [E.addrP, ‹p.wf›])); simp [this]
    · simp at h
  | add x y ihx ihy =>
    have hx' := E.closed_reloc ρ hρ x; have hy' := E.closed_reloc ρ hρ y
    have hra : (ρ.addr a).wf := hok a (E.addrP_mem _ a h)
    simp only [E.addrP, E.reloc, hx', hy'] at h ⊢
    split at h
    · rename_i hxc hyc
      obtain ⟨p, hp, hpl⟩ := Option.bind_eq_some_iff.mp h
      have hokx : x.relocOk ρ := fun q hq => hok q (by simp [E.addrs, hq])
      have hpr : (ρ.addr p).wf := hokx p (E.addrP_mem x p hp)
      simp only [hxc, hyc, ihx p hp hokx, Option.bind_some, addrPlus_reloc ρ hρ p _ a hpl hpr hra]
    · rename_i hxc hyc
      obtain ⟨p, hp, hpl⟩ := Option.bind_eq_some_iff.mp h
      have hoky : y.relocOk ρ := fun q hq => hok q (by simp [E.addrs, hq])
      have hpr : (ρ.addr p).wf := hoky p (E.addrP_mem y p hp)
      simp only [hxc, hyc, ihy p hp hoky, Option.bind_some, addrPlus_reloc ρ hρ p _ a hpl hpr hra]
    · simp at h
  | and x y ihx ihy =>
    cases y with
    | const m =>
      simp only [E.addrP, E.reloc] at h ⊢
      split at h
      · rename_i hm
        rcases hl : x.low3 with _ | l
        · simp [hl] at h
        · simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
          obtain ⟨l', hl', hll⟩ := (E.low3_reloc ρ hρ x).2 l hl
          simp only [hm, ↓reduceIte, hl', Option.map_some, Option.some.injEq, Reloc.addr_num ρ hρ]
          have : l' &&& m = l &&& m := by bv_decide
          rw [this]
      · simp at h
    | _ => simp [E.addrP] at h
  | _ => simp [E.addrP] at h

theorem E.addr_reloc (e : E) (a : Addr) (h : e.addr = some a) (hok : e.relocOk ρ) :
    (e.reloc ρ).addr = some (ρ.addr a) := by
  simp only [E.addr, E.closed_reloc ρ hρ] at h ⊢
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rename_i hr
      rw [Reloc.addr_region0 ρ hρ _ (wordGpr_region_num _ hr.1)]
      simp [hr]
    · simp at h
  · exact E.addrP_reloc ρ hρ e a h hok

end E


namespace X86
open LaneOps

/-- Relocate a symbolic state: every lane, and the memory words of the shifted regions. -/
def relocState (ρ : Reloc) (s : State E) : State E :=
  { v := s.v.map (·.map (E.reloc ρ)), g := s.g, gd := s.gd.map (E.reloc ρ), k := s.k,
    zf := s.zf, cf := s.cf, nf := s.nf, vf := s.vf, vl := s.vl,
    mem := fun r q => E.reloc ρ (s.mem r (q - ρ.wshift r)),
    pc := s.pc, depth := s.depth, err := s.err, halted := s.halted, tail := s.tail }

section State
variable (ρ : Reloc) (hρ : ρ.ok)

@[simp] theorem reloc_const (v : BitVec 64) : E.reloc ρ (const v) = const v := rfl
@[simp] theorem reloc_ptr (a : Addr) : E.reloc ρ (ptr a) = ptr (ρ.addr a) := rfl
@[simp] theorem reloc_xor (a b : E) : E.reloc ρ (xor a b) = xor (E.reloc ρ a) (E.reloc ρ b) := rfl
@[simp] theorem reloc_and (a b : E) : E.reloc ρ (and a b) = and (E.reloc ρ a) (E.reloc ρ b) := rfl
@[simp] theorem reloc_or (a b : E) : E.reloc ρ (or a b) = or (E.reloc ρ a) (E.reloc ρ b) := rfl
@[simp] theorem reloc_not (a : E) : E.reloc ρ (not a) = not (E.reloc ρ a) := rfl
@[simp] theorem reloc_shl (a : E) (n : Nat) : E.reloc ρ (shl a n) = shl (E.reloc ρ a) n := rfl
@[simp] theorem reloc_shr (a : E) (n : Nat) : E.reloc ρ (shr a n) = shr (E.reloc ρ a) n := rfl
@[simp] theorem reloc_rol (a : E) (n : Nat) : E.reloc ρ (rol a n) = rol (E.reloc ρ a) n := rfl
@[simp] theorem reloc_add (a b : E) : E.reloc ρ (add a b) = add (E.reloc ρ a) (E.reloc ρ b) := rfl
@[simp] theorem reloc_ternlog (imm : Nat) (a b c : E) :
    E.reloc ρ (ternlog imm a b c) = ternlog imm (E.reloc ρ a) (E.reloc ρ b) (E.reloc ρ c) := rfl

include hρ in
theorem reloc_asConst (e : E) : asConst (E.reloc ρ e) = asConst e := E.closed_reloc ρ hρ e

include hρ in
theorem reloc_asAddr (e : E) (a : Addr) (h : asAddr e = some a) (hok : e.relocOk ρ) :
    asAddr (E.reloc ρ e) = some (ρ.addr a) := E.addr_reloc ρ hρ e a h hok

@[simp] theorem halted_reloc (s : State E) : (relocState ρ s).halted = s.halted := rfl
@[simp] theorem err_reloc (s : State E) : (relocState ρ s).err = s.err := rfl
@[simp] theorem pc_reloc (s : State E) : (relocState ρ s).pc = s.pc := rfl
@[simp] theorem depth_reloc (s : State E) : (relocState ρ s).depth = s.depth := rfl
@[simp] theorem k_reloc (s : State E) : (relocState ρ s).k = s.k := rfl
@[simp] theorem zf_reloc (s : State E) : (relocState ρ s).zf = s.zf := rfl
@[simp] theorem cf_reloc (s : State E) : (relocState ρ s).cf = s.cf := rfl
@[simp] theorem fail_reloc (s : State E) : (relocState ρ s).fail = relocState ρ s.fail := rfl
theorem next_reloc (s : State E) : next (relocState ρ s) = relocState ρ (next s) := rfl
theorem reloc_upd_pc (s : State E) (p : Nat) : relocState ρ { s with pc := p } = { relocState ρ s with pc := p } := rfl
theorem reloc_upd_pc_depth (s : State E) (p d : Nat) :
    relocState ρ { s with pc := p, depth := d } = { relocState ρ s with pc := p, depth := d } := rfl
theorem reloc_upd_zf (s : State E) (z : Bool) : relocState ρ { s with zf := z } = { relocState ρ s with zf := z } := rfl
theorem reloc_upd_cf (s : State E) (c : Bool) : relocState ρ { s with cf := c } = { relocState ρ s with cf := c } := rfl
theorem reloc_upd_zf_cf (s : State E) (z c : Bool) :
    relocState ρ { s with zf := z, cf := c } = { relocState ρ s with zf := z, cf := c } := rfl
theorem reloc_upd_halted (s : State E) : relocState ρ { s with halted := true } = { relocState ρ s with halted := true } := rfl
theorem reloc_upd_tail (s : State E) (n : String) :
    relocState ρ { s with halted := true, tail := some n } = { relocState ρ s with halted := true, tail := some n } := rfl
theorem reloc_upd_k (s : State E) (k : Vector Nat 8) : relocState ρ { s with k := k } = { relocState ρ s with k := k } := rfl

theorem getV_reloc (s : State E) (n : Nat) : (relocState ρ s).getV n = (s.getV n).map (E.reloc ρ) := by
  simp only [State.getV, relocState, Vector.getD]
  rcases h : s.v[n]? with _ | v <;> simp [h, Vector.toList_map]

theorem getGD_reloc (s : State E) (n : Nat) : (relocState ρ s).getGD n = E.reloc ρ (s.getGD n) := by
  simp only [State.getGD, relocState, Vector.getD]
  rcases h : s.gd[n]? with _ | v <;> simp [h]

theorem setGD_reloc (s : State E) (n : Nat) (x : E) : (relocState ρ s).setGD n (E.reloc ρ x) = relocState ρ (s.setGD n x) := by
  simp [State.setGD, relocState, Vector.map_setIfInBounds]

theorem setGD_reloc' (s : State E) (n : Nat) (x x' : E) (hx : E.reloc ρ x = x') :
    (relocState ρ s).setGD n x' = relocState ρ (s.setGD n x) := by
  subst hx; exact setGD_reloc ρ s n x

theorem setX_reloc (s : State E) (n : Nat) (a : Addr) : setX (relocState ρ s) n (ρ.addr a) = relocState ρ (setX s n a) := by
  simp only [setX]; exact setGD_reloc' ρ s n _ _ rfl

theorem getD_reloc (l : List E) (i : Nat) : (l.map (E.reloc ρ)).getD i (const 0) = E.reloc ρ (l.getD i (const 0)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem headD_reloc (l : List E) : (l.map (E.reloc ρ)).headD (const 0) = E.reloc ρ (l.headD (const 0)) := by
  cases l <;> simp

theorem optGetD_reloc (o : Option E) : (o.map (E.reloc ρ)).getD (const 0) = E.reloc ρ (o.getD (const 0)) := by
  rcases o with _ | x <;> simp

theorem getElem?_reloc_getD (l : List E) (i : Nat) :
    (l.map (E.reloc ρ))[i]?.getD (const 0) = E.reloc ρ (l[i]?.getD (const 0)) := by
  rw [List.getElem?_map]; exact optGetD_reloc ρ _

theorem writeV_reloc (s : State E) (n lanes : Nat) (vs : List E) :
    writeV (relocState ρ s) n lanes (vs.map (E.reloc ρ)) = relocState ρ (writeV s n lanes vs) := by
  simp only [writeV, State.setV, relocState, Vector.map_setIfInBounds]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  split
  · simp [List.getD_eq_getElem?_getD]; cases vs[i]? <;> simp
  · simp

theorem writeV_reloc' (s : State E) (n lanes : Nat) (vs : List E) (vs' : List E) (h : vs' = vs.map (E.reloc ρ)) :
    writeV (relocState ρ s) n lanes vs' = relocState ρ (writeV s n lanes vs) := by
  subst h; exact writeV_reloc ρ s n lanes vs

include hρ in
theorem gx_reloc (s : State E) (n : Nat) (a : Addr) (h : gx s n = some a) (hok : (s.getGD n).relocOk ρ) :
    gx (relocState ρ s) n = some (ρ.addr a) := by
  simp only [gx, getGD_reloc] at h ⊢
  exact reloc_asAddr ρ hρ _ a h hok

include hρ in
theorem memAddr?_reloc (s : State E) (m : MemOp) (a : Addr) (h : memAddr? s m = some a)
    (hok : ∀ g disp, m = .base g disp → (s.getGD g).relocOk ρ) :
    memAddr? (relocState ρ s) m = some (ρ.addr a) := by
  cases m with
  | base g disp =>
    simp only [memAddr?] at h ⊢
    rcases hx : gx s g with _ | x
    · simp [hx] at h
    · rw [gx_reloc ρ hρ _ _ _ hx (hok g disp rfl)]
      simp only [hx, Option.map_some, Option.some.injEq] at h ⊢
      rw [← h, Reloc.addr_add]
      rfl
  | rip off =>
    simp only [memAddr?, Option.some.injEq] at h ⊢
    rw [← h, Reloc.addr_rodata ρ hρ _ rfl]

include hρ in
theorem read_reloc (rodata : Array (BitVec 64)) (s : State E) (r : Region) (q : Int) :
    (relocState ρ s).read rodata r (q + ρ.wshift r) = E.reloc ρ (s.read rodata r q) := by
  simp only [State.read]
  split
  · rename_i hr; subst hr
    have : ρ.wshift rRodata = 0 := by simp [Reloc.wshift, hρ.2.2.1]
    rw [this, Int.add_zero]; split <;> simp
  · simp only [relocState, Int.add_sub_cancel]

include hρ in
theorem loadWords_reloc (rodata : Array (BitVec 64)) (s : State E) (a : Addr) (n : Nat) :
    (relocState ρ s).loadWords rodata (ρ.addr a) n = (s.loadWords rodata a n).map (List.map (E.reloc ρ)) := by
  simp only [State.loadWords, Reloc.addr_mod8 ρ hρ, Reloc.addr_region, Reloc.addr_div8 ρ hρ]
  split
  · simp only [Option.map_some, Option.some.injEq, List.map_map]
    apply List.map_congr_left; intro i _
    simp only [Function.comp_def]
    rw [show a.off / 8 + ρ.wshift a.region + Int.ofNat i = (a.off / 8 + Int.ofNat i) + ρ.wshift a.region by omega]
    exact read_reloc ρ hρ rodata s a.region _
  · rfl

theorem memStore_reloc (m : Region → Int → E) (r : Region) (q : Int) (v : E) :
    memStore (fun r' q' => E.reloc ρ (m r' (q' - ρ.wshift r'))) r (q + ρ.wshift r) (E.reloc ρ v) =
      fun r' q' => E.reloc ρ (memStore m r q v r' (q' - ρ.wshift r')) := by
  funext r' q'; simp only [memStore]
  by_cases hr : r' = r
  · simp only [hr, true_and]
    by_cases hq : q' = q + ρ.wshift r
    · simp [hq]
    · have : ¬ (q' - ρ.wshift r = q) := by omega
      simp [hq, this]
  · simp [hr]

theorem memStoreFrom_reloc (m : Region → Int → E) (r : Region) (q : Int) (vs : List E) :
    memStoreFrom (fun r' q' => E.reloc ρ (m r' (q' - ρ.wshift r'))) r (q + ρ.wshift r) (vs.map (E.reloc ρ)) =
      fun r' q' => E.reloc ρ (memStoreFrom m r q vs r' (q' - ρ.wshift r')) := by
  induction vs generalizing m q with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, memStoreFrom, memStore_reloc]
    rw [show q + ρ.wshift r + 1 = (q + 1) + ρ.wshift r by omega]
    exact ih (memStore m r q v) (q + 1)

include hρ in
theorem storeWords_reloc (s : State E) (a : Addr) (vs : List E) :
    (relocState ρ s).storeWords (ρ.addr a) (vs.map (E.reloc ρ)) = (s.storeWords a vs).map (relocState ρ) := by
  simp only [State.storeWords, Reloc.addr_mod8 ρ hρ, Reloc.addr_region, Reloc.addr_div8 ρ hρ]
  split
  · simp only [Option.map_some, relocState, memStoreFrom_reloc]
  · rfl

theorem storeWords_err' (st s' : State E) (a : Addr) (vs : List E) (h : st.storeWords a vs = some s') : s'.err = st.err :=
  storeWords_err st s' a vs h

include hρ in
theorem readSrc_reloc_some (rodata : Array (BitVec 64)) (s : State E) (lanes : Nat) (src : Src) (bs : List E)
    (h : readSrc rodata s lanes src = some bs) (hok : ∀ m g disp, (src = .mem m ∨ src = .bcst m) → m = .base g disp → (s.getGD g).relocOk ρ) :
    readSrc rodata (relocState ρ s) lanes src = some (bs.map (E.reloc ρ)) := by
  cases src with
  | reg n => simp only [readSrc, Option.some.injEq] at h ⊢; rw [getV_reloc, ← List.map_take, h]
  | mem m =>
    simp only [readSrc] at h ⊢
    rcases ha : memAddr? s m with _ | a
    · simp [ha] at h
    · rw [memAddr?_reloc ρ hρ _ _ _ ha (fun g disp hm => hok m g disp (Or.inl rfl) hm)]
      simp only [ha, Option.bind_some] at h ⊢
      rw [loadWords_reloc ρ hρ, h]; rfl
  | bcst m =>
    simp only [readSrc] at h ⊢
    rcases ha : memAddr? s m with _ | a
    · simp [ha] at h
    · rw [memAddr?_reloc ρ hρ _ _ _ ha (fun g disp hm => hok m g disp (Or.inr rfl) hm)]
      simp only [ha, Option.bind_some] at h ⊢
      rw [loadWords_reloc ρ hρ]
      rcases hl : s.loadWords rodata a 1 with _ | l
      · simp [hl] at h
      · simp only [hl, Option.map_some, Option.some.injEq] at h ⊢
        rw [← h]; cases l <;> simp [List.map_replicate]

theorem setFlagsSub_reloc (s : State E) (a b : Addr) :
    setFlagsSub (relocState ρ s) (ρ.addr a) (ρ.addr b) = relocState ρ (setFlagsSub s a b) := by
  simp only [setFlagsSub, Reloc.addr_region]
  by_cases hr : a.region = b.region
  · simp only [hr, ↓reduceIte, Reloc.addr]
    have h1 : (a.off + ρ.δ b.region = b.off + ρ.δ b.region) = (a.off = b.off) := by
      apply propext; omega
    have h2 : (a.off + ρ.δ b.region < b.off + ρ.δ b.region) = (a.off < b.off) := by
      apply propext; omega
    simp only [h1, h2]; rfl
  · simp only [hr, ↓reduceIte]; rfl

/-! ## The combinators -/

include hρ in
theorem withX_reloc (s : State E) (n : Nat) (k k' : Addr → State E)
    (hne : (withX s n k).err = false) (hok : (s.getGD n).relocOk ρ)
    (hk : ∀ a, gx s n = some a → (k a).err = false → k' (ρ.addr a) = relocState ρ (k a)) :
    withX (relocState ρ s) n k' = relocState ρ (withX s n k) := by
  simp only [withX] at hne ⊢
  rcases hx : gx s n with _ | a
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [gx_reloc ρ hρ _ _ _ hx hok, hk a hx hne]

include hρ in
theorem withMem_reloc (s : State E) (m : MemOp) (k k' : Addr → State E)
    (hne : (withMem s m k).err = false) (hok : ∀ g disp, m = .base g disp → (s.getGD g).relocOk ρ)
    (hk : ∀ a, memAddr? s m = some a → (k a).err = false → k' (ρ.addr a) = relocState ρ (k a)) :
    withMem (relocState ρ s) m k' = relocState ρ (withMem s m k) := by
  simp only [withMem] at hne ⊢
  rcases hx : memAddr? s m with _ | a
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [memAddr?_reloc ρ hρ _ _ _ hx hok, hk a hx hne]

include hρ in
theorem withSrc_reloc (rodata : Array (BitVec 64)) (s : State E) (lanes : Nat) (b : Src)
    (k k' : List E → State E)
    (hne : (withSrc rodata s lanes b k).err = false)
    (hok : ∀ m g disp, (b = .mem m ∨ b = .bcst m) → m = .base g disp → (s.getGD g).relocOk ρ)
    (hk : ∀ bs, readSrc rodata s lanes b = some bs → (k bs).err = false → k' (bs.map (E.reloc ρ)) = relocState ρ (k bs)) :
    withSrc rodata (relocState ρ s) lanes b k' = relocState ρ (withSrc rodata s lanes b k) := by
  simp only [withSrc] at hne ⊢
  rcases hx : readSrc rodata s lanes b with _ | bs
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [readSrc_reloc_some ρ hρ _ _ _ _ _ hx hok, hk bs hx hne]

include hρ in
theorem withLoad_reloc (rodata : Array (BitVec 64)) (s : State E) (a : Addr) (n : Nat)
    (k k' : List E → State E)
    (hne : (withLoad rodata s a n k).err = false)
    (hk : ∀ ws, s.loadWords rodata a n = some ws → (k ws).err = false → k' (ws.map (E.reloc ρ)) = relocState ρ (k ws)) :
    withLoad rodata (relocState ρ s) (ρ.addr a) n k' = relocState ρ (withLoad rodata s a n k) := by
  simp only [withLoad, loadWords_reloc ρ hρ] at hne ⊢
  rcases hx : s.loadWords rodata a n with _ | ws
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [Option.map_some, hk ws hx hne]

include hρ in
theorem withStore_reloc (s : State E) (a : Addr) (vs vs' : List E) (hv : vs' = vs.map (E.reloc ρ))
    (k k' : State E → State E)
    (hne : (withStore s a vs k).err = false)
    (hk : ∀ s', s.storeWords a vs = some s' → (k s').err = false → k' (relocState ρ s') = relocState ρ (k s')) :
    withStore (relocState ρ s) (ρ.addr a) vs' k' = relocState ρ (withStore s a vs k) := by
  subst hv
  simp only [withStore, storeWords_reloc ρ hρ] at hne ⊢
  rcases hx : s.storeWords a vs with _ | s'
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [Option.map_some, hk s' hx hne]

include hρ in
theorem readG_reloc (rodata : Array (BitVec 64)) (s : State E) (b : GSrc) (k k' : E → State E)
    (hne : (readG rodata s b k).err = false)
    (hok : ∀ m g disp, b = .mem m → m = .base g disp → (s.getGD g).relocOk ρ)
    (hk : ∀ y, (k y).err = false → k' (E.reloc ρ y) = relocState ρ (k y)) :
    readG rodata (relocState ρ s) b k' = relocState ρ (readG rodata s b k) := by
  cases b with
  | reg g => simp only [readG, getGD_reloc] at hne ⊢; exact hk _ hne
  | imm i => simp only [readG] at hne ⊢; rw [← reloc_const ρ]; exact hk _ hne
  | mem m =>
    simp only [readG] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok m g disp rfl hm)
    intro a _ hne2
    apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
    intro ws _ hne3
    rw [headD_reloc]; exact hk _ hne3

end State
end X86
end Keccaktree.Asm
