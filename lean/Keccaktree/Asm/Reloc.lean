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

theorem relocLane (ρ : Reloc) (hρ : ρ.ok) : IsLaneHom (E.reloc ρ) where
  const _ := rfl
  xor _ _ := rfl
  and _ _ := rfl
  or _ _ := rfl
  not _ := rfl
  shl _ _ := rfl
  shr _ _ := rfl
  rol _ _ := rfl
  add _ _ := rfl
  ternlog _ _ _ _ := rfl
  asConst a v h := by show (E.reloc ρ a).closed = some v; rw [E.closed_reloc ρ hρ]; exact h

theorem condHolds_reloc (s : State E) (c : Cond) : condHolds (relocState ρ s) c = condHolds s c := by cases c <;> rfl

include hρ in
theorem binop_reloc (rodata : Array (BitVec 64)) (s : State E) (lanes d a : Nat) (b : Src) (g g' : E → E → E)
    (hg : ∀ x y, g' (E.reloc ρ x) (E.reloc ρ y) = E.reloc ρ (g x y)) (hne : (binop rodata s lanes d a b g).err = false)
    (hok : ∀ m g disp, (b = .mem m ∨ b = .bcst m) → m = .base g disp → (s.getGD g).relocOk ρ) :
    binop rodata (relocState ρ s) lanes d a b g' = relocState ρ (binop rodata s lanes d a b g) := by
  simp only [binop]
  apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne hok
  intro bs _ _
  rw [← next_reloc]; apply congrArg next
  apply writeV_reloc' ρ
  rw [getV_reloc, ← List.map_take, zipWith_map_hom g g' hg]

theorem addr_mk_add (a : Addr) (n : Int) : (⟨(ρ.addr a).region, (ρ.addr a).off + n⟩ : Addr) = ρ.addr ⟨a.region, a.off + n⟩ := by
  simp only [Reloc.addr, Addr.mk.injEq, true_and]; omega

theorem addr_mk_sub (a : Addr) (n : Int) : (⟨(ρ.addr a).region, (ρ.addr a).off - n⟩ : Addr) = ρ.addr ⟨a.region, a.off - n⟩ := by
  simp only [Reloc.addr, Addr.mk.injEq, true_and]; omega

theorem addr_mk_sub' (a : Addr) (n : Int) : (⟨a.region, (ρ.addr a).off - n⟩ : Addr) = ρ.addr ⟨a.region, a.off - n⟩ := by
  simp only [Reloc.addr, Addr.mk.injEq, true_and]; omega

theorem setX_relocFix (s : State E) (n : Nat) (b : Addr) (hb : ρ.addr b = b) :
    setX (relocState ρ s) n b = relocState ρ (setX s n b) := by
  conv => lhs; rw [← hb]
  exact setX_reloc ρ s n b

include hρ in
theorem setFlagsSub_reloc0 (s : State E) (a b : Addr) (ha : a.region = 0) (hb : b.region = 0) :
    setFlagsSub (relocState ρ s) a b = relocState ρ (setFlagsSub s a b) := by
  conv => lhs; rw [← Reloc.addr_region0 ρ hρ a ha, ← Reloc.addr_region0 ρ hρ b hb]
  exact setFlagsSub_reloc ρ s a b

include hρ in
theorem setFlagsSub_reloc_num (s : State E) (a : Addr) (k : Int) :
    setFlagsSub (relocState ρ s) (ρ.addr a) (Addr.num k) = relocState ρ (setFlagsSub s a (Addr.num k)) := by
  rw [← setFlagsSub_reloc ρ s a (Addr.num k), Reloc.addr_num ρ hρ]

/-- The vector instructions after `withSrc`/no source: `next (writeV ..)` with the lanes
built from the lane operations. -/
syntax "x86_vec_reloc" : tactic
macro_rules
  | `(tactic| x86_vec_reloc) => `(tactic| (
      rw [← next_reloc]; apply congrArg next
      apply writeV_reloc' ρ
      simp only [getV_reloc, ← List.map_take, List.map_map, Function.comp_def, getD_reloc,
        getElem?_reloc_getD, optGetD_reloc, lane128_map (relocLane ρ hρ), List.map_append, List.map_cons, List.map_nil,
        reloc_const, reloc_xor, reloc_and, reloc_or, reloc_not, reloc_shl, reloc_shr, reloc_rol, reloc_add,
        reloc_ternlog, map_ite, foldr_cons2_map, foldr_append_map, shufb128_map' (relocLane ρ hρ)]
      try rfl))

theorem relocAddr_sub (a : Addr) (n : Int) : ρ.addr ⟨a.region, a.off - n⟩ = ⟨a.region, (ρ.addr a).off - n⟩ := by
  simp only [Reloc.addr, Addr.mk.injEq, true_and]; omega

set_option linter.deprecated false in
include hρ in
theorem repBody_reloc (rodata : Array (BitVec 64)) (st : State E) (n src dst : Addr)
    (hne : (repBody rodata st n src dst).err = false) :
    repBody rodata (relocState ρ st) (ρ.addr n) (ρ.addr src) (ρ.addr dst) = relocState ρ (repBody rodata st n src dst) := by
  unfold repBody at hne ⊢
  by_cases hc : n.region = 0 ∧ n.off % 8 = 0 ∧ n.off ≥ 0
  · rw [Reloc.addr_region0 ρ hρ n hc.1]
    rw [if_pos hc] at hne
    rw [if_pos hc, if_pos hc]
    exact withLoad_reloc ρ hρ _ _ _ _ _ _ hne fun vs _ hne5 =>
      withStore_reloc ρ hρ _ _ _ _ rfl _ _ hne5 fun s' _ _ => by
        rw [addr_mk_add, addr_mk_add, setX_relocFix ρ _ _ _ (Reloc.addr_num ρ hρ 0), setX_reloc, setX_reloc, next_reloc]
  · have hc' : ¬ ((ρ.addr n).region = 0 ∧ (ρ.addr n).off % 8 = 0 ∧ (ρ.addr n).off ≥ 0) := by
      intro h; rw [Reloc.addr_region0 ρ hρ n h.1] at h; exact hc h
    rw [if_neg hc] at hne
    rw [if_neg hc', if_neg hc]
    exact absurd hne (by simp only [fail_err]; decide)

include hρ in
theorem exec_reloc_vmov (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (dst : _) (src : _) (mask : _)
    (hne : (exec rodata (.vmov lanes dst src mask) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vmov lanes dst src mask) st, E.relocOk ρ e) :
    exec rodata (.vmov lanes dst src mask) (relocState ρ st) = relocState ρ (exec rodata (.vmov lanes dst src mask) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro vs _ _
    simp only [k_reloc]
    rw [← next_reloc ρ]; apply congrArg next
    apply writeV_reloc' ρ
    cases mask with
    | none => rfl
    | some k =>
      simp only [getV_reloc ρ, List.map_map, Function.comp_def, getD_reloc ρ, map_ite]
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vstore (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (dst : _) (src : _)
    (hne : (exec rodata (.vstore lanes dst src) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vstore lanes dst src) st, E.relocOk ρ e) :
    exec rodata (.vstore lanes dst src) (relocState ρ st) = relocState ρ (exec rodata (.vstore lanes dst src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro a _ hne2
    apply withStore_reloc ρ hρ _ _ _ _ (by rw [getV_reloc ρ, List.map_take]) _ _ hne2
    intro s' _ _; rfl
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpxor (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpxor lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpxor lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpxor lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpxor lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_reloc ρ hρ _ _ _ _ _ _ _ _ (fun x y => (reloc_xor ρ x y).symm) hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpand (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpand lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpand lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpand lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpand lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_reloc ρ hρ _ _ _ _ _ _ _ _ (fun x y => (reloc_and ρ x y).symm) hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpandn (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpandn lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpandn lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpandn lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpandn lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_reloc ρ hρ _ _ _ _ _ _ _ _ (fun x y => rfl) hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpor (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpor lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpor lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpor lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpor lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_reloc ρ hρ _ _ _ _ _ _ _ _ (fun x y => (reloc_or ρ x y).symm) hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpaddq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpaddq lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpaddq lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpaddq lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpaddq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_reloc ρ hρ _ _ _ _ _ _ _ _ (fun x y => (reloc_add ρ x y).symm) hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpsllq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vpsllq lanes d a imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpsllq lanes d a imm) st, E.relocOk ρ e) :
    exec rodata (.vpsllq lanes d a imm) (relocState ρ st) = relocState ρ (exec rodata (.vpsllq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; x86_vec_reloc
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpsrlq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vpsrlq lanes d a imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpsrlq lanes d a imm) st, E.relocOk ρ e) :
    exec rodata (.vpsrlq lanes d a imm) (relocState ρ st) = relocState ρ (exec rodata (.vpsrlq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; x86_vec_reloc
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vprolq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vprolq lanes d a imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vprolq lanes d a imm) st, E.relocOk ρ e) :
    exec rodata (.vprolq lanes d a imm) (relocState ρ st) = relocState ρ (exec rodata (.vprolq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; x86_vec_reloc
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpsllvq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpsllvq lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpsllvq lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpsllvq lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpsllvq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ hne2
    rcases hall : (bs.map LaneOps.asConst).all Option.isSome with _ | _
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [asConst_map_all (relocLane ρ hρ) bs hall, hall, ↓reduceIte]; x86_vec_reloc
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpsrlvq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpsrlvq lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpsrlvq lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpsrlvq lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpsrlvq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ hne2
    rcases hall : (bs.map LaneOps.asConst).all Option.isSome with _ | _
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [asConst_map_all (relocLane ρ hρ) bs hall, hall, ↓reduceIte]; x86_vec_reloc
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpternlogq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vpternlogq lanes d a b imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpternlogq lanes d a b imm) st, E.relocOk ρ e) :
    exec rodata (.vpternlogq lanes d a b imm) (relocState ρ st) = relocState ρ (exec rodata (.vpternlogq lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ _; x86_vec_reloc
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpshufb (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (ctrl : _)
    (hne : (exec rodata (.vpshufb lanes d a ctrl) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpshufb lanes d a ctrl) st, E.relocOk ρ e) :
    exec rodata (.vpshufb lanes d a ctrl) (relocState ρ st) = relocState ρ (exec rodata (.vpshufb lanes d a ctrl) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro cs _ hne2
    rcases hall : (cs.map LaneOps.asConst).all Option.isSome with _ | _
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [asConst_map_all (relocLane ρ hρ) cs hall, hall, ↓reduceIte]
      rw [← next_reloc ρ]; apply congrArg next
      apply writeV_reloc' ρ
      simp only [getV_reloc ρ, ← List.map_take, getD_reloc ρ, shufb128_map' (relocLane ρ hρ), foldr_cons2_map]
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpshufd (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vpshufd lanes d a imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpshufd lanes d a imm) st, E.relocOk ρ e) :
    exec rodata (.vpshufd lanes d a imm) (relocState ρ st) = relocState ρ (exec rodata (.vpshufd lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    have hl : ((List.range lanes).map fun i => (qwordSel imm (i % 2)).map fun q =>
        (((relocState ρ st).getV a).take lanes).getD (2 * (i / 2) + q) (LaneOps.const 0)) =
        ((List.range lanes).map fun i => (qwordSel imm (i % 2)).map fun q =>
        ((st.getV a).take lanes).getD (2 * (i / 2) + q) (LaneOps.const 0)).map (Option.map (E.reloc ρ)) := by
      simp only [List.map_map, Function.comp_def, Option.map_map, getV_reloc ρ, ← List.map_take, getD_reloc ρ]
    rw [hl, allSome_map (relocLane ρ hρ)]
    rcases hs : allSome ((List.range lanes).map fun i => (qwordSel imm (i % 2)).map fun q =>
        ((st.getV a).take lanes).getD (2 * (i / 2) + q) (LaneOps.const 0)) with _ | r
    · simp only [hs, fail_err] at hne; exact absurd hne (by decide)
    · simp only [Option.map_some, next_reloc ρ, writeV_reloc ρ]
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpblendd (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vpblendd lanes d a b imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpblendd lanes d a b imm) st, E.relocOk ρ e) :
    exec rodata (.vpblendd lanes d a b imm) (relocState ρ st) = relocState ρ (exec rodata (.vpblendd lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ hne2
    have hl : ((List.range lanes).map fun i =>
        if imm.testBit (2 * i) = imm.testBit (2 * i + 1) then
          some (if imm.testBit (2 * i) then (bs.map (E.reloc ρ)).getD i (LaneOps.const 0)
                else (((relocState ρ st).getV a).take lanes).getD i (LaneOps.const 0))
        else none) =
        ((List.range lanes).map fun i =>
        if imm.testBit (2 * i) = imm.testBit (2 * i + 1) then
          some (if imm.testBit (2 * i) then bs.getD i (LaneOps.const 0)
                else ((st.getV a).take lanes).getD i (LaneOps.const 0))
        else none).map (Option.map (E.reloc ρ)) := by
      simp only [List.map_map, Function.comp_def, getV_reloc ρ, ← List.map_take]
      apply List.map_congr_left; intro i _
      split
      · simp only [Option.map_some, map_ite, getD_reloc ρ]
      · rfl
    rw [hl, allSome_map (relocLane ρ hρ)]
    rcases hs : allSome ((List.range lanes).map fun i =>
        if imm.testBit (2 * i) = imm.testBit (2 * i + 1) then
          some (if imm.testBit (2 * i) then bs.getD i (LaneOps.const 0)
                else ((st.getV a).take lanes).getD i (LaneOps.const 0))
        else none) with _ | r
    · simp only [hs, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [Option.map_some, next_reloc ρ, writeV_reloc ρ]
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpalignr (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vpalignr lanes d a b imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpalignr lanes d a b imm) st, E.relocOk ρ e) :
    exec rodata (.vpalignr lanes d a b imm) (relocState ρ st) = relocState ρ (exec rodata (.vpalignr lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ hne2
    by_cases hc : imm % 8 = 0 ∧ imm ≤ 32
    · simp only [hc, and_self, ↓reduceIte] at hne2 ⊢
      rw [← next_reloc ρ]; apply congrArg next
      apply writeV_reloc' ρ
      rw [getV_reloc ρ, ← List.map_take]
      simp only [alignr_map (relocLane ρ hρ), getD_reloc ρ, foldr_cons2_map]
    · simp only [hc, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpunpcklqdq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpunpcklqdq lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpunpcklqdq lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpunpcklqdq lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpunpcklqdq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ _; x86_vec_reloc
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpunpckhqdq (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpunpckhqdq lanes d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpunpckhqdq lanes d a b) st, E.relocOk ρ e) :
    exec rodata (.vpunpckhqdq lanes d a b) (relocState ρ st) = relocState ρ (exec rodata (.vpunpckhqdq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ _; x86_vec_reloc
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vperm2i128 (rodata : Array (BitVec 64)) (st : State E) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vperm2i128 d a b imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vperm2i128 d a b imm) st, E.relocOk ρ e) :
    exec rodata (.vperm2i128 d a b imm) (relocState ρ st) = relocState ρ (exec rodata (.vperm2i128 d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ _
    rw [← next_reloc ρ]; apply congrArg next
    apply writeV_reloc' ρ
    rw [getV_reloc ρ, ← List.map_take, List.map_append]
    congr 1 <;> (split <;> (first | (simp only [List.map_cons, List.map_nil, reloc_const]; done) |
      (split <;> simp only [lane128_map (relocLane ρ hρ)])))
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vinserti128 (rodata : Array (BitVec 64)) (st : State E) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vinserti128 d a b imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vinserti128 d a b imm) st, E.relocOk ρ e) :
    exec rodata (.vinserti128 d a b imm) (relocState ρ st) = relocState ρ (exec rodata (.vinserti128 d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ _
    rw [← next_reloc ρ]; apply congrArg next
    apply writeV_reloc' ρ
    rw [getV_reloc ρ, ← List.map_take]
    simp only [map_ite_list, List.map_append, lane128_map (relocLane ρ hρ)]
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vextracti128 (rodata : Array (BitVec 64)) (st : State E) (m : _) (a : _) (imm : _)
    (hne : (exec rodata (.vextracti128 m a imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vextracti128 m a imm) st, E.relocOk ρ e) :
    exec rodata (.vextracti128 m a imm) (relocState ρ st) = relocState ρ (exec rodata (.vextracti128 m a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro ad _ hne2
    apply withStore_reloc ρ hρ _ _ _ _ (by rw [getV_reloc ρ, ← List.map_take, lane128_map (relocLane ρ hρ)]) _ _ hne2
    intro s' _ _; rfl
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vshufi64x2 (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vshufi64x2 lanes d a b imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vshufi64x2 lanes d a b imm) st, E.relocOk ρ e) :
    exec rodata (.vshufi64x2 lanes d a b imm) (relocState ρ st) = relocState ρ (exec rodata (.vshufi64x2 lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ _
    rw [← next_reloc ρ]; apply congrArg next
    apply writeV_reloc' ρ
    rw [getV_reloc ρ, ← List.map_take]
    simp only [ite_map_list, lane128_map (relocLane ρ hρ), foldr_append_map]
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vpermt2q (rodata : Array (BitVec 64)) (st : State E) (lanes : _) (d : _) (idx : _) (b : _)
    (hne : (exec rodata (.vpermt2q lanes d idx b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vpermt2q lanes d idx b) st, E.relocOk ρ e) :
    exec rodata (.vpermt2q lanes d idx b) (relocState ρ st) = relocState ρ (exec rodata (.vpermt2q lanes d idx b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_reloc ρ hρ _ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))
    intro bs _ hne2
    have hv : ((relocState ρ st).getV idx).take lanes = ((st.getV idx).take lanes).map (E.reloc ρ) := by
      rw [getV_reloc ρ, List.map_take]
    rw [hv]
    rcases hall : (((st.getV idx).take lanes).map LaneOps.asConst).all Option.isSome with _ | _
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
    · rw [asConst_map_all (relocLane ρ hρ) _ hall]
      simp only [hall, ↓reduceIte]
      rw [← next_reloc ρ]; apply congrArg next
      apply writeV_reloc' ρ
      rw [getV_reloc ρ, ← List.map_take]
      simp only [List.map_map, Function.comp_def, getD_reloc ρ, map_ite]
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_kmovw (rodata : Array (BitVec 64)) (st : State E) (k : _) (m : _)
    (hne : (exec rodata (.kmovw k m) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.kmovw k m) st, E.relocOk ρ e) :
    exec rodata (.kmovw k m) (relocState ρ st) = relocState ρ (exec rodata (.kmovw k m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro a _ hne2
    rw [Reloc.addr_region, Reloc.addr_div8 ρ hρ, read_reloc ρ hρ, reloc_asConst ρ hρ, Reloc.addr_mod8 ρ hρ]
    rcases hc : LaneOps.asConst (st.read rodata a.region (a.off / 8)) with _ | w
    · simp only [hc, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [hc]; rfl
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_vzeroupper (rodata : Array (BitVec 64)) (st : State E)
    (hne : (exec rodata (.vzeroupper) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.vzeroupper) st, E.relocOk ρ e) :
    exec rodata (.vzeroupper) (relocState ρ st) = relocState ρ (exec rodata (.vzeroupper) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, next_reloc ρ]
  · simp [exec, relocState, hh]


include hρ in
theorem exec_reloc_mov (rodata : Array (BitVec 64)) (st : State E) (d : _) (src : _)
    (hne : (exec rodata (.mov d src) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.mov d src) st, E.relocOk ρ e) :
    exec rodata (.mov d src) (relocState ρ st) = relocState ρ (exec rodata (.mov d src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rw [getGD_reloc, setGD_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_xchg (rodata : Array (BitVec 64)) (st : State E) (a : _) (b : _)
    (hne : (exec rodata (.xchg a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.xchg a b) st, E.relocOk ρ e) :
    exec rodata (.xchg a b) (relocState ρ st) = relocState ρ (exec rodata (.xchg a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rw [getGD_reloc, getGD_reloc, setGD_reloc, setGD_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_movi (rodata : Array (BitVec 64)) (st : State E) (d : _) (imm : _)
    (hne : (exec rodata (.movi d imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.movi d imm) st, E.relocOk ρ e) :
    exec rodata (.movi d imm) (relocState ρ st) = relocState ρ (exec rodata (.movi d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rw [← next_reloc]; exact congrArg next (setGD_reloc' ρ _ _ _ _ rfl)
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_lea (rodata : Array (BitVec 64)) (st : State E) (d : _) (m : _)
    (hne : (exec rodata (.lea d m) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.lea d m) st, E.relocOk ρ e) :
    exec rodata (.lea d m) (relocState ρ st) = relocState ρ (exec rodata (.lea d m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro a _ _; rw [setX_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_add (rodata : Array (BitVec 64)) (st : State E) (d : _) (imm : _)
    (hne : (exec rodata (.add d imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.add d imm) st, E.relocOk ρ e) :
    exec rodata (.add d imm) (relocState ρ st) = relocState ρ (exec rodata (.add d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro a _ _; rw [addr_mk_add, setX_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_sub (rodata : Array (BitVec 64)) (st : State E) (d : _) (imm : _)
    (hne : (exec rodata (.sub d imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.sub d imm) st, E.relocOk ρ e) :
    exec rodata (.sub d imm) (relocState ρ st) = relocState ρ (exec rodata (.sub d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro a _ _
    by_cases h0 : a.region = 0
    · rw [Reloc.addr_region0 ρ hρ a h0]
      simp only [h0, ↓reduceIte]
      rw [setX_relocFix ρ _ _ ⟨0, a.off - imm⟩ (Reloc.addr_region0 ρ hρ _ rfl), setFlagsSub_reloc0 ρ hρ _ _ _ h0 rfl, next_reloc]
    · simp only [Reloc.addr_region, h0, ↓reduceIte]
      rw [addr_mk_sub', setX_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_andi (rodata : Array (BitVec 64)) (st : State E) (d : _) (imm : _)
    (hne : (exec rodata (.andi d imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.andi d imm) st, E.relocOk ρ e) :
    exec rodata (.andi d imm) (relocState ρ st) = relocState ρ (exec rodata (.andi d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro a _ _
    by_cases h0 : imm = -64 ∧ a.region = rStack
    · rw [Reloc.addr_stack ρ hρ a h0.2]
      simp only [h0, and_self, ↓reduceIte]
      rw [setX_relocFix ρ _ _ ⟨rStack, a.off - a.off % 64⟩ (Reloc.addr_stack ρ hρ _ rfl), next_reloc]
    · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_shl (rodata : Array (BitVec 64)) (st : State E) (d : _) (imm : _)
    (hne : (exec rodata (.shl d imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.shl d imm) st, E.relocOk ρ e) :
    exec rodata (.shl d imm) (relocState ρ st) = relocState ρ (exec rodata (.shl d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro a _ _
    by_cases h0 : a.region = 0
    · rw [Reloc.addr_region0 ρ hρ a h0]
      simp only [h0, ↓reduceIte]
      rw [setX_relocFix ρ _ _ ⟨0, a.off * 2 ^ imm⟩ (Reloc.addr_region0 ρ hρ _ rfl), next_reloc]
    · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_dec (rodata : Array (BitVec 64)) (st : State E) (d : _)
    (hne : (exec rodata (.dec d) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.dec d) st, E.relocOk ρ e) :
    exec rodata (.dec d) (relocState ρ st) = relocState ρ (exec rodata (.dec d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro a _ _
    by_cases h0 : a.region = 0
    · rw [Reloc.addr_region0 ρ hρ a h0]
      simp only [h0, ↓reduceIte]
      rw [setX_relocFix ρ _ _ ⟨0, a.off - 1⟩ (Reloc.addr_region0 ρ hρ _ rfl)]; rfl
    · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_xorz (rodata : Array (BitVec 64)) (st : State E) (d : _)
    (hne : (exec rodata (.xorz d) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.xorz d) st, E.relocOk ρ e) :
    exec rodata (.xorz d) (relocState ρ st) = relocState ρ (exec rodata (.xorz d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rw [setX_relocFix ρ _ _ _ (Reloc.addr_num ρ hρ 0)]; rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_cmpi (rodata : Array (BitVec 64)) (st : State E) (a : _) (imm : _)
    (hne : (exec rodata (.cmpi a imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.cmpi a imm) st, E.relocOk ρ e) :
    exec rodata (.cmpi a imm) (relocState ρ st) = relocState ρ (exec rodata (.cmpi a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro x _ _; rw [setFlagsSub_reloc_num ρ hρ, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_cmpr (rodata : Array (BitVec 64)) (st : State E) (a : _) (b : _)
    (hne : (exec rodata (.cmpr a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.cmpr a b) st, E.relocOk ρ e) :
    exec rodata (.cmpr a b) (relocState ρ st) = relocState ρ (exec rodata (.cmpr a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro x _ hne2
    apply withX_reloc ρ hρ _ _ _ _ hne2 (hok _ (by simp [decodes]))
    intro y _ _; rw [setFlagsSub_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_cmpm (rodata : Array (BitVec 64)) (st : State E) (m : _) (b : _)
    (hne : (exec rodata (.cmpm m b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.cmpm m b) st, E.relocOk ρ e) :
    exec rodata (.cmpm m b) (relocState ρ st) = relocState ρ (exec rodata (.cmpm m b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro ad had hne2
    apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
    intro ws hws hne3
    rw [headD_reloc]
    rcases hc : LaneOps.asAddr (ws.headD (LaneOps.const 0)) with _ | v
    · simp only [hc, fail_err] at hne3; exact absurd hne3 (by decide)
    · simp only [hc] at hne3
      rw [reloc_asAddr ρ hρ _ _ hc (hok _ (by simp [decodes, had, hws]))]
      apply withX_reloc ρ hρ _ _ _ _ hne3 (hok _ (by simp [decodes]))
      intro y _ _; rw [setFlagsSub_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_cmprm (rodata : Array (BitVec 64)) (st : State E) (a : _) (m : _)
    (hne : (exec rodata (.cmprm a m) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.cmprm a m) st, E.relocOk ρ e) :
    exec rodata (.cmprm a m) (relocState ρ st) = relocState ρ (exec rodata (.cmprm a m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro ad had hne2
    apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
    intro ws hws hne3
    rw [headD_reloc]
    rcases hc : LaneOps.asAddr (ws.headD (LaneOps.const 0)) with _ | v
    · simp only [hc, fail_err] at hne3; exact absurd hne3 (by decide)
    · simp only [hc] at hne3
      rw [reloc_asAddr ρ hρ _ _ hc (hok _ (by simp [decodes, had, hws]))]
      apply withX_reloc ρ hρ _ _ _ _ hne3 (hok _ (by simp [decodes]))
      intro y _ _; rw [setFlagsSub_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_test (rodata : Array (BitVec 64)) (st : State E) (a : _) (b : _)
    (hne : (exec rodata (.test a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.test a b) st, E.relocOk ρ e) :
    exec rodata (.test a b) (relocState ρ st) = relocState ρ (exec rodata (.test a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro x _ hne2
    apply withX_reloc ρ hρ _ _ _ _ hne2 (hok _ (by simp [decodes]))
    intro y _ _
    by_cases h0 : x.region = 0 ∧ y.region = 0
    · rw [Reloc.addr_region0 ρ hρ x h0.1, Reloc.addr_region0 ρ hρ y h0.2]
      simp only [h0, and_self, ↓reduceIte]; rfl
    · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_bt (rodata : Array (BitVec 64)) (st : State E) (a : _) (b : _)
    (hne : (exec rodata (.bt a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.bt a b) st, E.relocOk ρ e) :
    exec rodata (.bt a b) (relocState ρ st) = relocState ρ (exec rodata (.bt a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rw [getGD_reloc, reloc_asConst ρ hρ]
    rcases hc : LaneOps.asConst (st.getGD a) with _ | w
    · simp only [hc, fail_err] at hne; exact absurd hne (by decide)
    · simp only [hc] at hne ⊢
      apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
      intro y _ _
      by_cases h0 : y.region = 0
      · rw [Reloc.addr_region0 ρ hρ y h0]; split <;> rfl
      · simp only [Reloc.addr_region, h0, false_and, ↓reduceIte, fail_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_btc (rodata : Array (BitVec 64)) (st : State E) (a : _) (imm : _)
    (hne : (exec rodata (.btc a imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.btc a imm) st, E.relocOk ρ e) :
    exec rodata (.btc a imm) (relocState ρ st) = relocState ρ (exec rodata (.btc a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rw [getGD_reloc, ← next_reloc]; exact congrArg next (setGD_reloc' ρ _ _ _ _ rfl)
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_alu (rodata : Array (BitVec 64)) (st : State E) (op : _) (d : _) (b : _)
    (hne : (exec rodata (.alu op d b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.alu op d b) st, E.relocOk ρ e) :
    exec rodata (.alu op d b) (relocState ρ st) = relocState ρ (exec rodata (.alu op d b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply readG_reloc ρ hρ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by subst hb; subst hm; simp [decodes]))
    intro y _
    rw [← next_reloc]; exact congrArg next (setGD_reloc' ρ _ _ _ _ (by rw [getGD_reloc, aluOp_map (relocLane ρ hρ)]))
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_andn (rodata : Array (BitVec 64)) (st : State E) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.andn d a b) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.andn d a b) st, E.relocOk ρ e) :
    exec rodata (.andn d a b) (relocState ρ st) = relocState ρ (exec rodata (.andn d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply readG_reloc ρ hρ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by subst hb; subst hm; simp [decodes]))
    intro y _
    rw [← next_reloc]; exact congrArg next (setGD_reloc' ρ _ _ _ _ (by rw [getGD_reloc]; rfl))
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_rorx (rodata : Array (BitVec 64)) (st : State E) (d : _) (b : _) (imm : _)
    (hne : (exec rodata (.rorx d b imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.rorx d b imm) st, E.relocOk ρ e) :
    exec rodata (.rorx d b imm) (relocState ρ st) = relocState ρ (exec rodata (.rorx d b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply readG_reloc ρ hρ _ _ _ _ _ hne (fun m g disp hb hm => hok _ (by subst hb; subst hm; simp [decodes]))
    intro y _
    rw [← next_reloc]; exact congrArg next (setGD_reloc' ρ _ _ _ _ (rfl))
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_xorm (rodata : Array (BitVec 64)) (st : State E) (m : _) (src : _)
    (hne : (exec rodata (.xorm m src) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.xorm m src) st, E.relocOk ρ e) :
    exec rodata (.xorm m src) (relocState ρ st) = relocState ρ (exec rodata (.xorm m src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro a _ hne2
    apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
    intro ws _ hne3
    apply withStore_reloc ρ hρ _ _ _ _ (by simp only [headD_reloc, getGD_reloc, List.map_cons, List.map_nil, reloc_xor]) _ _ hne3
    intro s' _ _; rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_storeqi (rodata : Array (BitVec 64)) (st : State E) (m : _) (imm : _)
    (hne : (exec rodata (.storeqi m imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.storeqi m imm) st, E.relocOk ρ e) :
    exec rodata (.storeqi m imm) (relocState ρ st) = relocState ρ (exec rodata (.storeqi m imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro a _ hne2
    apply withStore_reloc ρ hρ _ _ _ _ rfl _ _ hne2
    intro s' _ _; rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_addm (rodata : Array (BitVec 64)) (st : State E) (m : _) (imm : _)
    (hne : (exec rodata (.addm m imm) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.addm m imm) st, E.relocOk ρ e) :
    exec rodata (.addm m imm) (relocState ρ st) = relocState ρ (exec rodata (.addm m imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro a _ hne2
    apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
    intro ws _ hne3
    apply withStore_reloc ρ hρ _ _ _ _ (by simp only [headD_reloc, List.map_cons, List.map_nil, reloc_add, reloc_const]) _ _ hne3
    intro s' _ _; rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_decm (rodata : Array (BitVec 64)) (st : State E) (m : _)
    (hne : (exec rodata (.decm m) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.decm m) st, E.relocOk ρ e) :
    exec rodata (.decm m) (relocState ρ st) = relocState ρ (exec rodata (.decm m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro ad had hne2
    apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
    intro ws hws hne3
    rw [headD_reloc]
    rcases hc : LaneOps.asAddr (ws.headD (LaneOps.const 0)) with _ | v
    · simp only [hc, fail_err] at hne3; exact absurd hne3 (by decide)
    · simp only [hc] at hne3
      rw [reloc_asAddr ρ hρ _ _ hc (hok _ (by simp [decodes, had, hws]))]
      by_cases h0 : v.region = 0
      · rw [Reloc.addr_region0 ρ hρ v h0]
        simp only [h0, ↓reduceIte] at hne3 ⊢
        apply withStore_reloc ρ hρ _ _ _ _ (by simp only [List.map_cons, List.map_nil, reloc_ptr]; rw [Reloc.addr_region0 ρ hρ _ rfl]) _ _ hne3
        intro s' _ _; rfl
      · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_jcc (rodata : Array (BitVec 64)) (st : State E) (c : _) (t : _)
    (hne : (exec rodata (.jcc c t) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.jcc c t) st, E.relocOk ρ e) :
    exec rodata (.jcc c t) (relocState ρ st) = relocState ρ (exec rodata (.jcc c t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    simp only [condHolds_reloc]; rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_jmp (rodata : Array (BitVec 64)) (st : State E) (t : _)
    (hne : (exec rodata (.jmp t) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.jmp t) st, E.relocOk ρ e) :
    exec rodata (.jmp t) (relocState ρ st) = relocState ρ (exec rodata (.jmp t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_jcct (rodata : Array (BitVec 64)) (st : State E) (c : _) (name : _)
    (hne : (exec rodata (.jcct c name) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.jcct c name) st, E.relocOk ρ e) :
    exec rodata (.jcct c name) (relocState ρ st) = relocState ρ (exec rodata (.jcct c name) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    simp only [condHolds_reloc]; split <;> rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_call (rodata : Array (BitVec 64)) (st : State E) (t : _)
    (hne : (exec rodata (.call t) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.call t) st, E.relocOk ρ e) :
    exec rodata (.call t) (relocState ρ st) = relocState ρ (exec rodata (.call t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro sp _ hne2
    rw [addr_mk_sub]
    apply withStore_reloc ρ hρ _ _ _ _ (by simp only [List.map_cons, List.map_nil, reloc_ptr, Reloc.addr_num ρ hρ, pc_reloc]) _ _ hne2
    intro s' _ _; rw [setX_reloc]; rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_ret (rodata : Array (BitVec 64)) (st : State E)
    (hne : (exec rodata (.ret) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.ret) st, E.relocOk ρ e) :
    exec rodata (.ret) (relocState ρ st) = relocState ρ (exec rodata (.ret) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    by_cases hd : st.depth = 0
    · simp only [depth_reloc, hd, ↓reduceIte]; rfl
    · simp only [depth_reloc, hd, ↓reduceIte] at hne ⊢
      apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
      intro sp hsp hne2
      apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
      intro ws hws hne3
      rw [headD_reloc]
      rcases hc : LaneOps.asAddr (ws.headD (LaneOps.const 0)) with _ | ra
      · simp only [hc, fail_err] at hne3; exact absurd hne3 (by decide)
      · simp only [hc] at hne3
        rw [reloc_asAddr ρ hρ _ _ hc (hok _ (by simp [decodes, hsp, hws]))]
        by_cases h0 : ra.region = 0
        · rw [Reloc.addr_region0 ρ hρ ra h0]
          simp only [h0, ↓reduceIte]
          rw [addr_mk_add, setX_reloc]; rfl
        · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_push (rodata : Array (BitVec 64)) (st : State E) (src : _)
    (hne : (exec rodata (.push src) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.push src) st, E.relocOk ρ e) :
    exec rodata (.push src) (relocState ρ st) = relocState ρ (exec rodata (.push src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro sp _ hne2
    rw [addr_mk_sub]
    apply withStore_reloc ρ hρ _ _ _ _ (by simp only [getGD_reloc, List.map_cons, List.map_nil]) _ _ hne2
    intro s' _ _; rw [setX_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_pop (rodata : Array (BitVec 64)) (st : State E) (d : _)
    (hne : (exec rodata (.pop d) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.pop d) st, E.relocOk ρ e) :
    exec rodata (.pop d) (relocState ρ st) = relocState ρ (exec rodata (.pop d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro sp _ hne2
    apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
    intro ws _ _
    rw [headD_reloc, setGD_reloc, addr_mk_add, setX_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_storeq (rodata : Array (BitVec 64)) (st : State E) (m : _) (src : _)
    (hne : (exec rodata (.storeq m src) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.storeq m src) st, E.relocOk ρ e) :
    exec rodata (.storeq m src) (relocState ρ st) = relocState ρ (exec rodata (.storeq m src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro a _ hne2
    apply withStore_reloc ρ hρ _ _ _ _ (by simp only [getGD_reloc, List.map_cons, List.map_nil]) _ _ hne2
    intro s' _ _; rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_loadq (rodata : Array (BitVec 64)) (st : State E) (d : _) (m : _)
    (hne : (exec rodata (.loadq d m) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.loadq d m) st, E.relocOk ρ e) :
    exec rodata (.loadq d m) (relocState ρ st) = relocState ρ (exec rodata (.loadq d m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_reloc ρ hρ _ _ _ _ hne (fun g disp hm => hok _ (by subst hm; simp [decodes]))
    intro a _ hne2
    apply withLoad_reloc ρ hρ _ _ _ _ _ _ hne2
    intro ws _ _
    rw [headD_reloc, setGD_reloc, next_reloc]
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_repmovsb (rodata : Array (BitVec 64)) (st : State E)
    (hne : (exec rodata (.repmovsb) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.repmovsb) st, E.relocOk ρ e) :
    exec rodata (.repmovsb) (relocState ρ st) = relocState ρ (exec rodata (.repmovsb) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_reloc ρ hρ _ _ _ _ hne (hok _ (by simp [decodes]))
    intro n _ hne2
    apply withX_reloc ρ hρ _ _ _ _ hne2 (hok _ (by simp [decodes]))
    intro src _ hne3
    apply withX_reloc ρ hρ _ _ _ _ hne3 (hok _ (by simp [decodes]))
    intro dst _ hne4
    exact repBody_reloc ρ hρ rodata st n src dst hne4
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_tailcall (rodata : Array (BitVec 64)) (st : State E) (name : _)
    (hne : (exec rodata (.tailcall name) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.tailcall name) st, E.relocOk ρ e) :
    exec rodata (.tailcall name) (relocState ρ st) = relocState ρ (exec rodata (.tailcall name) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rfl
  · simp [exec, relocState, hh]

include hρ in
theorem exec_reloc_nop (rodata : Array (BitVec 64)) (st : State E)
    (hne : (exec rodata (.nop) st).err = false)
    (hok : ∀ e ∈ decodes rodata (.nop) st, E.relocOk ρ e) :
    exec rodata (.nop) (relocState ρ st) = relocState ρ (exec rodata (.nop) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    rw [next_reloc]
  · simp [exec, relocState, hh]


include hρ in
/-- **`exec` commutes with relocation** (x86), for every instruction whose symbolic
step does not fail and whose decoded addresses stay representable. -/
theorem exec_reloc (rodata : Array (BitVec 64)) (i : Instr) (st : State E)
    (hne : (exec rodata i st).err = false) (hok : ∀ e ∈ decodes rodata i st, E.relocOk ρ e) :
    exec rodata i (relocState ρ st) = relocState ρ (exec rodata i st) := by
  cases i with
  | vmov lanes dst src mask => exact exec_reloc_vmov ρ hρ rodata st lanes dst src mask hne hok
  | vstore lanes dst src => exact exec_reloc_vstore ρ hρ rodata st lanes dst src hne hok
  | vpxor lanes d a b => exact exec_reloc_vpxor ρ hρ rodata st lanes d a b hne hok
  | vpand lanes d a b => exact exec_reloc_vpand ρ hρ rodata st lanes d a b hne hok
  | vpandn lanes d a b => exact exec_reloc_vpandn ρ hρ rodata st lanes d a b hne hok
  | vpor lanes d a b => exact exec_reloc_vpor ρ hρ rodata st lanes d a b hne hok
  | vpaddq lanes d a b => exact exec_reloc_vpaddq ρ hρ rodata st lanes d a b hne hok
  | vpsllq lanes d a imm => exact exec_reloc_vpsllq ρ hρ rodata st lanes d a imm hne hok
  | vpsrlq lanes d a imm => exact exec_reloc_vpsrlq ρ hρ rodata st lanes d a imm hne hok
  | vprolq lanes d a imm => exact exec_reloc_vprolq ρ hρ rodata st lanes d a imm hne hok
  | vpsllvq lanes d a b => exact exec_reloc_vpsllvq ρ hρ rodata st lanes d a b hne hok
  | vpsrlvq lanes d a b => exact exec_reloc_vpsrlvq ρ hρ rodata st lanes d a b hne hok
  | vpternlogq lanes d a b imm => exact exec_reloc_vpternlogq ρ hρ rodata st lanes d a b imm hne hok
  | vpshufb lanes d a ctrl => exact exec_reloc_vpshufb ρ hρ rodata st lanes d a ctrl hne hok
  | vpshufd lanes d a imm => exact exec_reloc_vpshufd ρ hρ rodata st lanes d a imm hne hok
  | vpblendd lanes d a b imm => exact exec_reloc_vpblendd ρ hρ rodata st lanes d a b imm hne hok
  | vpalignr lanes d a b imm => exact exec_reloc_vpalignr ρ hρ rodata st lanes d a b imm hne hok
  | vpunpcklqdq lanes d a b => exact exec_reloc_vpunpcklqdq ρ hρ rodata st lanes d a b hne hok
  | vpunpckhqdq lanes d a b => exact exec_reloc_vpunpckhqdq ρ hρ rodata st lanes d a b hne hok
  | vperm2i128 d a b imm => exact exec_reloc_vperm2i128 ρ hρ rodata st d a b imm hne hok
  | vinserti128 d a b imm => exact exec_reloc_vinserti128 ρ hρ rodata st d a b imm hne hok
  | vextracti128 m a imm => exact exec_reloc_vextracti128 ρ hρ rodata st m a imm hne hok
  | vshufi64x2 lanes d a b imm => exact exec_reloc_vshufi64x2 ρ hρ rodata st lanes d a b imm hne hok
  | vpermt2q lanes d idx b => exact exec_reloc_vpermt2q ρ hρ rodata st lanes d idx b hne hok
  | kmovw k m => exact exec_reloc_kmovw ρ hρ rodata st k m hne hok
  | vzeroupper => exact exec_reloc_vzeroupper ρ hρ rodata st hne hok
  | mov d src => exact exec_reloc_mov ρ hρ rodata st d src hne hok
  | xchg a b => exact exec_reloc_xchg ρ hρ rodata st a b hne hok
  | movi d imm => exact exec_reloc_movi ρ hρ rodata st d imm hne hok
  | lea d m => exact exec_reloc_lea ρ hρ rodata st d m hne hok
  | add d imm => exact exec_reloc_add ρ hρ rodata st d imm hne hok
  | sub d imm => exact exec_reloc_sub ρ hρ rodata st d imm hne hok
  | andi d imm => exact exec_reloc_andi ρ hρ rodata st d imm hne hok
  | shl d imm => exact exec_reloc_shl ρ hρ rodata st d imm hne hok
  | dec d => exact exec_reloc_dec ρ hρ rodata st d hne hok
  | xorz d => exact exec_reloc_xorz ρ hρ rodata st d hne hok
  | cmpi a imm => exact exec_reloc_cmpi ρ hρ rodata st a imm hne hok
  | cmpr a b => exact exec_reloc_cmpr ρ hρ rodata st a b hne hok
  | cmpm m b => exact exec_reloc_cmpm ρ hρ rodata st m b hne hok
  | cmprm a m => exact exec_reloc_cmprm ρ hρ rodata st a m hne hok
  | test a b => exact exec_reloc_test ρ hρ rodata st a b hne hok
  | bt a b => exact exec_reloc_bt ρ hρ rodata st a b hne hok
  | btc a imm => exact exec_reloc_btc ρ hρ rodata st a imm hne hok
  | alu op d b => exact exec_reloc_alu ρ hρ rodata st op d b hne hok
  | andn d a b => exact exec_reloc_andn ρ hρ rodata st d a b hne hok
  | rorx d b imm => exact exec_reloc_rorx ρ hρ rodata st d b imm hne hok
  | xorm m src => exact exec_reloc_xorm ρ hρ rodata st m src hne hok
  | storeqi m imm => exact exec_reloc_storeqi ρ hρ rodata st m imm hne hok
  | addm m imm => exact exec_reloc_addm ρ hρ rodata st m imm hne hok
  | decm m => exact exec_reloc_decm ρ hρ rodata st m hne hok
  | jcc c t => exact exec_reloc_jcc ρ hρ rodata st c t hne hok
  | jmp t => exact exec_reloc_jmp ρ hρ rodata st t hne hok
  | jcct c name => exact exec_reloc_jcct ρ hρ rodata st c name hne hok
  | call t => exact exec_reloc_call ρ hρ rodata st t hne hok
  | ret => exact exec_reloc_ret ρ hρ rodata st hne hok
  | push src => exact exec_reloc_push ρ hρ rodata st src hne hok
  | pop d => exact exec_reloc_pop ρ hρ rodata st d hne hok
  | storeq m src => exact exec_reloc_storeq ρ hρ rodata st m src hne hok
  | loadq d m => exact exec_reloc_loadq ρ hρ rodata st d m hne hok
  | repmovsb => exact exec_reloc_repmovsb ρ hρ rodata st hne hok
  | tailcall name => exact exec_reloc_tailcall ρ hρ rodata st name hne hok
  | nop => exact exec_reloc_nop ρ hρ rodata st hne hok

end State
end X86

/-! ## Relocatable instruction sets -/

/-- An instruction set whose semantics commute with relocation: the lane values each
step decodes as addresses (`decodes`), and `exec_reloc` for them. -/
structure Isa.Relocatable (isa : Isa) where
  decodes : Array (BitVec 64) → isa.Instr → State E → List E
  exec_reloc : ∀ (ρ : Reloc), ρ.ok → ∀ (rodata : Array (BitVec 64)) (i : isa.Instr) (st : State E),
    (isa.exec rodata i st).err = false → (∀ e ∈ decodes rodata i st, E.relocOk ρ e) →
      isa.exec rodata i (X86.relocState ρ st) = X86.relocState ρ (isa.exec rodata i st)

/-- The decoded lane values along a trace. -/
def Isa.Relocatable.traceDecodes {isa : Isa} (R : isa.Relocatable) (rodata : Array (BitVec 64)) :
    List isa.Instr → State E → List E
  | [], _ => []
  | i :: l, s => R.decodes rodata i s ++ R.traceDecodes rodata l (isa.exec rodata i s)

/-- **A symbolic trace commutes with relocation**: the run of a relocated cut is the
relocated run, if the run does not fail and its decoded addresses stay representable. -/
theorem Isa.Relocatable.execTrace_reloc {isa : Isa} (R : isa.Relocatable) (ρ : Reloc) (hρ : ρ.ok)
    (rodata : Array (BitVec 64)) (l : List isa.Instr) (st : State E)
    (hne : (isa.execTrace rodata l st).err = false) (hok : ∀ e ∈ R.traceDecodes rodata l st, E.relocOk ρ e) :
    isa.execTrace rodata l (X86.relocState ρ st) = X86.relocState ρ (isa.execTrace rodata l st) := by
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
    simp only [Isa.Relocatable.traceDecodes, List.mem_append] at hok
    rw [R.exec_reloc ρ hρ rodata i st h1 (fun e he => hok e (Or.inl he))]
    exact ih _ hne (fun e he => hok e (Or.inr he))

/-- The x86 instruction set is relocatable. -/
def X86.isaReloc : X86.isa.Relocatable where
  decodes := X86.decodes
  exec_reloc := fun ρ hρ rodata i st hne hok => X86.exec_reloc ρ hρ rodata i st hne hok

end Keccaktree.Asm
