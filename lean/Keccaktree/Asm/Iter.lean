import Keccaktree.Asm.Reloc
import Keccaktree.Asm.Footprint
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Relocated slices: one symbolic run, every iteration

A *slice certificate* bundles the closed, kernel-checked facts about one recorded
slice at its base position (the cut's control words and closed control state, the
recorded path, the decoded addresses' bound, the next cut's control words as closed
trees, the control part after the slice).  `SliceCert.step` turns it into a fact about
every relocated position: from any concrete state whose cut is the base cut relocated
by `ρ`, the fetch-execute loop runs the recorded path, lands on the evaluation of the
relocated symbolic result, and the next cut is the base next cut relocated by `ρ`.
`SliceCert.data` transfers the lane invariants (`step{c}` of the generated proofs) to
the relocated position, and `SliceCert.frame` keeps every memory cell the base run
does not store to.
-/
namespace Keccaktree.Asm
open X86

/-! ## Footprints along a trace -/

/-- What an instruction set's steps store to, with the frame property. -/
structure Isa.Footprint (isa : Isa) where
  writes : State E → isa.Instr → List (Region × Int)
  exec_frame : ∀ (rodata : Array (BitVec 64)) (i : isa.Instr) (s : State E),
    (isa.exec rodata i s).err = false → ∀ r q, (r, q) ∉ writes s i → (isa.exec rodata i s).mem r q = s.mem r q

def Isa.Footprint.traceWrites {isa : Isa} (F : isa.Footprint) (rodata : Array (BitVec 64)) :
    List isa.Instr → State E → List (Region × Int)
  | [], _ => []
  | i :: l, s => F.writes s i ++ F.traceWrites rodata l (isa.exec rodata i s)

theorem Isa.Footprint.execTrace_frame {isa : Isa} (F : isa.Footprint) (rodata : Array (BitVec 64))
    (l : List isa.Instr) (s : State E) (hne : (isa.execTrace rodata l s).err = false)
    (r : Region) (q : Int) (hw : (r, q) ∉ F.traceWrites rodata l s) :
    (isa.execTrace rodata l s).mem r q = s.mem r q := by
  induction l generalizing s with
  | nil => rfl
  | cons i l ih =>
    simp only [Isa.execTrace, List.foldl_cons] at hne ⊢
    simp only [Isa.Footprint.traceWrites, List.mem_append, not_or] at hw
    have h1 : (isa.exec rodata i s).err = false := by
      cases hc : (isa.exec rodata i s).err
      · rfl
      · have := isa.err_execTrace rodata l _ hc
        simp only [Isa.execTrace] at this
        rw [this] at hne; exact absurd hne (by decide)
    have := ih (isa.exec rodata i s) hne hw.2
    simp only [Isa.execTrace] at this
    rw [this, F.exec_frame rodata i s h1 r q hw.1]

/-- The x86 footprint. -/
def X86.isaFoot : X86.isa.Footprint where
  writes := fun s i => X86.writes s i
  exec_frame := fun rodata i s hne r q hw => X86.exec_frame rodata i s hne r q hw

/-! ## Relocation of a state, read at the relocated variables -/

theorem readVar_relocState_var (ρ : Reloc) (t : State E) (i : Nat) :
    readVar (relocState ρ t) (ρ.var i) = E.reloc ρ (readVar t i) := by
  by_cases h : i < 288
  · rw [Reloc.var_lt ρ i h]
    unfold readVar
    by_cases h1 : i < 256
    · have h2 : i / 8 < 32 := by omega
      have h3 : i % 8 < 8 := Nat.mod_lt _ (by decide)
      simp only [h1, ↓reduceIte, relocState, Vector.getD, Array.getD, Vector.size_toArray, h2, h3, ↓reduceDIte,
        Array.getInternal_eq_getElem, Vector.getElem_toArray, Vector.getElem_map]
    · have h2 : i - 256 < 32 := by omega
      simp only [h1, h, ↓reduceIte, relocState, Vector.getD, Array.getD, Vector.size_toArray, h2, ↓reduceDIte,
        Array.getInternal_eq_getElem, Vector.getElem_toArray, Vector.getElem_map]
  · have hv : ρ.var i = memVar (memVarRegion i) (memVarIndex i + ρ.wshift (memVarRegion i)) := by
      simp only [Reloc.var, h, ↓reduceIte]
    have hge := memVar_ge (memVarRegion i) (memVarIndex i + ρ.wshift (memVarRegion i))
    rw [hv]
    simp only [readVar, show ¬ memVar (memVarRegion i) (memVarIndex i + ρ.wshift (memVarRegion i)) < 256 by omega,
      show ¬ memVar (memVarRegion i) (memVarIndex i + ρ.wshift (memVarRegion i)) < 288 by omega, ↓reduceIte,
      memVarRegion_memVar, memVarIndex_memVar, h, show ¬ i < 256 by omega, relocState, Int.add_sub_cancel]

/-! ## The recorded path at a relocated position -/

theorem pathOk_reloc {isa : Isa} (R : isa.Relocatable) (ρ : Reloc) (hρ : ρ.ok) (rodata : Array (BitVec 64))
    (prog : Array isa.Instr) (idx : List Nat) (t : State E) (h : isa.pathOk rodata prog idx t = true)
    (hok : ∀ e ∈ R.traceDecodes rodata (idx.map (prog.getD · isa.nop)) t, E.relocOk ρ e) :
    isa.pathOk rodata prog idx (relocState ρ t) = true := by
  induction idx generalizing t with
  | nil => simpa [Isa.pathOk, relocState] using h
  | cons i rest ih =>
    simp only [Isa.pathOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h ⊢
    obtain ⟨⟨⟨he, hh⟩, hpc⟩, hrest⟩ := h
    simp only [List.map_cons, Isa.Relocatable.traceDecodes, List.mem_append] at hok
    have hne : (isa.exec rodata (prog.getD i isa.nop) t).err = false := isa.pathOk_err rodata prog rest _ hrest
    refine ⟨⟨⟨by simpa [relocState] using he, by simpa [relocState] using hh⟩, by simpa [relocState] using hpc⟩, ?_⟩
    rw [R.exec_reloc ρ hρ rodata _ t hne (fun e he' => hok e (Or.inl he'))]
    exact ih _ hrest (fun e he' => hok e (Or.inr he'))

/-- The recorded path ends without a fault. -/
theorem pathOk_execTrace {isa : Isa} (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (idx : List Nat) (s : State E)
    (h : isa.pathOk rodata prog idx s = true) :
    (isa.execTrace rodata (idx.map (prog.getD · isa.nop)) s).err = false := by
  induction idx generalizing s with
  | nil => simpa [Isa.pathOk, Isa.execTrace] using h
  | cons i rest ih =>
    simp only [Isa.pathOk, Bool.and_eq_true] at h
    simp only [List.map_cons, Isa.execTrace, List.foldl_cons]
    exact ih _ h.2

/-! ## Encodings -/

theorem encInt_decInt (n : Nat) : encInt (decInt n) = n := by
  unfold encInt decInt
  split
  · rename_i h
    simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
    omega
  · rename_i h
    have hp : ¬ (0 ≤ -((((n + 1) / 2 : Nat)) : Int)) := by omega
    simp only [Int.ofNat_eq_natCast] at hp ⊢
    rw [if_neg hp]
    omega

theorem memVar_region_index (i : Nat) (h : 288 ≤ i) : memVar (memVarRegion i) (memVarIndex i) = i := by
  simp only [memVar, memVarRegion, memVarIndex, encInt_decInt]
  omega

/-! ## Slice certificates -/

/-- Is the closed control tree `e` representable after a relocation within `B`? -/
def ctlTreeOk (B : Int) : E → Bool
  | .ptr a => decide (a.wf ∧ a.off < B ∧ a.region ≠ 0)
  | .const _ => true
  | _ => false

/-- A pointer plus a closed number, folded into the pointer (a counter pointer stepped by `add`:
the next cut holds the folded pointer).  The number is signed (`toInt`: RISC-V moves the stack
pointer down with `addi sp, sp, -n`) and may be any closed expression (RVV advances its pointers by
`vl << 6`, `vl` a control constant). -/
def E.fold : E → E
  | .add (.ptr a) e => match e.closed with
    | some k => .ptr ⟨a.region, a.off + k.toInt⟩
    | none => .add (.ptr a) e
  | e => e

theorem gprWord_add_const (a : Addr) (k : BitVec 64) :
    gprWord a + k = gprWord ⟨a.region, a.off + k.toInt⟩ := by
  have h : BitVec.ofInt 64 (a.off + k.toInt) = BitVec.ofInt 64 a.off + k := by
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt]
  unfold gprWord
  simp only
  split
  · rw [h]
  · rw [h, BitVec.add_assoc]

theorem E.eval_reloc_fold (ρ : Reloc) (hρ : ρ.ok) (env : Nat → BitVec 64) (e : E) :
    E.eval env (E.reloc ρ (E.fold e)) = E.eval env (E.reloc ρ e) := by
  unfold E.fold
  split
  · rename_i a e'
    split
    · rename_i k hk
      have hk' : (e'.reloc ρ).closed = some k := by rw [E.closed_reloc ρ hρ]; exact hk
      simp only [E.reloc, E.eval, Reloc.addr]
      rw [E.closed_eval env _ k hk', gprWord_add_const]
      show gprWord ⟨a.region, a.off + k.toInt + ρ.δ a.region⟩ = gprWord ⟨a.region, a.off + ρ.δ a.region + k.toInt⟩
      exact congrArg (fun z : Int => gprWord ⟨a.region, z⟩) (by omega)
    · rfl
  · rfl

/-- The closed facts about one slice at its base position. -/
structure SliceCert (isa : Isa) (R : isa.Relocatable) (rodata : Array (BitVec 64)) (prog : Array isa.Instr) (B : Int) where
  ctl : List Nat
  sc : State (BitVec 64)
  idx : List Nat
  ctl' : List Nat
  sc' : State (BitVec 64)
  path : isa.pathOk rodata prog idx (cutOf ctl sc) = true
  dec : (R.traceDecodes rodata (idx.map (prog.getD · isa.nop)) (cutOf ctl sc)).all (E.addrsBelow B) = true
  glue : ctl'.all (fun v => E.fold (readVar (isa.execTrace rodata (idx.map (prog.getD · isa.nop)) (cutOf ctl sc)) v) ==
    cutVar ctl' sc' v && ctlTreeOk B (cutVar ctl' sc' v)) = true
  cells : ctl'.all (fun v => decide (v < 288) || decide (memVarRegion v = rStack)) = true
  ctrl : let t := isa.execTrace rodata (idx.map (prog.getD · isa.nop)) (cutOf ctl sc)
    t.g = sc'.g ∧ t.k = sc'.k ∧ t.zf = sc'.zf ∧ t.cf = sc'.cf ∧ t.nf = sc'.nf ∧ t.vf = sc'.vf ∧ t.vl = sc'.vl ∧
    t.pc = sc'.pc ∧ t.depth = sc'.depth ∧ t.halted = false ∧ t.tail = none

/-- A closed control word, relocated: its value after the relocated run is the relocated constant,
so the next cut's control word is the relocated one. -/
theorem cutVar_reloc_closed (ctl : List Nat) (sc S' : State (BitVec 64)) (i : Nat) (hi : i ∈ ctl)
    (ρ : Reloc) (hρ : ρ.ok) (B : Int) (hw : ρ.within B) (htree : ctlTreeOk B (cutVar ctl sc i) = true)
    (env : Nat → BitVec 64) (henv : envOf S' i = E.eval env (E.reloc ρ (cutVar ctl sc i))) :
    cutVar ctl S' i = E.reloc ρ (cutVar ctl sc i) := by
  have hc : ctl.contains i = true := List.contains_iff_mem.mpr hi
  generalize hT : cutVar ctl sc i = T at htree henv
  cases T with
  | ptr a =>
    simp only [ctlTreeOk, decide_eq_true_eq] at htree
    obtain ⟨⟨h0, h1⟩, hB, hreg⟩ := htree
    simp only [E.reloc, E.eval] at henv ⊢
    have hδ0 := (hρ.2.2.2 a.region).1
    have hδ := hw a.region
    have hwf : (ρ.addr a).wf := by
      simp only [Addr.wf, Reloc.addr]; constructor <;> omega
    have hwg := wordGpr_gprWord (ρ.addr a) hwf
    simp only [cutVar, hc, ↓reduceIte, henv, hwg, Reloc.addr_region, ne_eq, hreg, not_false_eq_true, true_and]
    all_goals rfl
  | const w =>
    simp only [E.reloc, E.eval] at henv ⊢
    simp only [cutVar, hc, ↓reduceIte] at hT ⊢
    split at hT
    · cases hT
    · rename_i hnf
      cases hT
      rw [henv]
      simp only [hnf, ↓reduceIte]
  | _ => simp [ctlTreeOk] at htree

namespace SliceCert
variable {isa : Isa} {R : isa.Relocatable} {rodata : Array (BitVec 64)} {prog : Array isa.Instr} {B : Int}
variable (C : SliceCert isa R rodata prog B)

def slice : List isa.Instr := C.idx.map (prog.getD · isa.nop)
def cut : State E := cutOf C.ctl C.sc
def res : State E := isa.execTrace rodata C.slice C.cut

/-- Status of a concrete state at a cut. -/
def Ok (S : State (BitVec 64)) : Prop := S.err = false ∧ S.halted = false ∧ S.tail = none

theorem res_err : C.res.err = false := pathOk_execTrace rodata prog C.idx C.cut C.path

theorem dec_ok (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) :
    ∀ e ∈ R.traceDecodes rodata C.slice C.cut, E.relocOk ρ e := by
  intro e he
  have := List.all_eq_true.mp C.dec e he
  exact E.relocOk_of_below ρ hρ B hw e this

theorem stack_wshift (ρ : Reloc) (hρ : ρ.ok) : ρ.wshift rStack = 0 := by
  simp only [Reloc.wshift, hρ.2.1]; rfl

/-- **One slice at a relocated position.** -/
theorem step (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B) (S : State (BitVec 64))
    (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) (hs : Ok S) :
    isa.run rodata prog C.idx.length S = isa.execTrace rodata C.slice S ∧
    isa.execTrace rodata C.slice S = mapState (E.eval (envOf S)) (relocState ρ C.res) ∧
    Ok (isa.execTrace rodata C.slice S) ∧
    relocState ρ (cutOf C.ctl' C.sc') = cutOf C.ctl' (isa.execTrace rodata C.slice S) := by
  have hok := C.dec_ok ρ hρ hw
  have hne := C.res_err
  have hconc := R.execTrace_reloc_concrete ρ hρ rodata C.slice C.ctl C.sc S hc hs hne hok
  have hpath := pathOk_reloc R ρ hρ rodata prog C.idx C.cut C.path hok
  refine ⟨?_, hconc, ?_, ?_⟩
  · have h := isa.run_of_pathOk rodata prog C.idx (envOf S) (relocState ρ C.cut) hpath
    have he : mapState (E.eval (envOf S)) (relocState ρ C.cut) = S := by
      show mapState (E.eval (envOf S)) (relocState ρ (cutOf C.ctl C.sc)) = S
      rw [hc]; exact eval_cutOf C.ctl S hs
    rw [he] at h; exact h
  · obtain ⟨_, _, _, _, _, _, _, _, _, hh, ht⟩ := C.ctrl
    rw [hconc]
    exact ⟨hne, hh, ht⟩
  · obtain ⟨hg, hk, hz, hcf, hn, hv, hvl, hpc, hd, _, _⟩ := C.ctrl
    apply relocState_cutOf
    · intro i hi
      have hg' := List.all_eq_true.mp C.glue i hi
      simp only [Bool.and_eq_true, beq_iff_eq] at hg'
      obtain ⟨hgl, htree⟩ := hg'
      have hcell := List.all_eq_true.mp C.cells i hi
      have hvar : ρ.var i = i := by
        by_cases hlt : i < 288
        · exact Reloc.var_lt ρ i hlt
        · have hr : memVarRegion i = rStack := by simpa [hlt] using hcell
          simp only [Reloc.var, hlt, ↓reduceIte, hr, stack_wshift ρ hρ, Int.add_zero]
          rw [← hr]
          exact memVar_region_index i (by omega)
      have henv : envOf (isa.execTrace rodata C.slice S) i =
          E.eval (envOf S) (E.reloc ρ (cutVar C.ctl' C.sc' i)) := by
        rw [hconc, envOf_mapState, ← hvar, readVar_relocState_var, hvar]
        show E.eval (envOf S) (E.reloc ρ (readVar C.res i)) = _
        rw [← E.eval_reloc_fold ρ hρ, show E.fold (readVar C.res i) = cutVar C.ctl' C.sc' i from hgl]
      exact cutVar_reloc_closed C.ctl' C.sc' _ i hi ρ hρ B hw htree _ henv
    · intro i hi hge
      have hcell := List.all_eq_true.mp C.cells i hi
      have hr : memVarRegion i = rStack := by simpa [show ¬ i < 288 by omega] using hcell
      rw [hr]; exact stack_wshift ρ hρ
    · rw [hconc]
      exact ⟨hg, hk, hz, hcf, hn, hv, hvl, hpc, hd⟩

/-- **The lane invariants at a relocated position**: reading the base variables at their relocated
locations, the state after the relocated slice holds the base symbolic lanes evaluated in the
relocated environment of the state before (for locations whose trees carry no pointer). -/
theorem data (ρ : Reloc) (hρ : ρ.ok) (S : State (BitVec 64)) (v : Nat) (hv : (readVar C.res v).noPtr = true) :
    envOf (mapState (E.eval (envOf S)) (relocState ρ C.res)) (ρ.var v) =
      E.eval (fun i => envOf S (ρ.var i)) (readVar C.res v) := by
  rw [envOf_mapState, readVar_relocState_var, E.eval_reloc_noPtr ρ _ _ hv]

/-- **The frame at a relocated position**: a memory cell the base run does not store to (at its
base location) keeps its value. -/
theorem frame (F : isa.Footprint) (ρ : Reloc) (S : State (BitVec 64))
    (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) (r : Region) (q : Int)
    (hw : (r, q - ρ.wshift r) ∉ F.traceWrites rodata C.slice C.cut) :
    (mapState (E.eval (envOf S)) (relocState ρ C.res)).mem r q = S.mem r q := by
  have h1 := F.execTrace_frame rodata C.slice C.cut C.res_err r (q - ρ.wshift r) hw
  have h2 : (relocState ρ (cutOf C.ctl C.sc)).mem r q = (cutOf C.ctl S).mem r q := by rw [hc]
  simp only [relocState] at h2
  show E.eval (envOf S) (E.reloc ρ (C.res.mem r (q - ρ.wshift r))) = S.mem r q
  rw [show C.res.mem r (q - ρ.wshift r) = C.cut.mem r (q - ρ.wshift r) from h1]
  show E.eval (envOf S) (E.reloc ρ ((cutOf C.ctl C.sc).mem r (q - ρ.wshift r))) = S.mem r q
  rw [h2]
  show E.eval (envOf S) (cutVar C.ctl S (memVar r q)) = S.mem r q
  rw [eval_cutVar, envOf_mem]

end SliceCert

/-! ## Identity and composition of relocations -/

/-- No relocation. -/
def Reloc.id : Reloc := ⟨fun _ => 0⟩

theorem Reloc.id_ok : Reloc.id.ok := by
  refine ⟨rfl, rfl, rfl, fun r => ⟨by simp [Reloc.id], by simp [Reloc.id]⟩⟩

theorem Reloc.id_within (B : Int) (hB : B ≤ 2 ^ 55) : Reloc.id.within B := by
  intro r; simp only [Reloc.id]; omega

theorem Reloc.id_var (i : Nat) : Reloc.id.var i = i := by
  by_cases h : i < 288
  · exact Reloc.var_lt _ i h
  · simp only [Reloc.var, h, ↓reduceIte, Reloc.wshift, Reloc.id]
    simp only [Int.zero_ediv, Int.add_zero]
    exact memVar_region_index i (by omega)

theorem E.reloc_id (e : E) : e.reloc Reloc.id = e := by
  induction e with
  | var i => simp only [E.reloc, Reloc.id_var]
  | const v => rfl
  | ptr a => simp only [E.reloc, Reloc.addr, Reloc.id, Int.add_zero]
  | xor a b iha ihb => simp only [E.reloc, iha, ihb]
  | and a b iha ihb => simp only [E.reloc, iha, ihb]
  | or a b iha ihb => simp only [E.reloc, iha, ihb]
  | not a ih => simp only [E.reloc, ih]
  | shl a n ih => simp only [E.reloc, ih]
  | shr a n ih => simp only [E.reloc, ih]
  | rol a n ih => simp only [E.reloc, ih]
  | add a b iha ihb => simp only [E.reloc, iha, ihb]
  | ternlog imm a b c iha ihb ihc => simp only [E.reloc, iha, ihb, ihc]

theorem Reloc.id_wshift (r : Region) : Reloc.id.wshift r = 0 := by
  simp only [Reloc.wshift, Reloc.id]; rfl

theorem relocState_id (s : State E) : relocState Reloc.id s = s := by
  cases s with
  | mk v g gd k zf cf nf vf vl mem pc depth err halted tail =>
    simp only [relocState, State.mk.injEq, true_and, and_true]
    refine ⟨?_, ?_, ?_⟩
    · apply Vector.ext; intro r hr; apply Vector.ext; intro l hl
      simp only [Vector.getElem_map, E.reloc_id]
    · apply Vector.ext; intro n hn
      simp only [Vector.getElem_map, E.reloc_id]
    · funext r q
      rw [Reloc.id_wshift, Int.sub_zero, E.reloc_id]

/-- Two relocations one after the other. -/
def Reloc.add (ρ σ : Reloc) : Reloc := ⟨fun r => ρ.δ r + σ.δ r⟩

theorem Reloc.add_ok (ρ σ : Reloc) (hρ : ρ.ok) (hσ : σ.ok) : (ρ.add σ).ok := by
  obtain ⟨a1, a2, a3, a4⟩ := hρ
  obtain ⟨b1, b2, b3, b4⟩ := hσ
  refine ⟨by simp [Reloc.add, a1, b1], by simp [Reloc.add, a2, b2], by simp [Reloc.add, a3, b3], fun r => ?_⟩
  obtain ⟨c1, c2⟩ := a4 r
  obtain ⟨d1, d2⟩ := b4 r
  exact ⟨by simp only [Reloc.add]; omega, Int.dvd_add c2 d2⟩

theorem Reloc.add_wshift (ρ σ : Reloc) (hρ : ρ.ok) (hσ : σ.ok) (r : Region) :
    (ρ.add σ).wshift r = ρ.wshift r + σ.wshift r := by
  have h1 := ρ.δ_eq hρ r
  have h2 := σ.δ_eq hσ r
  simp only [Reloc.wshift, Reloc.add] at *
  omega

theorem Reloc.add_var (ρ σ : Reloc) (hρ : ρ.ok) (hσ : σ.ok) (i : Nat) : (ρ.add σ).var i = ρ.var (σ.var i) := by
  by_cases h : i < 288
  · rw [Reloc.var_lt _ i h, Reloc.var_lt _ i h, Reloc.var_lt _ i h]
  · have hge := memVar_ge (memVarRegion i) (memVarIndex i + σ.wshift (memVarRegion i))
    simp only [Reloc.var, h, ↓reduceIte, show ¬ memVar (memVarRegion i) (memVarIndex i + σ.wshift (memVarRegion i)) < 288 by omega,
      memVarRegion_memVar, memVarIndex_memVar, Reloc.add_wshift ρ σ hρ hσ]
    congr 1; omega

theorem E.reloc_add (ρ σ : Reloc) (hρ : ρ.ok) (hσ : σ.ok) (e : E) : (e.reloc σ).reloc ρ = e.reloc (ρ.add σ) := by
  induction e with
  | var i => simp only [E.reloc, Reloc.add_var ρ σ hρ hσ]
  | const v => rfl
  | ptr a => simp only [E.reloc, Reloc.addr, Reloc.add, E.ptr.injEq]; simp only [Addr.mk.injEq, true_and]; omega
  | xor a b iha ihb => simp only [E.reloc, iha, ihb]
  | and a b iha ihb => simp only [E.reloc, iha, ihb]
  | or a b iha ihb => simp only [E.reloc, iha, ihb]
  | not a ih => simp only [E.reloc, ih]
  | shl a n ih => simp only [E.reloc, ih]
  | shr a n ih => simp only [E.reloc, ih]
  | rol a n ih => simp only [E.reloc, ih]
  | add a b iha ihb => simp only [E.reloc, iha, ihb]
  | ternlog imm a b c iha ihb ihc => simp only [E.reloc, iha, ihb, ihc]

theorem relocState_add (ρ σ : Reloc) (hρ : ρ.ok) (hσ : σ.ok) (s : State E) :
    relocState ρ (relocState σ s) = relocState (ρ.add σ) s := by
  cases s with
  | mk v g gd k zf cf nf vf vl mem pc depth err halted tail =>
    simp only [relocState, State.mk.injEq, true_and, and_true]
    refine ⟨?_, ?_, ?_⟩
    · apply Vector.ext; intro r hr; apply Vector.ext; intro l hl
      simp only [Vector.getElem_map, E.reloc_add ρ σ hρ hσ]
    · apply Vector.ext; intro n hn
      simp only [Vector.getElem_map, E.reloc_add ρ σ hρ hσ]
    · funext r q
      rw [E.reloc_add ρ σ hρ hσ, Reloc.add_wshift ρ σ hρ hσ]
      congr 2; omega

end Keccaktree.Asm
