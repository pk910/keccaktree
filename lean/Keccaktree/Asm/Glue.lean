import Keccaktree.Asm.Iter
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Glue between segments

Reading the control part and the control words of a concrete state off a cut
equation `relocState ρ (cutOf ctl sc) = cutOf ctl S`, and the cut of a state after
the concrete count steps (a flag, the program counter, a memory word outside the
control words).
-/
namespace Keccaktree.Asm
open X86

set_option maxRecDepth 100000 in
theorem readVar_cutOf (ctl : List Nat) (s : State (BitVec 64)) (v : Nat) : readVar (cutOf ctl s) v = cutVar ctl s v := by
  unfold readVar
  by_cases h1 : v < 256
  · have h2 : v / 8 < 32 := by omega
    have h3 : v % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [h1, ↓reduceIte, cutOf, Vector.getD, Array.getD, Vector.size_toArray, h2, h3, ↓reduceDIte,
      Array.getInternal_eq_getElem, Vector.getElem_toArray, Vector.getElem_ofFn]
    congr 1; simp only [regVar]; omega
  · by_cases h2 : v < 288
    · have h3 : v - 256 < 32 := by omega
      simp only [h1, h2, ↓reduceIte, cutOf, Vector.getD, Array.getD, Vector.size_toArray, h3, ↓reduceDIte,
        Array.getInternal_eq_getElem, Vector.getElem_toArray, Vector.getElem_ofFn]
      congr 1; simp only [gdVar]; omega
    · simp only [h1, h2, ↓reduceIte]
      show cutVar ctl s (memVar (memVarRegion v) (memVarIndex v)) = cutVar ctl s v
      rw [memVar_region_index v (by omega)]

theorem cut_fields (ρ : Reloc) (ctl : List Nat) (sc S : State (BitVec 64)) (h : relocState ρ (cutOf ctl sc) = cutOf ctl S) :
    S.g = sc.g ∧ S.k = sc.k ∧ S.zf = sc.zf ∧ S.cf = sc.cf ∧ S.nf = sc.nf ∧ S.vf = sc.vf ∧ S.vl = sc.vl ∧
      S.pc = sc.pc ∧ S.depth = sc.depth := by
  have e1 := congrArg State.g h; have e2 := congrArg State.k h; have e3 := congrArg State.zf h
  have e4 := congrArg State.cf h; have e5 := congrArg State.nf h; have e6 := congrArg State.vf h
  have e7 := congrArg State.vl h; have e8 := congrArg State.pc h; have e9 := congrArg State.depth h
  simp only [relocState, cutOf] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  exact ⟨e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm, e7.symm, e8.symm, e9.symm⟩

/-- A control word of a register or a stack cell, read off a relocated cut. -/
theorem cut_word (ρ : Reloc) (hρ : ρ.ok) (ctl : List Nat) (sc S : State (BitVec 64)) (h : relocState ρ (cutOf ctl sc) = cutOf ctl S)
    (v : Nat) (hv : v < 288 ∨ memVarRegion v = rStack) :
    cutVar ctl S v = E.reloc ρ (cutVar ctl sc v) := by
  have hvar : ρ.var v = v := by
    rcases hv with hv | hv
    · exact Reloc.var_lt ρ v hv
    · by_cases hlt : v < 288
      · exact Reloc.var_lt ρ v hlt
      · simp only [Reloc.var, hlt, ↓reduceIte, hv, SliceCert.stack_wshift ρ hρ, Int.add_zero]
        rw [← hv]; exact memVar_region_index v (by omega)
  have := congrArg (fun t => readVar t v) h
  have e1 : readVar (relocState ρ (cutOf ctl sc)) v = E.reloc ρ (cutVar ctl sc v) := by
    have := readVar_relocState_var ρ (cutOf ctl sc) v
    rw [hvar, readVar_cutOf] at this; exact this
  rw [e1, readVar_cutOf] at this
  exact this.symm

/-- The value of a pointer control word. -/
theorem cut_ptr (ctl : List Nat) (S : State (BitVec 64)) (v : Nat) (hv : v ∈ ctl) (a : Addr)
    (h : cutVar ctl S v = .ptr a) : envOf S v = gprWord a := by
  have hc : ctl.contains v = true := List.contains_iff_mem.mpr hv
  simp only [cutVar, hc, ↓reduceIte] at h
  split at h
  · rename_i hf
    cases h
    exact hf.2.symm
  · cases h

/-- The value of a number control word. -/
theorem cut_const (ctl : List Nat) (S : State (BitVec 64)) (v : Nat) (hv : v ∈ ctl) (w : BitVec 64)
    (h : cutVar ctl S v = .const w) : envOf S v = w := by
  have hc : ctl.contains v = true := List.contains_iff_mem.mpr hv
  simp only [cutVar, hc, ↓reduceIte] at h
  split at h
  · cases h
  · cases h; rfl

theorem cutOf_upd_zf_pc (ctl : List Nat) (S : State (BitVec 64)) (z : Bool) (p : Nat) :
    cutOf ctl { S with zf := z, pc := p } = { cutOf ctl S with zf := z, pc := p } := rfl

theorem envOf_memStore_other (S : State (BitVec 64)) (r : Region) (q : Int) (w : BitVec 64) (v : Nat)
    (hv : v ≠ memVar r q) : envOf { S with mem := memStore S.mem r q w } v = envOf S v := by
  unfold envOf
  split
  · rfl
  · split
    · rfl
    · simp only [memStore]
      have : ¬ (memVarRegion v = r ∧ memVarIndex v = q) := by
        intro hc; apply hv
        rw [← hc.1, ← hc.2]; exact (memVar_region_index v (by omega)).symm
      simp only [this, ↓reduceIte]

/-- Changing a memory word outside the control words keeps the cut. -/
theorem cutOf_memStore (ctl : List Nat) (S : State (BitVec 64)) (r : Region) (q : Int) (w : BitVec 64)
    (hn : memVar r q ∉ ctl) : cutOf ctl { S with mem := memStore S.mem r q w } = cutOf ctl S := by
  have hcv : ∀ v, cutVar ctl { S with mem := memStore S.mem r q w } v = cutVar ctl S v := by
    intro v
    unfold cutVar
    split
    · rename_i hc
      have hv : v ≠ memVar r q := by
        intro he; subst he; exact hn (List.contains_iff_mem.mp hc)
      rw [envOf_memStore_other S r q w v hv]
    · rfl
  simp only [cutOf, hcv]

theorem relocState_upd_zf_pc (ρ : Reloc) (s : State E) (z : Bool) (p : Nat) :
    relocState ρ { s with zf := z, pc := p } = { relocState ρ s with zf := z, pc := p } := rfl

end Keccaktree.Asm
