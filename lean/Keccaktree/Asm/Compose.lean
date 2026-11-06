import Keccaktree.Asm.Trace
import Keccaktree.Asm.Cut
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
Chaining slices.  Between slices the concrete state is viewed through fresh
variables: `cutOf s` is the symbolic cut state with `s`'s control part and a
variable at every register lane and memory word, `envOf s` the value of
every such variable in `s`.  Evaluating the cut state under `envOf s` gives
`s` back exactly (`eval_cutOf`), and with `execTrace_map`, running a slice on
the concrete state is evaluating the slice's symbolic result under `envOf s`
(`execTrace_cut`).
-/
namespace Keccaktree.Asm.X86
open Keccaktree.Asm

/-- A memory literal for the closed control states the generated proofs name:
the given (region, word, value) cells, zero elsewhere. -/
def memLit (l : List (Nat × Int × BitVec 64)) (r : Region) (q : Int) : BitVec 64 :=
  match l.find? (fun (r', q', _) => r' == r.val && q' == q) with
  | some (_, _, w) => w
  | none => 0

/-- The value of cut variable `i` in a concrete state. -/
def envOf (s : State (BitVec 64)) (i : Nat) : BitVec 64 :=
  if i < 256 then (s.getV (i / 8)).getD (i % 8) 0
  else if i < 288 then s.gd.getD (i - 256) 0
  else s.mem (memVarRegion i) (memVarIndex i)

/-- A cut variable: the constant it holds in `s` if it is one of the control
words `ctl` (pointers and counts kept in data registers or on the stack, which
the slice's address arithmetic needs to see), a fresh variable otherwise. -/
def cutVar (ctl : List Nat) (s : State (BitVec 64)) (i : Nat) : E :=
  if ctl.contains i then .const (envOf s i) else .var i

/-- The symbolic state at a cut: the control part of `s`, variables elsewhere. -/
def cutOf (ctl : List Nat) (s : State (BitVec 64)) : State E :=
  { v := Vector.ofFn fun r : Fin 32 => Vector.ofFn fun l : Fin 8 => cutVar ctl s (regVar r l)
    g := s.g, gd := Vector.ofFn fun n : Fin 32 => cutVar ctl s (gdVar n)
    k := s.k, zf := s.zf, cf := s.cf, nf := s.nf, vf := s.vf, vl := s.vl
    mem := fun r q => cutVar ctl s (memVar r q)
    pc := s.pc, depth := s.depth, err := false, halted := false, tail := none }

theorem eval_cutVar (ctl : List Nat) (s : State (BitVec 64)) (i : Nat) :
    E.eval (envOf s) (cutVar ctl s i) = envOf s i := by
  unfold cutVar; split <;> simp only [E.eval]

theorem envOf_reg (s : State (BitVec 64)) (r : Fin 32) (l : Fin 8) : envOf s (regVar r l) = s.v[r][l] := by
  simp only [envOf, regVar]
  have hlt : 8 * r.val + l.val < 256 := by omega
  simp only [hlt, ↓reduceIte, State.getV]
  have h1 : (8 * r.val + l.val) / 8 = r.val := by omega
  have h2 : (8 * r.val + l.val) % 8 = l.val := by omega
  simp [h1, h2, Vector.getD, List.getD_eq_getElem?_getD]

theorem envOf_mem (s : State (BitVec 64)) (r : Region) (q : Int) : envOf s (memVar r q) = s.mem r q := by
  have hn : ¬ (memVar r q < 256) := by have := memVar_ge r q; omega
  have hn2 : ¬ (memVar r q < 288) := by have := memVar_ge r q; omega
  simp only [envOf, hn, hn2, ↓reduceIte, memVarRegion_memVar, memVarIndex_memVar]

theorem envOf_gd (s : State (BitVec 64)) (n : Fin 32) : envOf s (gdVar n) = s.gd[n] := by
  have h1 : ¬ (gdVar n < 256) := by simp only [gdVar]; omega
  have h2 : gdVar n < 288 := by simp only [gdVar]; omega
  simp only [envOf, gdVar] at h1 h2 ⊢
  simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left, Vector.getD, List.getD_eq_getElem?_getD]
  simp [Vector.getElem?_eq_getElem n.isLt]

/-- A concrete state is the evaluation of its own cut (registers and memory;
the control part of the cut is `s`'s with the status flags cleared). -/
theorem eval_cutOf_v (ctl : List Nat) (s : State (BitVec 64)) :
    (mapState (E.eval (envOf s)) (cutOf ctl s)).v = s.v := by
  apply Vector.ext; intro r hr; apply Vector.ext; intro l hl
  simp only [mapState, cutOf, Vector.getElem_map, Vector.getElem_ofFn, eval_cutVar]
  exact envOf_reg _ ⟨r, hr⟩ ⟨l, hl⟩

theorem eval_cutOf_gd (ctl : List Nat) (s : State (BitVec 64)) :
    (mapState (E.eval (envOf s)) (cutOf ctl s)).gd = s.gd := by
  apply Vector.ext; intro n hn
  simp only [mapState, cutOf, Vector.getElem_map, Vector.getElem_ofFn, eval_cutVar]
  exact envOf_gd _ ⟨n, hn⟩

theorem eval_cutOf_mem (ctl : List Nat) (s : State (BitVec 64)) :
    (mapState (E.eval (envOf s)) (cutOf ctl s)).mem = s.mem := by
  funext r q
  simp only [mapState, cutOf, eval_cutVar]
  exact envOf_mem _ r q

theorem eval_cutOf (ctl : List Nat) (s : State (BitVec 64)) (hs : s.err = false ∧ s.halted = false ∧ s.tail = none) :
    mapState (E.eval (envOf s)) (cutOf ctl s) = s := by
  obtain ⟨he, hh, ht⟩ := hs
  have hv := eval_cutOf_v ctl s
  have hm := eval_cutOf_mem ctl s
  have hd := eval_cutOf_gd ctl s
  cases s with
  | mk v g gd k zf cf nf vf vl mem pc depth err halted tail =>
    simp only at he hh ht hv hm hd
    subst he hh ht
    simp only [mapState, cutOf] at hv hm hd ⊢
    rw [hv, hm, hd]

/-- Reading a cut variable off an evaluated symbolic state is evaluating the
symbolic lane there. -/
theorem envOf_mapState (env : Nat → BitVec 64) (t : State E) (i : Nat) :
    envOf (mapState (E.eval env) t) i = E.eval env (readVar t i) := by
  unfold envOf readVar
  split
  case isFalse =>
    split
    · by_cases h : i - 256 < 32
      · simp only [mapState, Vector.getD, Array.getD, Vector.size_toArray, h, ↓reduceDIte,
          Array.getInternal_eq_getElem, Vector.getElem_toArray, Vector.getElem_map]
      · simp only [mapState, Vector.getD, Array.getD, Vector.size_toArray, h, ↓reduceDIte, E.eval]
    · rfl
  case isTrue =>
    have hi : i / 8 < 32 := by omega
    have hl : i % 8 < 8 := by omega
    simp only [State.getV, mapState, Vector.getD, Array.getD, Vector.size_toArray, hi, hl, ↓reduceDIte,
      Array.getInternal_eq_getElem, Vector.getElem_toArray, Vector.getElem_map, Vector.toList_map,
      List.getD_eq_getElem?_getD, List.getElem?_map, Vector.getElem?_toList, Vector.getElem?_eq_getElem hl,
      Option.map_some, Option.getD_some]

/-- Running a slice on a concrete state is evaluating the slice's symbolic
result under the state's cut environment, provided the concrete state's
control part is the cut's and the symbolic run does not fail. -/
theorem execTrace_cut (isa : Isa) (rodata : Array (BitVec 64)) (slice : List isa.Instr) (ctl : List Nat)
    (cut : State E) (S : State (BitVec 64))
    (hc : cutOf ctl S = cut) (hs : S.err = false ∧ S.halted = false ∧ S.tail = none)
    (hne : (isa.execTrace rodata slice cut).err = false) :
    isa.execTrace rodata slice S = mapState (E.eval (envOf S)) (isa.execTrace rodata slice cut) := by
  have h := isa.execTrace_map (E.eval_isHom (envOf S)) rodata slice cut hne
  rw [← h, ← hc, eval_cutOf ctl S hs]

end Keccaktree.Asm.X86
