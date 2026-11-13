import Keccaktree.Asm.ArmHom
import Keccaktree.Asm.Reloc
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
/-!
The AArch64 semantics commute with relocation (`Arm.exec_reloc`): `Arm.isaReloc`.
-/
namespace Keccaktree.Asm.Arm
open Keccaktree.Asm Keccaktree.Asm.X86
open LaneOps

/-- The lane values an instruction decodes as addresses: its base / count register. -/
def decodes (rodata : Array (BitVec 64)) (i : Instr) (s : State E) : List E :=
  match i with
  | .add _ a _ | .sub _ a _ | .subs _ a _ | .cmp a _ | .cbz a _ => [s.getGD a]
  | .ldr _ b _ | .str _ b _ | .ldp _ _ b _ _ | .stp _ _ b _ _ => [s.getGD b]
  | _ => []

section
variable (ρ : Reloc) (hρ : ρ.ok)

theorem lane_reloc (s : State E) (n l : Nat) : lane (relocState ρ s) n l = E.reloc ρ (lane s n l) := by
  simp only [lane, getV_reloc, getD_reloc]

theorem setLanes_reloc (s : State E) (n : Nat) (lo hi : E) :
    setLanes (relocState ρ s) n (E.reloc ρ lo) (E.reloc ρ hi) = relocState ρ (setLanes s n lo hi) := by
  simp only [setLanes, State.setV, relocState, Vector.map_setIfInBounds]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  split
  · rfl
  · split <;> rfl

theorem setLanes_reloc' (s : State E) (n : Nat) (lo hi lo' hi' : E) (hlo : E.reloc ρ lo = lo') (hhi : E.reloc ρ hi = hi') :
    setLanes (relocState ρ s) n lo' hi' = relocState ρ (setLanes s n lo hi) := by
  subst hlo hhi; exact setLanes_reloc ρ s n lo hi

theorem rotr_reloc (x : E) (n : Nat) : E.reloc ρ (rotr x n) = rotr (E.reloc ρ x) n := rfl

include hρ in
theorem tblWord_reloc (lo hi : E) (cw : BitVec 64) : tblWord (E.reloc ρ lo) (E.reloc ρ hi) cw = E.reloc ρ (tblWord lo hi cw) := by
  simp only [tblWord]
  rw [X86.foldl_hom (E.reloc ρ) _ _ ?_ _ _]
  · rfl
  intro acc i
  try dsimp only
  split
  · rfl
  · split <;> rfl

theorem next_reloc' (s : State E) : next (relocState ρ s) = relocState ρ (next s) := rfl
theorem setFlags_reloc (s : State E) (a b : Int) : setFlags (relocState ρ s) a b = relocState ρ (setFlags s a b) := rfl
theorem condHolds_reloc' (s : State E) (c : Cond) : condHolds (relocState ρ s) c = condHolds s c := by cases c <;> rfl

theorem setX_reloc' (s : State E) (n : Nat) (a : Addr) : setX (relocState ρ s) n (ρ.addr a) = relocState ρ (setX s n a) := by
  simp only [setX]; exact setGD_reloc' ρ s n _ _ rfl

include hρ in
theorem gx_reloc' (s : State E) (n : Nat) (a : Addr) (h : gx s n = some a) (hok : (s.getGD n).relocOk ρ) :
    gx (relocState ρ s) n = some (ρ.addr a) := by
  simp only [gx, getGD_reloc] at h ⊢
  exact reloc_asAddr ρ hρ _ a h hok

include hρ in
theorem addr_reloc (s : State E) (base : Nat) (off : Int) (a : Addr) (h : addr s base off = some a)
    (hok : (s.getGD base).relocOk ρ) : addr (relocState ρ s) base off = some (ρ.addr a) := by
  simp only [addr] at h ⊢
  rcases hx : gx s base with _ | x
  · simp [hx] at h
  · rw [gx_reloc' ρ hρ _ _ _ hx hok]
    simp only [hx, Option.map_some, Option.some.injEq] at h ⊢
    rw [← h]; exact (addr_mk_add ρ x off)

theorem regWords_reloc (s : State E) (r : LReg) : regWords (relocState ρ s) r = (regWords s r).map (E.reloc ρ) := by
  cases r <;> simp [regWords, lane_reloc, getGD_reloc]

theorem loadReg_reloc (s : State E) (r : LReg) (ws : List E) :
    loadReg (relocState ρ s) r (ws.map (E.reloc ρ)) = relocState ρ (loadReg s r ws) := by
  cases r with
  | q n => simp only [loadReg, getD_reloc, setLanes_reloc]
  | d n => simp only [loadReg, getD_reloc, lane_reloc, setLanes_reloc]
  | x n => simp only [loadReg, getD_reloc, setGD_reloc]

/-- The vector instructions: `next (setLanes ..)` with lane functions built from the lane operations. -/
syntax "arm_vec_reloc" : tactic
macro_rules
  | `(tactic| arm_vec_reloc) => `(tactic| (
      rw [← next_reloc']
      exact congrArg next (setLanes_reloc' ρ _ _ _ _ _ _
        (by (try split) <;> simp [lane_reloc, reloc_xor, reloc_and, reloc_or, reloc_not, reloc_shl, reloc_shr, reloc_rol,
          reloc_add, reloc_const, rotr_reloc])
        (by (try split) <;> simp [lane_reloc, reloc_xor, reloc_and, reloc_or, reloc_not, reloc_shl, reloc_shr, reloc_rol,
          reloc_add, reloc_const, rotr_reloc]))))

include hρ in
/-- **`exec` commutes with relocation** (AArch64). -/
theorem exec_reloc (rodata : Array (BitVec 64)) (i : Instr) (st : State E) (hne : (exec rodata i st).err = false)
    (hok : ∀ e ∈ decodes rodata i st, E.relocOk ρ e) :
    exec rodata i (relocState ρ st) = relocState ρ (exec rodata i st) := by
  cases hh : st.halted
  · cases i with
    | eor d a b => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec_reloc
    | bic d a b => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec_reloc
    | eor3 d a b c => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, vop3]; arm_vec_reloc
    | bcax d a b c => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, vop3]; arm_vec_reloc
    | rax1 d a b => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec_reloc
    | xar d a b n => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec_reloc
    | shl d a n => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, vop1]; arm_vec_reloc
    | sri d a n => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; arm_vec_reloc
    | addv d a b => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec_reloc
    | tbl d a b =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, lane_reloc] at hne ⊢
      rw [reloc_asConst ρ hρ, reloc_asConst ρ hρ]
      rcases h0 : LaneOps.asConst (lane st b 0) with _ | c0
      · simp only [h0, fail_err'] at hne; exact absurd hne (by decide)
      · rcases h1 : LaneOps.asConst (lane st b 1) with _ | c1
        · simp only [h0, h1, fail_err'] at hne; exact absurd hne (by decide)
        · simp only
          rw [← next_reloc']
          exact congrArg next (setLanes_reloc' ρ _ _ _ _ _ _ (tblWord_reloc ρ hρ _ _ _).symm (tblWord_reloc ρ hρ _ _ _).symm)
    | zip1 d a b => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; arm_vec_reloc
    | zip2 d a b => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; arm_vec_reloc
    | movv d a => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; arm_vec_reloc
    | movi0 d => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; arm_vec_reloc
    | eorx d a b n =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setGD_reloc' ρ _ _ _ _ (by simp [getGD_reloc, reloc_xor, rotr_reloc]))
    | bicx d a b n =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setGD_reloc' ρ _ _ _ _ (by simp [getGD_reloc, reloc_and, reloc_not, rotr_reloc]))
    | rorx d a n =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setGD_reloc' ρ _ _ _ _ (by simp [getGD_reloc, rotr_reloc]))
    | movx d a =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setGD_reloc' ρ _ _ _ _ (by simp [getGD_reloc]))
    | movi d imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setGD_reloc' ρ _ _ _ _ rfl)
    | add d a imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_reloc' ρ hρ _ _ _ hx (hok _ (by simp [decodes]))]
        rw [addr_mk_add, setX_reloc', next_reloc']
    | sub d a imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_reloc' ρ hρ _ _ _ hx (hok _ (by simp [decodes]))]
        rw [addr_mk_sub, setX_reloc', next_reloc']
    | subs d a imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_reloc' ρ hρ _ _ _ hx (hok _ (by simp [decodes]))]
        by_cases h0 : x.region = 0
        · rw [Reloc.addr_region0 ρ hρ x h0]
          simp only [h0, ↓reduceIte]
          have e : setX (relocState ρ st) d ⟨0, x.off - imm⟩ = relocState ρ (setX st d ⟨0, x.off - imm⟩) := by
            rw [← setX_reloc' ρ _ _ ⟨0, x.off - imm⟩, Reloc.addr_region0 ρ hρ _ rfl]
          rw [e]; rfl
        · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
    | cmp a imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_reloc' ρ hρ _ _ _ hx (hok _ (by simp [decodes]))]
        by_cases h0 : x.region = 0
        · rw [Reloc.addr_region0 ρ hρ x h0]; simp only [h0, ↓reduceIte]; rfl
        · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
    | csel d a b c =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, condHolds_reloc']
      rw [← next_reloc']; exact congrArg next (setGD_reloc' ρ _ _ _ _ (by split <;> simp [getGD_reloc]))
    | ldr r base off =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), loadWords_reloc ρ hρ]
        rcases hl : st.loadWords rodata a (regSize r / 8).toNat with _ | ws
        · rfl
        · simp only [Option.map_some, loadReg_reloc, next_reloc']
    | ldrlit r lo hi =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      have e : loadReg (relocState ρ st) r [const lo, const hi] = relocState ρ (loadReg st r [const lo, const hi]) :=
        loadReg_reloc ρ st r [const lo, const hi]
      rw [e, next_reloc']
    | str r base off =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), regWords_reloc, storeWords_reloc ρ hρ]
        rcases hs : st.storeWords a (regWords st r) with _ | s'
        · rfl
        · simp only [Option.map_some, next_reloc']
    | ldp r1 r2 base off wb =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base (if wb = 2 then 0 else off) with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), loadWords_reloc ρ hρ]
        rcases hl : st.loadWords rodata a ((regSize r1 + regSize r2) / 8).toNat with _ | ws
        · rfl
        · simp only [Option.map_some, ← List.map_take, ← List.map_drop, loadReg_reloc]
          split
          · rw [next_reloc']
          · rw [addr_mk_add, setX_reloc', next_reloc']
    | stp r1 r2 base off wb =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base (if wb = 2 then 0 else off) with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), regWords_reloc, ← List.map_append,
          storeWords_reloc ρ hρ]
        rcases hs : st.storeWords a (regWords st r1 ++ regWords st r2) with _ | s'
        · rfl
        · simp only [Option.map_some]
          split
          · rw [next_reloc']
          · rw [addr_mk_add, setX_reloc', next_reloc']
    | cbz a t =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_reloc' ρ hρ _ _ _ hx (hok _ (by simp [decodes]))]
        by_cases h0 : x.region = 0
        · rw [Reloc.addr_region0 ρ hρ x h0]; simp only [h0, ↓reduceIte]; rfl
        · simp only [Reloc.addr_region, h0, ↓reduceIte, fail_reloc]
    | bcond c t => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, condHolds_reloc']; rfl
    | b t => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; rfl
    | tailcall name => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; rfl
    | ret => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; rfl
    | nop => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, next_reloc']
    | data => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, fail_reloc]
  · simp [exec, relocState, hh]

end

/-- The AArch64 instruction set is relocatable. -/
def isaReloc : isa.Relocatable where
  decodes := decodes
  exec_reloc := fun ρ hρ rodata i st hne hok => exec_reloc ρ hρ rodata i st hne hok

end Keccaktree.Asm.Arm
