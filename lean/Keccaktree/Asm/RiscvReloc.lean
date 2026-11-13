import Keccaktree.Asm.RiscvHom
import Keccaktree.Asm.ArmReloc
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
/-!
The RISC-V semantics commute with relocation (`Riscv.exec_reloc`): `Riscv.isaReloc vlmax`.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next getGD_map setGD_map setGD_map' gx_map_some setX_map next_map condHolds_map
open Keccaktree.Asm.Arm (gx setX withX addr withAddr addr_reloc setX_reloc')
open LaneOps

/-- The lane values an instruction decodes as addresses. -/
def decodes (rodata : Array (BitVec 64)) (i : Instr) (s : State E) : List E :=
  match i with
  | .ld _ b _ | .sd _ b _ | .vlseg _ b _ | .vsseg _ b _ => [s.getGD b]
  | .lbu _ b _ | .sb _ b _ | .vle8 _ b | .vse8 _ b => [s.getGD b]
  | .br _ a b _ => [getR s a, getR s b]
  | _ => []

section
variable (ρ : Reloc) (hρ : ρ.ok)

theorem getR_reloc (s : State E) (n : Nat) : getR (relocState ρ s) n = E.reloc ρ (getR s n) := by
  unfold getR; split
  · rfl
  · exact getGD_reloc ρ s n

theorem setR_reloc' (s : State E) (n : Nat) (x x' : E) (hx : E.reloc ρ x = x') :
    setR (relocState ρ s) n x' = relocState ρ (setR s n x) := by
  unfold setR; split
  · rfl
  · exact setGD_reloc' ρ s n x x' hx

theorem lane_reloc (s : State E) (n l : Nat) : lane (relocState ρ s) n l = E.reloc ρ (lane s n l) := by
  simp only [lane, getV_reloc, getD_reloc]

theorem setActive_reloc' (s : State E) (d : Nat) (g g' : Nat → E) (hg : ∀ l, E.reloc ρ (g l) = g' l) :
    setActive (relocState ρ s) d g' = relocState ρ (setActive s d g) := by
  simp only [setActive, State.setV, relocState, Vector.map_setIfInBounds]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  by_cases hi : i < s.vl
  · simp only [hi, ↓reduceIte]; exact (hg i).symm
  · simp only [hi, ↓reduceIte]
    show lane (relocState ρ s) d i = E.reloc ρ (lane s d i)
    exact lane_reloc ρ s d i

theorem setLanes_reloc' (s : State E) (d c : Nat) (g g' : Nat → E) (hg : ∀ l, E.reloc ρ (g l) = g' l) :
    setLanes (relocState ρ s) d c g' = relocState ρ (setLanes s d c g) := by
  simp only [setLanes, State.setV, relocState, Vector.map_setIfInBounds]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  by_cases hi : i < c
  · simp only [hi, ↓reduceIte]; exact (hg i).symm
  · simp only [hi, ↓reduceIte]
    show lane (relocState ρ s) d i = E.reloc ρ (lane s d i)
    exact lane_reloc ρ s d i

include hρ in
theorem setGroup_reloc (vlmax : Nat) (s : State E) (d : Nat) (ws : List E) (n : Nat) :
    setGroup vlmax (relocState ρ s) d (ws.map (E.reloc ρ)) n = relocState ρ (setGroup vlmax s d ws n) := by
  unfold setGroup
  exact (X86.foldl_hom (relocState ρ) _ _ (fun acc r => (setLanes_reloc' ρ acc (d + r) _ _ _
    (fun l => (getD_reloc ρ ws _).symm)).symm) _ _).symm

theorem groupWord_reloc (vlmax : Nat) (s : State E) (src j : Nat) :
    groupWord vlmax (relocState ρ s) src j = E.reloc ρ (groupWord vlmax s src j) := lane_reloc ρ s _ _

include hρ in
theorem wordOf_reloc (a : Addr) : wordOf (ρ.addr a) = ρ.addr (wordOf a) := by
  have h := Reloc.addr_mod8 ρ hρ a
  simp only [wordOf, Reloc.addr, Addr.mk.injEq, true_and] at h ⊢
  omega

include hρ in
theorem byteOf_reloc (a : Addr) : byteOf (ρ.addr a) = byteOf a := by
  simp only [byteOf, Reloc.addr_mod8 ρ hρ a]

include hρ in
theorem hiWord_reloc (a : Addr) (n : Nat) :
    (⟨(ρ.addr a).region, (wordOf (ρ.addr a)).off + 8 * n⟩ : Addr) = ρ.addr ⟨a.region, (wordOf a).off + 8 * n⟩ := by
  rw [wordOf_reloc ρ hρ]
  simp only [Reloc.addr, wordOf, Addr.mk.injEq, true_and]
  omega

include hρ in
theorem loadBytes_reloc (rodata : Array (BitVec 64)) (s : State E) (a : Addr) (n : Nat) :
    loadBytes rodata (relocState ρ s) (ρ.addr a) n = (loadBytes rodata s a n).map (List.map (E.reloc ρ)) := by
  unfold loadBytes
  rw [byteOf_reloc ρ hρ]
  split
  · exact loadWords_reloc ρ hρ rodata s a n
  · rw [wordOf_reloc ρ hρ, loadWords_reloc ρ hρ]
    rcases s.loadWords rodata (wordOf a) (n + 1) with _ | ws
    · rfl
    · simp only [Option.map_some, joinWords_map (relocLane ρ hρ)]

include hρ in
theorem storeBytes_reloc (rodata : Array (BitVec 64)) (s : State E) (a : Addr) (vs : List E) (n : Nat) :
    storeBytes rodata (relocState ρ s) (ρ.addr a) (vs.map (E.reloc ρ)) n = (storeBytes rodata s a vs n).map (relocState ρ) := by
  unfold storeBytes
  rw [byteOf_reloc ρ hρ]
  split
  · exact storeWords_reloc ρ hρ s a vs
  · rw [hiWord_reloc ρ hρ, wordOf_reloc ρ hρ, loadWords_reloc ρ hρ, loadWords_reloc ρ hρ]
    rcases s.loadWords rodata (wordOf a) 1 with _ | l1
    · rfl
    · rcases s.loadWords rodata ⟨a.region, (wordOf a).off + 8 * n⟩ 1 with _ | l2
      · rcases l1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
      · rcases l1 with _ | ⟨lo, _ | ⟨_, _⟩⟩ <;> rcases l2 with _ | ⟨hi, _ | ⟨_, _⟩⟩ <;> try rfl
        simp only [Option.map_some, List.map_cons, List.map_nil]
        rw [← splitWords_map (relocLane ρ hρ)]
        exact storeWords_reloc ρ hρ s _ _

theorem next_reloc' (s : State E) : next (relocState ρ s) = relocState ρ (next s) := rfl
@[simp] theorem vl_reloc' (s : State E) : (relocState ρ s).vl = s.vl := rfl
theorem fail_err'' (s : State E) : s.fail.err = true := rfl

theorem rotr_reloc (x : E) (n : Nat) : E.reloc ρ (rotr x n) = rotr (E.reloc ρ x) n := rfl
theorem sub_reloc (a b : E) : E.reloc ρ (sub a b) = sub (E.reloc ρ a) (E.reloc ρ b) := rfl
theorem op2_reloc (k : Op2) (a b : E) : E.reloc ρ (op2 k a b) = op2 k (E.reloc ρ a) (E.reloc ρ b) := by cases k <;> rfl
theorem opi_reloc (k : OpI) (a : E) (i : BitVec 64) : E.reloc ρ (opi k a i) = opi k (E.reloc ρ a) i := by cases k <;> rfl
theorem vop_reloc (k : VOp) (a b : E) : E.reloc ρ (vop k a b) = vop k (E.reloc ρ a) (E.reloc ρ b) := by cases k <;> rfl
theorem vsh_reloc (k : VSh) (a : E) (n : Nat) : E.reloc ρ (vsh k a n) = vsh k (E.reloc ρ a) n := by
  cases k <;> simp only [vsh] <;> (try split) <;> rfl

include hρ in
/-- **`exec` commutes with relocation** (RISC-V). -/
theorem exec_reloc (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (st : State E)
    (hne : (exec vlmax rodata i st).err = false) (hok : ∀ e ∈ decodes rodata i st, E.relocOk ρ e) :
    exec vlmax rodata i (relocState ρ st) = relocState ρ (exec vlmax rodata i st) := by
  cases hh : st.halted
  · cases i with
    | op d a b k =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setR_reloc' ρ _ _ _ _ (by simp [getR_reloc, op2_reloc]))
    | opi d a k imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setR_reloc' ρ _ _ _ _ (by simp [getR_reloc, opi_reloc]))
    | li d imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setR_reloc' ρ _ _ _ _ rfl)
    | mv d a =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setR_reloc' ρ _ _ _ _ (by simp [getR_reloc]))
    | not d a =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setR_reloc' ρ _ _ _ _ (by simp [getR_reloc]))
    | lea d a =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      by_cases h : a.region = rRodata
      · simp only [h, ↓reduceIte]
        have e : setX (relocState ρ st) d a = relocState ρ (setX st d a) := by
          conv => lhs; rw [← Reloc.addr_rodata ρ hρ a h]
          exact setX_reloc' ρ st d a
        rw [e, next_reloc']
      · simp only [h, ↓reduceIte, fail_reloc]
    | ld d base off =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), loadWords_reloc ρ hρ]
        rcases hl : st.loadWords rodata a 1 with _ | l
        · rfl
        · rcases l with _ | ⟨w, l⟩
          · rfl
          · rcases l with _ | ⟨w2, l⟩
            · simp only [Option.map_some, List.map_cons, List.map_nil]
              rw [← next_reloc']; exact congrArg next (setR_reloc' ρ _ _ _ _ rfl)
            · rfl
    | sd src base off =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), getR_reloc]
        rw [show [E.reloc ρ (getR st src)] = [getR st src].map (E.reloc ρ) from rfl, storeWords_reloc ρ hρ]
        rcases hs : st.storeWords a [getR st src] with _ | s'
        · rfl
        · simp only [Option.map_some, next_reloc']
    | br c a b t =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, getR_reloc] at hne ⊢
      rcases hx : LaneOps.asAddr (getR st a) with _ | x
      · simp only [hx, fail_err''] at hne; exact absurd hne (by decide)
      · rcases hy : LaneOps.asAddr (getR st b) with _ | y
        · simp only [hx, hy, fail_err''] at hne; exact absurd hne (by decide)
        · rw [reloc_asAddr ρ hρ _ _ hx (hok _ (by simp [decodes])), reloc_asAddr ρ hρ _ _ hy (hok _ (by simp [decodes]))]
          simp only [hx, hy, Reloc.addr_region]
          by_cases hr : x.region = y.region
          · simp only [hr, ↓reduceIte, Reloc.addr]
            have e : brHolds c (x.off + ρ.δ y.region) (y.off + ρ.δ y.region) = brHolds c x.off y.off := by
              have h1 : (x.off + ρ.δ y.region == y.off + ρ.δ y.region) = (x.off == y.off) := by
                have : (x.off + ρ.δ y.region = y.off + ρ.δ y.region) ↔ (x.off = y.off) := by omega
                rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact this
              cases c <;> simp only [brHolds, h1, bne, Int.add_le_add_iff_right]
            rw [e]; rfl
          · simp only [hr, ↓reduceIte, fail_reloc]
    | j t => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; rfl
    | ret => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]; rfl
    | nop => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, next_reloc']
    | unsupported name => simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, fail_reloc]
    | vsetvli d a =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, getR_reloc] at hne ⊢
      rw [reloc_asConst ρ hρ]
      rcases hx : LaneOps.asConst (getR st a) with _ | x
      · simp only [hx, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [hx]
        have e : setR (relocState ρ st) d (const (BitVec.ofNat 64 (min x.toNat vlmax))) =
            relocState ρ (setR st d (const (BitVec.ofNat 64 (min x.toNat vlmax)))) := setR_reloc' ρ st d _ _ rfl
        rw [e]; rfl
    | vop d a b k =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setActive_reloc' ρ _ _ _ _ (fun l => by simp [lane_reloc, vop_reloc]))
    | vnot d a =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setActive_reloc' ρ _ _ _ _ (fun l => by simp [lane_reloc]))
    | vshifti d a k imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setActive_reloc' ρ _ _ _ _ (fun l => by simp [lane_reloc, vsh_reloc]))
    | vshiftx d a k x =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, getR_reloc] at hne ⊢
      rw [reloc_asConst ρ hρ]
      rcases hx : LaneOps.asConst (getR st x) with _ | n
      · simp only [hx, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [hx]
        rw [← next_reloc']; exact congrArg next (setActive_reloc' ρ _ _ _ _ (fun l => by simp [lane_reloc, vsh_reloc]))
    | vxorx d a x =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setActive_reloc' ρ _ _ _ _ (fun l => by simp [lane_reloc, getR_reloc]))
    | vmvi d imm =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setActive_reloc' ρ _ _ _ _ (fun _ => rfl))
    | vmvx d x =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setActive_reloc' ρ _ _ _ _ (fun _ => (getR_reloc ρ _ _).symm))
    | vmvv d a =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte]
      rw [← next_reloc']; exact congrArg next (setActive_reloc' ρ _ _ _ _ (fun l => (lane_reloc ρ _ _ _).symm))
    | vlseg d base nf =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr, vl_reloc'] at hne ⊢
      rcases ha : addr st base 0 with _ | a
      · simp only [ha, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes]))]
        rw [loadWords_reloc ρ hρ]
        rcases hl : st.loadWords rodata a (nf * st.vl) with _ | ws
        · rfl
        · simp only [Option.map_some]
          rw [← next_reloc']; congr 1
          exact (X86.foldl_hom (relocState ρ) _ _ (fun acc i => (setActive_reloc' ρ acc (d + i) _ _ (fun l => (getD_reloc ρ ws _).symm)).symm) _ _).symm
    | vsseg src base nf =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr, vl_reloc'] at hne ⊢
      rcases ha : addr st base 0 with _ | a
      · simp only [ha, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), lane_reloc]
        have hw : (List.range (nf * st.vl)).map (fun q => E.reloc ρ (lane st (src + q % nf) (q / nf))) =
            ((List.range (nf * st.vl)).map fun q => lane st (src + q % nf) (q / nf)).map (E.reloc ρ) := by
          rw [List.map_map]; rfl
        rw [hw, storeWords_reloc ρ hρ]
        rcases hs : st.storeWords a ((List.range (nf * st.vl)).map fun q => lane st (src + q % nf) (q / nf)) with _ | s'
        · rfl
        · simp only [Option.map_some, next_reloc']
    | lbu d base off =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), wordOf_reloc ρ hρ, byteOf_reloc ρ hρ,
          loadWords_reloc ρ hρ]
        rcases hl : st.loadWords rodata (wordOf a) 1 with _ | l
        · rfl
        · rcases l with _ | ⟨w, _ | ⟨w2, l⟩⟩
          · rfl
          · simp only [Option.map_some, List.map_cons, List.map_nil]
            rw [← next_reloc']; exact congrArg next (setR_reloc' ρ _ _ _ _ rfl)
          · rfl
    | sb src base off =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), wordOf_reloc ρ hρ, byteOf_reloc ρ hρ,
          loadWords_reloc ρ hρ, getR_reloc]
        rcases hl : st.loadWords rodata (wordOf a) 1 with _ | l
        · rfl
        · rcases l with _ | ⟨w, _ | ⟨w2, l⟩⟩
          · rfl
          · simp only [Option.map_some, List.map_cons, List.map_nil]
            rw [← insByte_map (relocLane ρ hρ), show [E.reloc ρ (insByte w (getR st src) (byteOf a))] =
              [insByte w (getR st src) (byteOf a)].map (E.reloc ρ) from rfl, storeWords_reloc ρ hρ]
            rcases (st.storeWords (wordOf a) [insByte w (getR st src) (byteOf a)]) with _ | s'
            · rfl
            · simp only [Option.map_some, next_reloc']
          · rfl
    | vsetvlie8 d a lmul =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, getR_reloc] at hne ⊢
      rw [reloc_asConst ρ hρ]
      rcases hx : LaneOps.asConst (getR st a) with _ | x
      · simp only [hx, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [hx]
        split
        · have e : setR (relocState ρ st) d (const (BitVec.ofNat 64 x.toNat)) =
              relocState ρ (setR st d (const (BitVec.ofNat 64 x.toNat))) := setR_reloc' ρ st d _ _ rfl
          rw [e]; rfl
        · rfl
    | vle8 d base =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr, vl_reloc'] at hne ⊢
      rcases ha : addr st base 0 with _ | a
      · simp only [ha, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), loadBytes_reloc ρ hρ]
        split
        · rcases (loadBytes rodata st a (st.vl / 8)) with _ | ws
          · rfl
          · simp only [Option.map_some]
            rw [← next_reloc', setGroup_reloc ρ hρ]
        · rfl
    | vse8 src base =>
      simp only [exec, hh, halted_reloc, Bool.false_eq_true, ↓reduceIte, withAddr, vl_reloc'] at hne ⊢
      rcases ha : addr st base 0 with _ | a
      · simp only [ha, fail_err''] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_reloc ρ hρ _ _ _ _ ha (hok _ (by simp [decodes])), groupWord_reloc]
        split
        · split
          · rfl
          · have hw : ((List.range (st.vl / 8)).map fun j => E.reloc ρ (groupWord vlmax st src j)) =
                ((List.range (st.vl / 8)).map fun j => groupWord vlmax st src j).map (E.reloc ρ) := by
              rw [List.map_map]; rfl
            rw [hw, storeBytes_reloc ρ hρ]
            rcases storeBytes rodata st a ((List.range (st.vl / 8)).map fun j => groupWord vlmax st src j) (st.vl / 8)
              with _ | s'
            · rfl
            · simp only [Option.map_some, next_reloc']
        · rfl
  · simp [exec, relocState, hh]

end

/-- The RISC-V instruction set is relocatable. -/
def isaReloc (vlmax : Nat) : (isa vlmax).Relocatable where
  decodes := decodes
  exec_reloc := fun ρ hρ rodata i st hne hok => exec_reloc ρ hρ vlmax rodata i st hne hok

end Keccaktree.Asm.Riscv
