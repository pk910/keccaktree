import Keccaktree.Asm.Riscv
import Keccaktree.Asm.ArmHom
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
The RISC-V semantics commute with lane homomorphisms (`exec_map`), and a
failed state stays failed (`err_exec`): `Riscv.isa vlmax`.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 hiding gx setX withX next getGD_map setGD_map setGD_map' gx_map_some setX_map next_map condHolds_map
open Keccaktree.Asm.Arm (gx setX withX addr withAddr gx_map_some setX_map addr_map_some getGD_map setGD_map setGD_map')
open LaneOps

section bytes
variable {α β : Type} [LaneOps α] [LaneOps β] {f : α → β} (hl : IsLaneHom f)
include hl

theorem insByte_map (w x : α) (k : Nat) : f (insByte w x k) = insByte (f w) (f x) k := by
  simp only [insByte, hl.or, hl.and, hl.shl, hl.const]

theorem joinWords_map (k : Nat) (ws : List α) (n : Nat) : (joinWords k ws n).map f = joinWords k (ws.map f) n := by
  simp only [joinWords, List.map_map]
  apply List.map_congr_left; intro j _
  simp only [Function.comp_apply, hl.or, hl.shr, hl.shl, X86.getD_map hl]

theorem splitWords_map (k : Nat) (lo hi : α) (vs : List α) (n : Nat) :
    (splitWords k lo hi vs n).map f = splitWords k (f lo) (f hi) (vs.map f) n := by
  simp only [splitWords, List.map_map]
  apply List.map_congr_left; intro j _
  simp only [Function.comp_apply, hl.or]
  have e1 : f (if j = 0 then LaneOps.and lo (LaneOps.const (BitVec.allOnes 64 >>> (64 - 8 * k)))
      else LaneOps.shr (vs.getD (j - 1) (LaneOps.const 0)) (64 - 8 * k)) =
      (if j = 0 then LaneOps.and (f lo) (LaneOps.const (BitVec.allOnes 64 >>> (64 - 8 * k)))
      else LaneOps.shr ((vs.map f).getD (j - 1) (LaneOps.const 0)) (64 - 8 * k)) := by
    split <;> simp only [hl.and, hl.const, hl.shr, X86.getD_map hl]
  have e2 : f (if j = n then LaneOps.and hi (LaneOps.const (~~~ (BitVec.allOnes 64 >>> (64 - 8 * k))))
      else LaneOps.shl (vs.getD j (LaneOps.const 0)) (8 * k)) =
      (if j = n then LaneOps.and (f hi) (LaneOps.const (~~~ (BitVec.allOnes 64 >>> (64 - 8 * k))))
      else LaneOps.shl ((vs.map f).getD j (LaneOps.const 0)) (8 * k)) := by
    split <;> simp only [hl.and, hl.const, hl.shl, X86.getD_map hl]
  rw [e1, e2]

end bytes

theorem setLanes_err {α : Type} [LaneOps α] (s : State α) (d c : Nat) (g : Nat → α) : (setLanes s d c g).err = s.err := rfl

theorem foldl_setLanes_err {α : Type} [LaneOps α] (d : Nat) (c : Nat → Nat) (g : Nat → Nat → α) :
    ∀ (l : List Nat) (s : State α), (l.foldl (fun s' r => setLanes s' (d + r) (c r) (g r)) s).err = s.err
  | [], _ => rfl
  | r :: l, s => by simp only [List.foldl_cons]; rw [foldl_setLanes_err d c g l]; rfl

theorem setGroup_err {α : Type} [LaneOps α] (vlmax : Nat) (s : State α) (d : Nat) (ws : List α) (n : Nat) :
    (setGroup vlmax s d ws n).err = s.err :=
  foldl_setLanes_err d (fun r => min vlmax (n - r * vlmax)) (fun r l => ws.getD (r * vlmax + l) (LaneOps.const 0)) _ s

theorem storeBytes_err {α : Type} [LaneOps α] (rodata : Array (BitVec 64)) (st s' : State α) (a : Addr) (vs : List α)
    (n : Nat) (h : storeBytes rodata st a vs n = some s') : s'.err = st.err := by
  unfold storeBytes at h
  split at h
  · exact storeWords_err _ _ _ _ h
  · split at h
    · exact storeWords_err _ _ _ _ h
    · cases h

variable {α β : Type} [LaneOps α] [LaneOps β] {f : α → β} (hf : IsHom f)
include hf

theorem getR_map (s : State α) (n : Nat) : getR (mapState f s) n = f (getR s n) := by
  unfold getR; split
  · exact (hf.const 0).symm
  · exact getGD_map hf s n

omit hf in
theorem setR_map' (s : State α) (n : Nat) (x : α) (x' : β) (hx : f x = x') :
    setR (mapState f s) n x' = mapState f (setR s n x) := by
  unfold setR; split
  · rfl
  · exact setGD_map' s n x x' hx

theorem lane_map (s : State α) (n l : Nat) : lane (mapState f s) n l = f (lane s n l) := by
  simp only [lane, getV_map hf, X86.getD_map hf.lane]

theorem setLanes_map' (s : State α) (d c : Nat) (g : Nat → α) (g' : Nat → β) (hg : ∀ l, f (g l) = g' l) :
    setLanes (mapState f s) d c g' = mapState f (setLanes s d c g) := by
  simp only [setLanes, State.setV, mapState, Vector.map_setIfInBounds]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  by_cases hi : i < c
  · simp only [hi, ↓reduceIte]; exact (hg i).symm
  · simp only [hi, ↓reduceIte]
    show lane (mapState f s) d i = f (lane s d i)
    exact lane_map hf s d i

theorem setGroup_map (vlmax : Nat) (s : State α) (d : Nat) (ws : List α) (n : Nat) :
    setGroup vlmax (mapState f s) d (ws.map f) n = mapState f (setGroup vlmax s d ws n) := by
  unfold setGroup
  exact (foldl_hom (mapState f) _ _ (fun acc r => (setLanes_map' hf acc (d + r) _ _ _
    (fun l => (X86.getD_map hf.lane ws _).symm)).symm) _ _).symm

theorem groupWord_map (vlmax : Nat) (s : State α) (src j : Nat) :
    groupWord vlmax (mapState f s) src j = f (groupWord vlmax s src j) := lane_map hf s _ _

theorem loadBytes_map (rodata : Array (BitVec 64)) (s : State α) (a : Addr) (n : Nat) :
    loadBytes rodata (mapState f s) a n = (loadBytes rodata s a n).map (List.map f) := by
  unfold loadBytes
  split
  · exact loadWords_map hf rodata s a n
  · rw [loadWords_map hf]
    rcases s.loadWords rodata (wordOf a) (n + 1) with _ | ws
    · rfl
    · simp only [Option.map_some, joinWords_map hf.lane]

theorem storeBytes_map (rodata : Array (BitVec 64)) (s : State α) (a : Addr) (vs : List α) (n : Nat) :
    storeBytes rodata (mapState f s) a (vs.map f) n = (storeBytes rodata s a vs n).map (mapState f) := by
  unfold storeBytes
  split
  · exact storeWords_map hf s a vs
  · rw [loadWords_map hf, loadWords_map hf]
    rcases s.loadWords rodata (wordOf a) 1 with _ | l1
    · rfl
    · rcases s.loadWords rodata ⟨a.region, (wordOf a).off + 8 * n⟩ 1 with _ | l2
      · rcases l1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
      · rcases l1 with _ | ⟨lo, _ | ⟨_, _⟩⟩ <;> rcases l2 with _ | ⟨hi, _ | ⟨_, _⟩⟩ <;> try rfl
        simp only [Option.map_some, List.map_cons, List.map_nil]
        rw [← splitWords_map hf.lane]
        exact storeWords_map hf s _ _

theorem setActive_map' (s : State α) (d : Nat) (g : Nat → α) (g' : Nat → β) (hg : ∀ l, f (g l) = g' l) :
    setActive (mapState f s) d g' = mapState f (setActive s d g) := by
  simp only [setActive, State.setV, mapState, Vector.map_setIfInBounds]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  by_cases hi : i < s.vl
  · simp only [hi, ↓reduceIte]; exact (hg i).symm
  · simp only [hi, ↓reduceIte]
    show lane (mapState f s) d i = f (lane s d i)
    exact lane_map hf s d i

omit hf in
theorem next_map (s : State α) : next (mapState f s) = mapState f (next s) := rfl
omit hf in
theorem map_upd_vl (s : State α) (n : Nat) : mapState f { s with vl := n } = { mapState f s with vl := n } := rfl
omit hf in
theorem fail_err' (s : State α) : s.fail.err = true := rfl

theorem rotr_map (x : α) (n : Nat) : f (rotr x n) = rotr (f x) n := by simp [rotr, hf.rol]
theorem sub_map (a b : α) : f (sub a b) = sub (f a) (f b) := by simp [sub, hf.add, hf.not, hf.const]
theorem op2_map (k : Op2) (a b : α) : f (op2 k a b) = op2 k (f a) (f b) := by
  cases k <;> simp [op2, hf.xor, hf.or, hf.and, hf.add, hf.not, sub_map hf]
theorem opi_map (k : OpI) (a : α) (i : BitVec 64) : f (opi k a i) = opi k (f a) i := by
  cases k <;> simp [opi, hf.xor, hf.or, hf.and, hf.add, hf.shl, hf.shr, hf.const, rotr_map hf]
theorem vop_map (k : VOp) (a b : α) : f (vop k a b) = vop k (f a) (f b) := by
  cases k <;> simp [vop, hf.xor, hf.or, hf.and, hf.not]
theorem vsh_map (k : VSh) (a : α) (n : Nat) : f (vsh k a n) = vsh k (f a) n := by
  cases k <;> simp only [vsh] <;> (try split) <;> simp [hf.shl, hf.shr, hf.const, rotr_map hf]

omit hf in
theorem setActive_err (s : State α) (d : Nat) (g : Nat → α) : (setActive s d g).err = s.err := rfl

omit hf in
theorem foldl_setActive_err (l : List Nat) (s : State α) (d : Nat) (h : Nat → Nat → α) :
    (l.foldl (fun s' i => setActive s' (d + i) (h i)) s).err = s.err := by
  induction l generalizing s with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons]; rw [ih]; rfl

theorem exec_map (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (st : State α)
    (hne : (exec vlmax rodata i st).err = false) :
    exec vlmax rodata i (mapState f st) = mapState f (exec vlmax rodata i st) := by
  cases hh : st.halted
  · cases i with
    | op d a b k =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setR_map' _ _ _ _ (by simp [getR_map hf, op2_map hf]))
    | opi d a k imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setR_map' _ _ _ _ (by simp [getR_map hf, opi_map hf]))
    | li d imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setR_map' _ _ _ _ (hf.const _))
    | mv d a =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setR_map' _ _ _ _ (by simp [getR_map hf]))
    | not d a =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setR_map' _ _ _ _ (by simp [getR_map hf, hf.not]))
    | lea d a =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      split <;> simp only [setX_map hf, next_map, fail_map]
    | ld d base off =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, loadWords_map hf]
        rcases hl : st.loadWords rodata a 1 with _ | l
        · rfl
        · rcases l with _ | ⟨w, l⟩
          · rfl
          · rcases l with _ | ⟨w2, l⟩
            · simp only [Option.map_some, List.map_cons, List.map_nil]
              rw [← next_map]; exact congrArg next (setR_map' _ _ _ _ rfl)
            · rfl
    | sd src base off =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, getR_map hf]
        rw [show [f (getR st src)] = [getR st src].map f from rfl, storeWords_map hf]
        rcases hs : st.storeWords a [getR st src] with _ | s'
        · rfl
        · simp only [Option.map_some, next_map]
    | br c a b t =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, getR_map hf] at hne ⊢
      rcases hx : LaneOps.asAddr (getR st a) with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · rcases hy : LaneOps.asAddr (getR st b) with _ | y
        · simp only [hx, hy, fail_err'] at hne; exact absurd hne (by decide)
        · simp only [hx, hy, hf.asAddr _ _ hx, hf.asAddr _ _ hy]
          split <;> (first | rfl | simp only [fail_map])
    | j t => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; rfl
    | ret => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; rfl
    | nop => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, next_map]
    | unsupported name => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, fail_map]
    | vsetvli d a =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, getR_map hf] at hne ⊢
      rcases hx : LaneOps.asConst (getR st a) with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, hf.asConst _ _ hx]
        rw [setR_map' _ _ _ _ (hf.const _)]; rfl
    | vop d a b k =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setActive_map' hf _ _ _ _ (fun l => by simp [lane_map hf, vop_map hf]))
    | vnot d a =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setActive_map' hf _ _ _ _ (fun l => by simp [lane_map hf, hf.not]))
    | vshifti d a k imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setActive_map' hf _ _ _ _ (fun l => by simp [lane_map hf, vsh_map hf]))
    | vshiftx d a k x =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, getR_map hf] at hne ⊢
      rcases hx : LaneOps.asConst (getR st x) with _ | n
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, hf.asConst _ _ hx]
        rw [← next_map]; exact congrArg next (setActive_map' hf _ _ _ _ (fun l => by simp [lane_map hf, vsh_map hf]))
    | vxorx d a x =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setActive_map' hf _ _ _ _ (fun l => by simp [lane_map hf, getR_map hf, hf.xor]))
    | vmvi d imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setActive_map' hf _ _ _ _ (fun _ => hf.const _))
    | vmvx d x =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setActive_map' hf _ _ _ _ (fun _ => (getR_map hf _ _).symm))
    | vmvv d a =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setActive_map' hf _ _ _ _ (fun l => (lane_map hf _ _ _).symm))
    | vlseg d base nf =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr, vl_map] at hne ⊢
      rcases ha : addr st base 0 with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, loadWords_map hf]
        rcases hl : st.loadWords rodata a (nf * st.vl) with _ | ws
        · rfl
        · simp only [Option.map_some]
          rw [← next_map]; congr 1
          exact (foldl_hom (mapState f) _ _ (fun acc i => (setActive_map' hf acc (d + i) _ _ (fun l => (X86.getD_map hf.lane ws _).symm)).symm) _ _).symm
    | vsseg src base nf =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr, vl_map] at hne ⊢
      rcases ha : addr st base 0 with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, lane_map hf]
        have hw : (List.range (nf * st.vl)).map (fun q => f (lane st (src + q % nf) (q / nf))) =
            ((List.range (nf * st.vl)).map fun q => lane st (src + q % nf) (q / nf)).map f := by
          rw [List.map_map]; rfl
        rw [hw, storeWords_map hf]
        rcases hs : st.storeWords a ((List.range (nf * st.vl)).map fun q => lane st (src + q % nf) (q / nf)) with _ | s'
        · rfl
        · simp only [Option.map_some, next_map]
    | lbu d base off =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, loadWords_map hf]
        rcases hl : st.loadWords rodata (wordOf a) 1 with _ | l
        · rfl
        · rcases l with _ | ⟨w, _ | ⟨w2, l⟩⟩
          · rfl
          · simp only [Option.map_some, List.map_cons, List.map_nil]
            rw [← next_map]; exact congrArg next (setR_map' _ _ _ _ (by simp [hf.and, hf.shr, hf.const]))
          · rfl
    | sb src base off =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, loadWords_map hf, getR_map hf]
        rcases hl : st.loadWords rodata (wordOf a) 1 with _ | l
        · rfl
        · rcases l with _ | ⟨w, _ | ⟨w2, l⟩⟩
          · rfl
          · simp only [Option.map_some, List.map_cons, List.map_nil]
            rw [← insByte_map hf.lane, show [f (insByte w (getR st src) (byteOf a))] =
              [insByte w (getR st src) (byteOf a)].map f from rfl, storeWords_map hf]
            rcases (st.storeWords (wordOf a) [insByte w (getR st src) (byteOf a)]) with _ | s'
            · rfl
            · simp only [Option.map_some, next_map]
          · rfl
    | vsetvlie8 d a lmul =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, getR_map hf] at hne ⊢
      rcases hx : LaneOps.asConst (getR st a) with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, hf.asConst _ _ hx]
        split
        · rw [setR_map' _ _ _ _ (hf.const _)]; rfl
        · rfl
    | vle8 d base =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr, vl_map] at hne ⊢
      rcases ha : addr st base 0 with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, loadBytes_map hf]
        split
        · rcases (loadBytes rodata st a (st.vl / 8)) with _ | ws
          · rfl
          · simp only [Option.map_some]
            rw [← next_map, setGroup_map hf]
        · rfl
    | vse8 src base =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr, vl_map] at hne ⊢
      rcases ha : addr st base 0 with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, groupWord_map hf]
        split
        · split
          · rfl
          · have hw : ((List.range (st.vl / 8)).map fun j => f (groupWord vlmax st src j)) =
                ((List.range (st.vl / 8)).map fun j => groupWord vlmax st src j).map f := by
              rw [List.map_map]; rfl
            rw [hw, storeBytes_map hf]
            rcases storeBytes rodata st a ((List.range (st.vl / 8)).map fun j => groupWord vlmax st src j) (st.vl / 8)
              with _ | s'
            · rfl
            · simp only [Option.map_some, next_map]
        · rfl
  · simp [exec, mapState, hh]

omit hf in
theorem err_exec (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (h : st.err = true) :
    (exec vlmax rodata i st).err = true := by
  cases hh : st.halted
  · cases i <;> simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, next, withAddr, setX, setR, State.setGD,
      State.setV, State.fail, h] <;>
      (repeat' split) <;> (try simp_all [setActive_err, foldl_setActive_err, setGroup_err]) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h)) <;>
      (try (rw [storeBytes_err _ _ _ _ _ _ ‹storeBytes _ _ _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

/-- The RISC-V instruction set, for a vector length of `vlmax` 64-bit lanes. -/
@[reducible] def isa (vlmax : Nat) : Isa where
  Instr := Instr
  nop := .nop
  exec := exec vlmax
  exec_map := fun f hf rodata i st hne => exec_map hf vlmax rodata i st hne
  err_exec := fun rodata i st h => err_exec vlmax rodata i st h

theorem isa_execTrace (vlmax : Nat) (rodata : Array (BitVec 64)) (l : List Instr) (s : State α) :
    (isa vlmax).execTrace rodata l s = execTrace vlmax rodata l s := rfl

end Keccaktree.Asm.Riscv
