import Keccaktree.Asm.Riscv
import Keccaktree.Asm.ArmHom
/-!
The RISC-V semantics commute with lane homomorphisms (`exec_map`), and a
failed state stays failed (`err_exec`): `Riscv.isa vlmax`.
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm Keccaktree.Asm.X86
open Keccaktree.Asm.Arm (gx setX withX addr withAddr gx_map_some setX_map addr_map_some getGD_map setGD_map setGD_map')
open LaneOps

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
  simp only [lane, getV_map hf, X86.getD_map hf]

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
    | lea d a => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, setX_map hf, next_map]
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
      rcases hx : LaneOps.asConst (getR st a) with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · rcases hy : LaneOps.asConst (getR st b) with _ | y
        · simp only [hx, hy, fail_err'] at hne; exact absurd hne (by decide)
        · simp only [hx, hy, hf.asConst _ _ hx, hf.asConst _ _ hy]; rfl
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
          exact (foldl_hom (mapState f) _ _ (fun acc i => (setActive_map' hf acc (d + i) _ _ (fun l => (X86.getD_map hf ws _).symm)).symm) _ _).symm
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
  · simp [exec, mapState, hh]

omit hf in
theorem err_exec (vlmax : Nat) (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (h : st.err = true) :
    (exec vlmax rodata i st).err = true := by
  cases hh : st.halted
  · cases i <;> simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, next, withAddr, setX, setR, State.setGD,
      State.setV, State.fail, h] <;>
      (repeat' split) <;> (try simp_all [setActive_err, foldl_setActive_err]) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
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
