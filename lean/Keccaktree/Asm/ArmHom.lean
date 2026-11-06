import Keccaktree.Asm.Arm
import Keccaktree.Asm.Trace
/-!
The AArch64 semantics commute with lane homomorphisms (`exec_map`), and a
failed state stays failed (`err_exec`): `Arm.isa`.
-/
namespace Keccaktree.Asm.Arm
open Keccaktree.Asm Keccaktree.Asm.X86
open LaneOps

variable {α β : Type} [LaneOps α] [LaneOps β] {f : α → β} (hf : IsHom f)
include hf

theorem getGD_map (s : State α) (n : Nat) : (mapState f s).getGD n = f (s.getGD n) := by
  simp only [State.getGD, mapState, Vector.getD]
  rcases h : s.gd[n]? with _ | v <;> simp [h, hf.const]

omit hf in
theorem setGD_map (s : State α) (n : Nat) (x : α) : (mapState f s).setGD n (f x) = mapState f (s.setGD n x) := by
  simp [State.setGD, mapState, Vector.map_setIfInBounds]

omit hf in
theorem setGD_map' (s : State α) (n : Nat) (x : α) (x' : β) (hx : f x = x') :
    (mapState f s).setGD n x' = mapState f (s.setGD n x) := by
  subst hx; exact setGD_map s n x

theorem getD_map (xs : List α) (i : Nat) : (xs.map f).getD i (const 0) = f (xs.getD i (const 0)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> simp [hf.const]

theorem lane_map (s : State α) (n l : Nat) : lane (mapState f s) n l = f (lane s n l) := by
  simp only [lane, getV_map hf, getD_map hf]

theorem setLanes_map (s : State α) (n : Nat) (lo hi : α) :
    setLanes (mapState f s) n (f lo) (f hi) = mapState f (setLanes s n lo hi) := by
  simp only [setLanes, State.setV, mapState, Vector.map_setIfInBounds]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  split
  · rfl
  · split
    · rfl
    · exact (hf.const 0).symm

theorem setLanes_map' (s : State α) (n : Nat) (lo hi : α) (lo' hi' : β) (hlo : f lo = lo') (hhi : f hi = hi') :
    setLanes (mapState f s) n lo' hi' = mapState f (setLanes s n lo hi) := by
  subst hlo hhi; exact setLanes_map hf s n lo hi

theorem rotr_map (x : α) (n : Nat) : f (rotr x n) = rotr (f x) n := by simp [rotr, hf.rol]

theorem gx_map_some (s : State α) (n : Nat) (a : Addr) (h : gx s n = some a) : gx (mapState f s) n = some a := by
  simp only [gx, getGD_map hf] at h ⊢
  rcases hc : LaneOps.asConst (s.getGD n) with _ | w
  · simp [hc] at h
  · rw [hf.asConst _ _ hc]; simp only [hc, Option.map_some] at h; simp only [Option.map_some, h]

theorem setX_map (s : State α) (n : Nat) (a : Addr) : setX (mapState f s) n a = mapState f (setX s n a) := by
  simp only [setX]; exact setGD_map' s n _ _ (hf.const _)

theorem addr_map_some (s : State α) (base : Nat) (off : Int) (a : Addr) (h : addr s base off = some a) :
    addr (mapState f s) base off = some a := by
  simp only [addr] at h ⊢
  rcases hx : gx s base with _ | x
  · simp [hx] at h
  · rw [gx_map_some hf _ _ _ hx]; simp only [hx, Option.map_some] at h; simp only [Option.map_some, h]

theorem regWords_map (s : State α) (r : LReg) : regWords (mapState f s) r = (regWords s r).map f := by
  cases r <;> simp [regWords, lane_map hf, getGD_map hf]

theorem loadReg_map (s : State α) (r : LReg) (ws : List α) :
    loadReg (mapState f s) r (ws.map f) = mapState f (loadReg s r ws) := by
  cases r with
  | q n => simp only [loadReg, getD_map hf, setLanes_map hf]
  | d n => simp only [loadReg, getD_map hf, lane_map hf, setLanes_map hf]
  | x n => simp only [loadReg, getD_map hf, setGD_map]

omit hf in
theorem next_map (s : State α) : next (mapState f s) = mapState f (next s) := rfl
omit hf in
theorem setFlags_map (s : State α) (a b : Int) : setFlags (mapState f s) a b = mapState f (setFlags s a b) := rfl
omit hf in
theorem condHolds_map (s : State α) (c : Cond) : condHolds (mapState f s) c = condHolds s c := by cases c <;> rfl
omit hf in
theorem fail_err' (s : State α) : s.fail.err = true := rfl

/-- The vector instructions: `next (setLanes ..)` with lane functions built from the lane operations. -/
syntax "arm_vec" : tactic
macro_rules
  | `(tactic| arm_vec) => `(tactic| (
      rw [← next_map]
      exact congrArg next (setLanes_map' hf _ _ _ _ _ _
        (by (try split) <;> simp [lane_map hf, hf.xor, hf.and, hf.or, hf.not, hf.shl, hf.shr, hf.rol, hf.add, hf.const, rotr_map hf])
        (by (try split) <;> simp [lane_map hf, hf.xor, hf.and, hf.or, hf.not, hf.shl, hf.shr, hf.rol, hf.add, hf.const, rotr_map hf]))))

theorem exec_map (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (hne : (exec rodata i st).err = false) :
    exec rodata i (mapState f st) = mapState f (exec rodata i st) := by
  cases hh : st.halted
  · cases i with
    | eor d a b => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec
    | bic d a b => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec
    | eor3 d a b c => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, vop3]; arm_vec
    | bcax d a b c => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, vop3]; arm_vec
    | rax1 d a b => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec
    | xar d a b n => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, vop2]; arm_vec
    | shl d a n => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, vop1]; arm_vec
    | sri d a n => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; arm_vec
    | zip1 d a b => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; arm_vec
    | zip2 d a b => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; arm_vec
    | movv d a => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; arm_vec
    | movi0 d => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; arm_vec
    | eorx d a b n =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [getGD_map hf, hf.xor, rotr_map hf]))
    | bicx d a b n =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [getGD_map hf, hf.and, hf.not, rotr_map hf]))
    | rorx d a n =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [getGD_map hf, rotr_map hf]))
    | movx d a =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [getGD_map hf]))
    | movi d imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [hf.const]))
    | add d a imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_map_some hf _ _ _ hx, setX_map hf, next_map]
    | sub d a imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_map_some hf _ _ _ hx, setX_map hf, next_map]
    | subs d a imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_map_some hf _ _ _ hx]
        split <;> simp only [setX_map hf, setFlags_map, next_map, fail_map]
    | cmp a imm =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_map_some hf _ _ _ hx]
        split <;> simp only [setFlags_map, next_map, fail_map]
    | csel d a b c =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, condHolds_map]
      rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by split <;> simp [getGD_map hf]))
    | ldr r base off =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, loadWords_map hf]
        rcases hl : st.loadWords rodata a (regSize r / 8).toNat with _ | ws
        · rfl
        · simp only [Option.map_some, loadReg_map hf, next_map]
    | ldrlit r lo hi =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
      rw [show ([const lo, const hi] : List β) = [const lo, const hi].map f by simp [hf.const], loadReg_map hf, next_map]
    | str r base off =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base off with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, regWords_map hf, storeWords_map hf]
        rcases hs : st.storeWords a (regWords st r) with _ | s'
        · rfl
        · simp only [Option.map_some, next_map]
    | ldp r1 r2 base off wb =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base (if wb = 2 then 0 else off) with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, loadWords_map hf]
        rcases hl : st.loadWords rodata a ((regSize r1 + regSize r2) / 8).toNat with _ | ws
        · rfl
        · simp only [Option.map_some, ← List.map_take, ← List.map_drop, loadReg_map hf]
          split <;> simp only [setX_map hf, next_map]
    | stp r1 r2 base off wb =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withAddr] at hne ⊢
      rcases ha : addr st base (if wb = 2 then 0 else off) with _ | a
      · simp only [ha, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [ha, addr_map_some hf _ _ _ _ ha, regWords_map hf, ← List.map_append, storeWords_map hf]
        rcases hs : st.storeWords a (regWords st r1 ++ regWords st r2) with _ | s'
        · rfl
        · simp only [Option.map_some]
          split <;> simp only [setX_map hf, next_map]
    | cbz a t =>
      simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, withX] at hne ⊢
      rcases hx : gx st a with _ | x
      · simp only [hx, fail_err'] at hne; exact absurd hne (by decide)
      · simp only [hx, gx_map_some hf _ _ _ hx]
        split <;> (first | rfl | simp only [fail_map])
    | bcond c t => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, condHolds_map]; rfl
    | b t => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; rfl
    | tailcall name => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; rfl
    | ret => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; rfl
    | nop => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, next_map]
    | data => simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, fail_map]
  · simp [exec, mapState, hh]

omit hf in
theorem err_exec (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (h : st.err = true) :
    (exec rodata i st).err = true := by
  cases hh : st.halted
  · cases i <;> simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, next, withX, withAddr, setX, State.setGD,
      State.setV, setLanes, vop1, vop2, vop3, setFlags, State.fail, loadReg, h] <;>
      (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

/-- The AArch64 instruction set. -/
def isa : Isa where
  Instr := Instr
  nop := .nop
  exec := exec
  exec_map := fun f hf rodata i st hne => exec_map hf rodata i st hne
  err_exec := fun rodata i st h => err_exec rodata i st h

theorem isa_execTrace (rodata : Array (BitVec 64)) (l : List Instr) (s : State α) :
    isa.execTrace rodata l s = execTrace rodata l s := rfl

end Keccaktree.Asm.Arm
