import Keccaktree.Asm.Trace
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Memory footprints

What a step writes: the memory cells (region, word index) an instruction stores to,
computed from the state before it with the same address decoding as `exec`.  Every
other cell keeps its value (`exec_frame`); along a trace, the cells outside the
trace's footprint are unchanged (`Isa.Footprint.execTrace_frame`).  The composition
of loop iterations needs this: iteration `k` must not touch the digests of the
earlier iterations nor the inputs of the later ones, and the base run's footprint is
a closed list the kernel can check.
-/
namespace Keccaktree.Asm
open X86

variable {α : Type} [LaneOps α]

/-- The cells of a store of `n` words at byte address `a`. -/
def storeCells (a : Addr) (n : Nat) : List (Region × Int) :=
  (List.range n).map fun (i : Nat) => (a.region, a.off / 8 + (i : Int))

namespace X86

theorem memStoreFrom_frame (m : Region → Int → α) (r : Region) (q0 : Int) (vs : List α) (r' : Region) (q' : Int)
    (h : ∀ i : Nat, i < vs.length → ¬ (r' = r ∧ q' = q0 + (i : Int))) :
    memStoreFrom m r q0 vs r' q' = m r' q' := by
  induction vs generalizing m q0 with
  | nil => rfl
  | cons v vs ih =>
    simp only [memStoreFrom]
    rw [ih]
    · simp only [memStore]
      have h0 := h 0 (by simp)
      have h0' : ¬ (r' = r ∧ q' = q0) := by simpa using h0
      simp only [h0', ↓reduceIte]
    · intro i hi hc
      apply h (i + 1) (by simp; omega)
      obtain ⟨h1, h2⟩ := hc
      exact ⟨h1, by rw [h2]; omega⟩

theorem storeWords_frame (s s' : State α) (a : Addr) (vs : List α) (h : s.storeWords a vs = some s')
    (r : Region) (q : Int) (hw : (r, q) ∉ storeCells a vs.length) : s'.mem r q = s.mem r q := by
  simp only [State.storeWords] at h
  split at h
  · cases h
    apply memStoreFrom_frame
    intro i hi hc
    apply hw
    simp only [storeCells, List.mem_map, List.mem_range]
    exact ⟨i, hi, by rw [hc.1, hc.2]⟩
  · cases h

/-- The cells an x86 instruction stores to (from the state before it). -/
def writes (s : State α) : Instr → List (Region × Int)
  | .vstore lanes m src => match memAddr? s m with
    | some a => storeCells a ((s.getV src).take lanes).length
    | none => []
  | .vextracti128 m _ _ => match memAddr? s m with
    | some a => storeCells a 2
    | none => []
  | .storeq m _ | .storeqi m _ | .xorm m _ | .addm m _ | .decm m => match memAddr? s m with
    | some a => storeCells a 1
    | none => []
  | .call _ | .push _ => match gx s 4 with
    | some sp => storeCells ⟨sp.region, sp.off - 8⟩ 1
    | none => []
  | .repmovsb => match gx s 1, gx s 7 with
    | some n, some dst => storeCells dst (n.off.toNat / 8)
    | _, _ => []
  | _ => []

/-- A store of a list of words followed by a memory-preserving continuation. -/
theorem withStore_frame (s : State α) (a : Addr) (vs : List α) (k : State α → State α)
    (hne : (withStore s a vs k).err = false) (hk : ∀ s', (k s').mem = s'.mem)
    (r : Region) (q : Int) (hw : (r, q) ∉ storeCells a vs.length) :
    (withStore s a vs k).mem r q = s.mem r q := by
  simp only [withStore] at hne ⊢
  split
  · rename_i s' hs
    rw [hk]; exact storeWords_frame s s' a vs hs r q hw
  · rfl

theorem withLoad_mem (rodata : Array (BitVec 64)) (s : State α) (a : Addr) (n : Nat) (k : List α → State α)
    (hk : ∀ ws, (k ws).mem = s.mem) : (withLoad rodata s a n k).mem = s.mem := by
  simp only [withLoad]; split
  · exact hk _
  · rfl

theorem withSrc_mem (rodata : Array (BitVec 64)) (s : State α) (lanes : Nat) (b : Src) (k : List α → State α)
    (hk : ∀ bs, (k bs).mem = s.mem) : (withSrc rodata s lanes b k).mem = s.mem := by
  simp only [withSrc]; split
  · exact hk _
  · rfl

theorem withX_mem (s : State α) (n : Nat) (k : Addr → State α) (hk : ∀ a, (k a).mem = s.mem) :
    (withX s n k).mem = s.mem := by
  simp only [withX]; split
  · exact hk _
  · rfl

theorem withMem_mem (s : State α) (m : MemOp) (k : Addr → State α) (hk : ∀ a, (k a).mem = s.mem) :
    (withMem s m k).mem = s.mem := by
  simp only [withMem]; split
  · exact hk _
  · rfl

theorem readG_mem (rodata : Array (BitVec 64)) (s : State α) (b : GSrc) (k : α → State α) (hk : ∀ y, (k y).mem = s.mem) :
    (readG rodata s b k).mem = s.mem := by
  cases b with
  | reg g => exact hk _
  | imm i => exact hk _
  | mem m => exact withMem_mem s m _ fun a => withLoad_mem rodata s a 1 _ fun ws => hk _

@[simp] theorem next_mem (s : State α) : (next s).mem = s.mem := rfl
@[simp] theorem setGD_mem (s : State α) (n : Nat) (x : α) : (s.setGD n x).mem = s.mem := rfl
@[simp] theorem setV_mem (s : State α) (n : Nat) (x : Vector α 8) : (s.setV n x).mem = s.mem := rfl
@[simp] theorem setX_mem (s : State α) (n : Nat) (a : Addr) : (setX s n a).mem = s.mem := rfl
@[simp] theorem writeV_mem (s : State α) (n lanes : Nat) (vs : List α) : (writeV s n lanes vs).mem = s.mem := rfl
@[simp] theorem fail_mem (s : State α) : s.fail.mem = s.mem := rfl
theorem setFlagsSub_mem (s : State α) (a b : Addr) : (setFlagsSub s a b).mem = s.mem := by
  simp only [setFlagsSub]; split <;> rfl
theorem binop_mem (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) (f : α → α → α) :
    (binop rodata s lanes d a b f).mem = s.mem := withSrc_mem rodata s lanes b _ fun _ => rfl

syntax "mk_mem" : tactic
macro_rules
  | `(tactic| mk_mem) => `(tactic| first
    | (apply binop_mem)
    | (apply withSrc_mem; intro _; (repeat' split) <;> mk_mem)
    | (apply withMem_mem; intro _; (repeat' split) <;> mk_mem)
    | (apply withX_mem; intro _; (repeat' split) <;> mk_mem)
    | (apply withLoad_mem; intro _; (repeat' split) <;> mk_mem)
    | (apply readG_mem; intro _; mk_mem)
    | (simp only [next_mem, setFlagsSub_mem, setX_mem, setGD_mem, writeV_mem, fail_mem, setV_mem]; done)
    | (split <;> mk_mem)
    | rfl)

theorem exec_mem_vmov (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_dst : _) (x_src : _) (x_mask : _) :
    (exec rodata (.vmov x_lanes x_dst x_src x_mask) s).mem = s.mem := by
  cases hh : s.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
    exact withSrc_mem rodata s _ _ _ (fun _ => rfl)
  · simp only [exec, hh, ↓reduceIte]

theorem exec_mem_vpxor (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpxor x_lanes x_d x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpand (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpand x_lanes x_d x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpandn (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpandn x_lanes x_d x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpor (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpor x_lanes x_d x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpaddq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpaddq x_lanes x_d x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpsllq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_imm : _) :
    (exec rodata (.vpsllq x_lanes x_d x_a x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpsrlq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_imm : _) :
    (exec rodata (.vpsrlq x_lanes x_d x_a x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vprolq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_imm : _) :
    (exec rodata (.vprolq x_lanes x_d x_a x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpsllvq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpsllvq x_lanes x_d x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpsrlvq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpsrlvq x_lanes x_d x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpternlogq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) (x_imm : _) :
    (exec rodata (.vpternlogq x_lanes x_d x_a x_b x_imm) s).mem = s.mem := by
  cases hh : s.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
    exact withSrc_mem rodata s _ _ _ (fun _ => rfl)
  · simp only [exec, hh, ↓reduceIte]

theorem exec_mem_vpshufb (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_ctrl : _) :
    (exec rodata (.vpshufb x_lanes x_d x_a x_ctrl) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpshufd (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_imm : _) :
    (exec rodata (.vpshufd x_lanes x_d x_a x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpblendd (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) (x_imm : _) :
    (exec rodata (.vpblendd x_lanes x_d x_a x_b x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpalignr (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) (x_imm : _) :
    (exec rodata (.vpalignr x_lanes x_d x_a x_b x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vpunpcklqdq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpunpcklqdq x_lanes x_d x_a x_b) s).mem = s.mem := by
  cases hh : s.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
    exact withSrc_mem rodata s _ _ _ (fun _ => rfl)
  · simp only [exec, hh, ↓reduceIte]

theorem exec_mem_vpunpckhqdq (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.vpunpckhqdq x_lanes x_d x_a x_b) s).mem = s.mem := by
  cases hh : s.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
    exact withSrc_mem rodata s _ _ _ (fun _ => rfl)
  · simp only [exec, hh, ↓reduceIte]

theorem exec_mem_vperm2i128 (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_a : _) (x_b : _) (x_imm : _) :
    (exec rodata (.vperm2i128 x_d x_a x_b x_imm) s).mem = s.mem := by
  cases hh : s.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
    exact withSrc_mem rodata s _ _ _ (fun _ => rfl)
  · simp only [exec, hh, ↓reduceIte]

theorem exec_mem_vinserti128 (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_a : _) (x_b : _) (x_imm : _) :
    (exec rodata (.vinserti128 x_d x_a x_b x_imm) s).mem = s.mem := by
  cases hh : s.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
    exact withSrc_mem rodata s _ _ _ (fun _ => rfl)
  · simp only [exec, hh, ↓reduceIte]

theorem exec_mem_vshufi64x2 (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_a : _) (x_b : _) (x_imm : _) :
    (exec rodata (.vshufi64x2 x_lanes x_d x_a x_b x_imm) s).mem = s.mem := by
  cases hh : s.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]
    exact withSrc_mem rodata s _ _ _ (fun _ => rfl)
  · simp only [exec, hh, ↓reduceIte]

theorem exec_mem_vpermt2q (rodata : Array (BitVec 64)) (s : State α) (x_lanes : _) (x_d : _) (x_idx : _) (x_b : _) :
    (exec rodata (.vpermt2q x_lanes x_d x_idx x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_kmovw (rodata : Array (BitVec 64)) (s : State α) (x_k : _) (x_m : _) :
    (exec rodata (.kmovw x_k x_m) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_vzeroupper (rodata : Array (BitVec 64)) (s : State α)  :
    (exec rodata (.vzeroupper) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_mov (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_s : _) :
    (exec rodata (.mov x_d x_s) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_xchg (rodata : Array (BitVec 64)) (s : State α) (x_a : _) (x_b : _) :
    (exec rodata (.xchg x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_movi (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_imm : _) :
    (exec rodata (.movi x_d x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_lea (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_m : _) :
    (exec rodata (.lea x_d x_m) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_add (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_imm : _) :
    (exec rodata (.add x_d x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_sub (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_imm : _) :
    (exec rodata (.sub x_d x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_andi (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_imm : _) :
    (exec rodata (.andi x_d x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_shl (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_imm : _) :
    (exec rodata (.shl x_d x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_dec (rodata : Array (BitVec 64)) (s : State α) (x_d : _) :
    (exec rodata (.dec x_d) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_xorz (rodata : Array (BitVec 64)) (s : State α) (x_d : _) :
    (exec rodata (.xorz x_d) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_cmpi (rodata : Array (BitVec 64)) (s : State α) (x_a : _) (x_imm : _) :
    (exec rodata (.cmpi x_a x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_cmpr (rodata : Array (BitVec 64)) (s : State α) (x_a : _) (x_b : _) :
    (exec rodata (.cmpr x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_cmpm (rodata : Array (BitVec 64)) (s : State α) (x_m : _) (x_b : _) :
    (exec rodata (.cmpm x_m x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_cmprm (rodata : Array (BitVec 64)) (s : State α) (x_a : _) (x_m : _) :
    (exec rodata (.cmprm x_a x_m) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_test (rodata : Array (BitVec 64)) (s : State α) (x_a : _) (x_b : _) :
    (exec rodata (.test x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_bt (rodata : Array (BitVec 64)) (s : State α) (x_a : _) (x_b : _) :
    (exec rodata (.bt x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_btc (rodata : Array (BitVec 64)) (s : State α) (x_a : _) (x_imm : _) :
    (exec rodata (.btc x_a x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_alu (rodata : Array (BitVec 64)) (s : State α) (x_op : _) (x_d : _) (x_b : _) :
    (exec rodata (.alu x_op x_d x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_andn (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_a : _) (x_b : _) :
    (exec rodata (.andn x_d x_a x_b) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_rorx (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_b : _) (x_imm : _) :
    (exec rodata (.rorx x_d x_b x_imm) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_jcc (rodata : Array (BitVec 64)) (s : State α) (x_c : _) (x_target : _) :
    (exec rodata (.jcc x_c x_target) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_jmp (rodata : Array (BitVec 64)) (s : State α) (x_target : _) :
    (exec rodata (.jmp x_target) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_jcct (rodata : Array (BitVec 64)) (s : State α) (x_c : _) (x_name : _) :
    (exec rodata (.jcct x_c x_name) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_ret (rodata : Array (BitVec 64)) (s : State α)  :
    (exec rodata (.ret) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_pop (rodata : Array (BitVec 64)) (s : State α) (x_d : _) :
    (exec rodata (.pop x_d) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_loadq (rodata : Array (BitVec 64)) (s : State α) (x_d : _) (x_m : _) :
    (exec rodata (.loadq x_d x_m) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_tailcall (rodata : Array (BitVec 64)) (s : State α) (x_name : _) :
    (exec rodata (.tailcall x_name) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

theorem exec_mem_nop (rodata : Array (BitVec 64)) (s : State α)  :
    (exec rodata (.nop) s).mem = s.mem := by
  simp only [exec]; split
  · rfl
  · mk_mem

set_option maxHeartbeats 4000000 in
/-- **The footprint of a step**: a non-failing step changes memory only in the cells it stores to. -/
theorem exec_frame (rodata : Array (BitVec 64)) (i : Instr) (s : State α) (hne : (exec rodata i s).err = false)
    (r : Region) (q : Int) (hw : (r, q) ∉ writes s i) : (exec rodata i s).mem r q = s.mem r q := by
  cases hh : s.halted
  · cases i with
    | vstore lanes m src =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withMem] at hne ⊢
      rcases ha : memAddr? s m with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        exact withStore_frame s a _ _ hne (fun _ => rfl) r q hw
    | vextracti128 m a' imm =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withMem] at hne ⊢
      rcases ha : memAddr? s m with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        exact withStore_frame s a _ _ hne (fun _ => rfl) r q (by simpa [lane128] using hw)
    | storeq m src =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withMem] at hne ⊢
      rcases ha : memAddr? s m with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        exact withStore_frame s a _ _ hne (fun _ => rfl) r q hw
    | storeqi m imm =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withMem] at hne ⊢
      rcases ha : memAddr? s m with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        exact withStore_frame s a _ _ hne (fun _ => rfl) r q hw
    | xorm m src =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withMem] at hne ⊢
      rcases ha : memAddr? s m with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        simp only [withLoad] at hne ⊢
        rcases hl : s.loadWords rodata a 1 with _ | ws
        · simp only [hl] at hne ⊢; rfl
        · simp only [hl] at hne ⊢
          exact withStore_frame s a _ _ hne (fun _ => rfl) r q hw
    | addm m imm =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withMem] at hne ⊢
      rcases ha : memAddr? s m with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        simp only [withLoad] at hne ⊢
        rcases hl : s.loadWords rodata a 1 with _ | ws
        · simp only [hl] at hne ⊢; rfl
        · simp only [hl] at hne ⊢
          exact withStore_frame s a _ _ hne (fun _ => rfl) r q hw
    | decm m =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withMem] at hne ⊢
      rcases ha : memAddr? s m with _ | a
      · simp only [ha] at hne ⊢; rfl
      · simp only [ha] at hne hw ⊢
        simp only [withLoad] at hne ⊢
        rcases hl : s.loadWords rodata a 1 with _ | ws
        · simp only [hl] at hne ⊢; rfl
        · simp only [hl] at hne ⊢
          rcases hv : LaneOps.asAddr (ws.headD (LaneOps.const 0)) with _ | v
          · simp only [hv] at hne ⊢; rfl
          · simp only [hv] at hne ⊢
            by_cases hr : v.region = 0
            · simp only [hr, ↓reduceIte] at hne ⊢
              exact withStore_frame s a _ _ hne (fun _ => rfl) r q hw
            · simp only [hr, ↓reduceIte]; rfl
    | call t =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withX] at hne ⊢
      rcases hsp : gx s 4 with _ | sp
      · simp only [hsp] at hne ⊢; rfl
      · simp only [hsp] at hne hw ⊢
        exact withStore_frame s _ _ _ hne (fun _ => rfl) r q hw
    | push src =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withX] at hne ⊢
      rcases hsp : gx s 4 with _ | sp
      · simp only [hsp] at hne ⊢; rfl
      · simp only [hsp] at hne hw ⊢
        exact withStore_frame s _ _ _ hne (fun _ => rfl) r q hw
    | repmovsb =>
      simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, writes] at hne hw ⊢
      simp only [withX] at hne ⊢
      rcases hn : gx s 1 with _ | n
      · simp only [hn] at hne ⊢; rfl
      · rcases hsrc : gx s 6 with _ | src
        · simp only [hn, hsrc] at hne ⊢; rfl
        · rcases hdst : gx s 7 with _ | dst
          · simp only [hn, hsrc, hdst] at hne ⊢; rfl
          · simp only [hn, hsrc, hdst] at hne hw ⊢
            simp only [repBody] at hne ⊢
            by_cases hc : n.region = 0 ∧ n.off % 8 = 0 ∧ n.off ≥ 0
            · simp only [hc, and_self, ↓reduceIte, withLoad] at hne ⊢
              rcases hl : s.loadWords rodata src (n.off.toNat / 8) with _ | vs
              · simp only [hl] at hne ⊢; rfl
              · simp only [hl] at hne ⊢
                have hlen : vs.length = n.off.toNat / 8 := by
                  simp only [State.loadWords] at hl
                  split at hl
                  · cases hl; simp
                  · cases hl
                exact withStore_frame s dst vs _ hne (fun _ => rfl) r q (by rw [hlen]; exact hw)
            · simp only [hc, ↓reduceIte]; rfl
    | vmov x_lanes x_dst x_src x_mask => rw [exec_mem_vmov]
    | vpxor x_lanes x_d x_a x_b => rw [exec_mem_vpxor]
    | vpand x_lanes x_d x_a x_b => rw [exec_mem_vpand]
    | vpandn x_lanes x_d x_a x_b => rw [exec_mem_vpandn]
    | vpor x_lanes x_d x_a x_b => rw [exec_mem_vpor]
    | vpaddq x_lanes x_d x_a x_b => rw [exec_mem_vpaddq]
    | vpsllq x_lanes x_d x_a x_imm => rw [exec_mem_vpsllq]
    | vpsrlq x_lanes x_d x_a x_imm => rw [exec_mem_vpsrlq]
    | vprolq x_lanes x_d x_a x_imm => rw [exec_mem_vprolq]
    | vpsllvq x_lanes x_d x_a x_b => rw [exec_mem_vpsllvq]
    | vpsrlvq x_lanes x_d x_a x_b => rw [exec_mem_vpsrlvq]
    | vpternlogq x_lanes x_d x_a x_b x_imm => rw [exec_mem_vpternlogq]
    | vpshufb x_lanes x_d x_a x_ctrl => rw [exec_mem_vpshufb]
    | vpshufd x_lanes x_d x_a x_imm => rw [exec_mem_vpshufd]
    | vpblendd x_lanes x_d x_a x_b x_imm => rw [exec_mem_vpblendd]
    | vpalignr x_lanes x_d x_a x_b x_imm => rw [exec_mem_vpalignr]
    | vpunpcklqdq x_lanes x_d x_a x_b => rw [exec_mem_vpunpcklqdq]
    | vpunpckhqdq x_lanes x_d x_a x_b => rw [exec_mem_vpunpckhqdq]
    | vperm2i128 x_d x_a x_b x_imm => rw [exec_mem_vperm2i128]
    | vinserti128 x_d x_a x_b x_imm => rw [exec_mem_vinserti128]
    | vshufi64x2 x_lanes x_d x_a x_b x_imm => rw [exec_mem_vshufi64x2]
    | vpermt2q x_lanes x_d x_idx x_b => rw [exec_mem_vpermt2q]
    | kmovw x_k x_m => rw [exec_mem_kmovw]
    | vzeroupper => rw [exec_mem_vzeroupper]
    | mov x_d x_s => rw [exec_mem_mov]
    | xchg x_a x_b => rw [exec_mem_xchg]
    | movi x_d x_imm => rw [exec_mem_movi]
    | lea x_d x_m => rw [exec_mem_lea]
    | add x_d x_imm => rw [exec_mem_add]
    | sub x_d x_imm => rw [exec_mem_sub]
    | andi x_d x_imm => rw [exec_mem_andi]
    | shl x_d x_imm => rw [exec_mem_shl]
    | dec x_d => rw [exec_mem_dec]
    | xorz x_d => rw [exec_mem_xorz]
    | cmpi x_a x_imm => rw [exec_mem_cmpi]
    | cmpr x_a x_b => rw [exec_mem_cmpr]
    | cmpm x_m x_b => rw [exec_mem_cmpm]
    | cmprm x_a x_m => rw [exec_mem_cmprm]
    | test x_a x_b => rw [exec_mem_test]
    | bt x_a x_b => rw [exec_mem_bt]
    | btc x_a x_imm => rw [exec_mem_btc]
    | alu x_op x_d x_b => rw [exec_mem_alu]
    | andn x_d x_a x_b => rw [exec_mem_andn]
    | rorx x_d x_b x_imm => rw [exec_mem_rorx]
    | jcc x_c x_target => rw [exec_mem_jcc]
    | jmp x_target => rw [exec_mem_jmp]
    | jcct x_c x_name => rw [exec_mem_jcct]
    | ret => rw [exec_mem_ret]
    | pop x_d => rw [exec_mem_pop]
    | loadq x_d x_m => rw [exec_mem_loadq]
    | tailcall x_name => rw [exec_mem_tailcall]
    | nop => rw [exec_mem_nop]
  · simp only [exec, hh, ↓reduceIte]

end X86
end Keccaktree.Asm
