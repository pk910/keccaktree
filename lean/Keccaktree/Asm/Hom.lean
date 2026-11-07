import Keccaktree.Asm.Lemmas
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
`exec` commutes with mapping a lane-operation homomorphism over the state.
Instantiated with `E.eval env` (symbolic ↦ concrete) and `E.subst σ`
(one cut's variables ↦ the previous slice's results).
-/
namespace Keccaktree.Asm

/-- A map of lane values that respects the lane operations and known constants. -/
structure IsHom [LaneOps α] [LaneOps β] (f : α → β) : Prop where
  const : ∀ v, f (LaneOps.const v) = LaneOps.const v
  xor : ∀ a b, f (LaneOps.xor a b) = LaneOps.xor (f a) (f b)
  and : ∀ a b, f (LaneOps.and a b) = LaneOps.and (f a) (f b)
  or : ∀ a b, f (LaneOps.or a b) = LaneOps.or (f a) (f b)
  not : ∀ a, f (LaneOps.not a) = LaneOps.not (f a)
  shl : ∀ a n, f (LaneOps.shl a n) = LaneOps.shl (f a) n
  shr : ∀ a n, f (LaneOps.shr a n) = LaneOps.shr (f a) n
  rol : ∀ a n, f (LaneOps.rol a n) = LaneOps.rol (f a) n
  add : ∀ a b, f (LaneOps.add a b) = LaneOps.add (f a) (f b)
  ternlog : ∀ imm a b c, f (LaneOps.ternlog imm a b c) = LaneOps.ternlog imm (f a) (f b) (f c)
  asConst : ∀ a v, LaneOps.asConst a = some v → LaneOps.asConst (f a) = some v

theorem E.eval_isHom (env : Nat → BitVec 64) : IsHom (E.eval env) where
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
  asConst a v h := by
    show some (E.eval env a) = some v
    rw [E.closed_eval env a v h]

theorem E.subst_isHom (σ : Nat → E) : IsHom (E.subst σ) where
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
  asConst a v h := E.closed_subst σ a v h

namespace X86
open LaneOps
variable {α β : Type} [LaneOps α] [LaneOps β] {f : α → β} (hf : IsHom f)
include hf

/-! ## The state components under `mapState` -/

theorem getV_map (s : State α) (n : Nat) : (mapState f s).getV n = (s.getV n).map f := by
  simp only [State.getV, mapState, Vector.getD]
  rcases h : s.v[n]? with _ | v <;> simp [h, hf.const, Vector.toList_map]

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

omit hf in
@[simp] theorem fail_map (s : State α) : (mapState f s).fail = mapState f s.fail := rfl
omit hf in
@[simp] theorem fail_err (s : State α) : s.fail.err = true := rfl
omit hf in
@[simp] theorem halted_map (s : State α) : (mapState f s).halted = s.halted := rfl
omit hf in
@[simp] theorem err_map (s : State α) : (mapState f s).err = s.err := rfl
omit hf in
@[simp] theorem pc_map (s : State α) : (mapState f s).pc = s.pc := rfl
omit hf in
@[simp] theorem depth_map (s : State α) : (mapState f s).depth = s.depth := rfl
omit hf in
@[simp] theorem k_map (s : State α) : (mapState f s).k = s.k := rfl
omit hf in
@[simp] theorem zf_map (s : State α) : (mapState f s).zf = s.zf := rfl
omit hf in
@[simp] theorem cf_map (s : State α) : (mapState f s).cf = s.cf := rfl
omit hf in
@[simp] theorem vl_map (s : State α) : (mapState f s).vl = s.vl := rfl
omit hf in
@[simp] theorem nf_map (s : State α) : (mapState f s).nf = s.nf := rfl
omit hf in
@[simp] theorem vf_map (s : State α) : (mapState f s).vf = s.vf := rfl
omit hf in
@[simp] theorem g_map (s : State α) : (mapState f s).g = s.g := rfl
omit hf in
@[simp] theorem tail_map (s : State α) : (mapState f s).tail = s.tail := rfl
omit hf in
@[simp] theorem gd_map (s : State α) : (mapState f s).gd = s.gd.map f := rfl
omit hf in
@[simp] theorem v_map (s : State α) : (mapState f s).v = s.v.map (·.map f) := rfl
omit hf in
@[simp] theorem mem_map (s : State α) : (mapState f s).mem = fun r q => f (s.mem r q) := rfl
omit hf in
theorem next_map (s : State α) : next (mapState f s) = mapState f (next s) := rfl
omit hf in
theorem map_upd_pc (s : State α) (p : Nat) : mapState f { s with pc := p } = { mapState f s with pc := p } := rfl
omit hf in
theorem map_upd_pc_depth (s : State α) (p d : Nat) :
    mapState f { s with pc := p, depth := d } = { mapState f s with pc := p, depth := d } := rfl
omit hf in
theorem map_upd_zf (s : State α) (z : Bool) : mapState f { s with zf := z } = { mapState f s with zf := z } := rfl
omit hf in
theorem map_upd_cf (s : State α) (c : Bool) : mapState f { s with cf := c } = { mapState f s with cf := c } := rfl
omit hf in
theorem map_upd_zf_cf (s : State α) (z c : Bool) :
    mapState f { s with zf := z, cf := c } = { mapState f s with zf := z, cf := c } := rfl
omit hf in
theorem map_upd_halted (s : State α) : mapState f { s with halted := true } = { mapState f s with halted := true } := rfl
omit hf in
theorem map_upd_tail (s : State α) (n : String) :
    mapState f { s with halted := true, tail := some n } = { mapState f s with halted := true, tail := some n } := rfl
omit hf in
theorem map_upd_k (s : State α) (k : Vector Nat 8) : mapState f { s with k := k } = { mapState f s with k := k } := rfl
omit hf in
theorem condHolds_map (s : State α) (c : Cond) : condHolds (mapState f s) c = condHolds s c := by cases c <;> rfl
omit hf in
theorem setFlagsSub_map (s : State α) (a b : Addr) : setFlagsSub (mapState f s) a b = mapState f (setFlagsSub s a b) := by
  simp only [setFlagsSub]; split <;> rfl

theorem read_map (rodata : Array (BitVec 64)) (s : State α) (r : Region) (q : Int) :
    (mapState f s).read rodata r q = f (s.read rodata r q) := by
  simp only [State.read, mapState]
  split
  · split <;> simp [hf.const]
  · rfl

theorem loadWords_map (rodata : Array (BitVec 64)) (s : State α) (a : Addr) (n : Nat) :
    (mapState f s).loadWords rodata a n = (s.loadWords rodata a n).map (List.map f) := by
  simp only [State.loadWords]
  split <;> simp [read_map hf]

omit hf in
theorem memStore_map (m : Region → Int → α) (r : Region) (q : Int) (v : α) :
    memStore (fun r q => f (m r q)) r q (f v) = fun r' q' => f (memStore m r q v r' q') := by
  funext r' q'; simp only [memStore]; split <;> rfl

omit hf in
theorem memStoreFrom_map (m : Region → Int → α) (r : Region) (q : Int) (vs : List α) :
    memStoreFrom (fun r q => f (m r q)) r q (vs.map f) = fun r' q' => f (memStoreFrom m r q vs r' q') := by
  induction vs generalizing m q with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons, memStoreFrom, memStore_map]; exact ih (memStore m r q v) (q + 1)

theorem storeWords_map (s : State α) (a : Addr) (vs : List α) :
    (mapState f s).storeWords a (vs.map f) = (s.storeWords a vs).map (mapState f) := by
  simp only [State.storeWords]
  split
  · simp only [Option.map_some, mapState, memStoreFrom_map]
  · rfl

omit hf in
theorem storeWords_err (st s' : State α) (a : Addr) (vs : List α) (h : st.storeWords a vs = some s') : s'.err = st.err := by
  simp only [State.storeWords] at h
  split at h
  · cases h; rfl
  · cases h

theorem getD_map (l : List α) (i : Nat) : (l.map f).getD i (LaneOps.const 0) = f (l.getD i (LaneOps.const 0)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hf.const]

theorem headD_map (l : List α) : (l.map f).headD (LaneOps.const 0) = f (l.headD (LaneOps.const 0)) := by
  cases l <;> simp [hf.const]

theorem writeV_map (s : State α) (n lanes : Nat) (vs : List α) :
    writeV (mapState f s) n lanes (vs.map f) = mapState f (writeV s n lanes vs) := by
  simp only [writeV, State.setV, mapState, Vector.map_setIfInBounds]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  split
  · simp [List.getD_eq_getElem?_getD, hf.const]
    cases vs[i]? <;> simp [hf.const]
  · simp [hf.const]

theorem writeV_map' (s : State α) (n lanes : Nat) (vs : List α) (vs' : List β) (h : vs' = vs.map f) :
    writeV (mapState f s) n lanes vs' = mapState f (writeV s n lanes vs) := by
  subst h; exact writeV_map hf s n lanes vs

omit hf in
theorem foldl_hom {γ δ ι : Type} (g : γ → δ) (step : γ → ι → γ) (step' : δ → ι → δ)
    (h : ∀ acc i, g (step acc i) = step' (g acc) i) (l : List ι) (init : γ) :
    g (l.foldl step init) = l.foldl step' (g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ih, h]

theorem lane128_map (xs : List α) (j : Nat) : lane128 (xs.map f) j = (lane128 xs j).map f := by
  simp only [lane128, List.map_cons, List.map_nil, getD_map hf]

theorem optGetD_map (o : Option α) : (o.map f).getD (LaneOps.const 0) = f (o.getD (LaneOps.const 0)) := by
  rcases o with _ | x <;> simp [hf.const]

theorem getElem?_map_getD (l : List α) (i : Nat) :
    (l.map f)[i]?.getD (LaneOps.const 0) = f (l[i]?.getD (LaneOps.const 0)) := by
  rw [List.getElem?_map]; exact optGetD_map hf _

omit hf in
theorem map_ite (c : Prop) [Decidable c] (x y : α) : f (if c then x else y) = if c then f x else f y := by
  split <;> rfl

omit hf in
theorem map_ite_list (c : Prop) [Decidable c] (l1 l2 : List α) :
    (if c then l1 else l2).map f = if c then l1.map f else l2.map f := by
  split <;> rfl

theorem alignr_map (bs as_ : List α) (j : Nat) :
    lane128 (bs.map f) j ++ lane128 (as_.map f) j ++ [LaneOps.const 0, LaneOps.const 0] =
      (lane128 bs j ++ lane128 as_ j ++ [LaneOps.const 0, LaneOps.const 0]).map f := by
  simp only [lane128_map hf, List.map_append, List.map_cons, List.map_nil, hf.const]

omit hf in
theorem ite_map (c : Prop) [Decidable c] (x y : α) : (if c then f x else f y) = f (if c then x else y) := by
  split <;> rfl

omit hf in
theorem ite_map_list (c : Prop) [Decidable c] (l1 l2 : List α) :
    (if c then l1.map f else l2.map f) = (if c then l1 else l2).map f := by
  split <;> rfl

omit hf in
theorem foldr_cons2_map {ι : Type} (x y : ι → α) (r : List ι) :
    List.foldr (fun j acc => f (x j) :: f (y j) :: acc) [] r = (List.foldr (fun j acc => x j :: y j :: acc) [] r).map f := by
  induction r with
  | nil => rfl
  | cons j r ih => simp [List.foldr_cons, ih]

omit hf in
theorem foldr_append_map {ι : Type} (g : ι → List α) (r : List ι) :
    List.foldr (fun j acc => (g j).map f ++ acc) [] r = (List.foldr (fun j acc => g j ++ acc) [] r).map f := by
  induction r with
  | nil => rfl
  | cons j r ih => simp [List.foldr_cons, ih]

omit hf in
theorem zipWith_map_hom (g : α → α → α) (g' : β → β → β) (hg : ∀ x y, g' (f x) (f y) = f (g x y)) (l1 l2 : List α) :
    List.zipWith g' (l1.map f) (l2.map f) = (List.zipWith g l1 l2).map f := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons x l ih => cases l2 <;> simp [ih, hg]

/-- If every symbolic lane is a known constant, the mapped lanes are the same constants. -/
theorem asConst_map_all (l : List α) (h : (l.map LaneOps.asConst).all Option.isSome = true) :
    (l.map f).map LaneOps.asConst = l.map LaneOps.asConst := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    rcases hx : LaneOps.asConst x with _ | v
    · simp [hx] at h
    · simp only [List.map_cons, hf.asConst x v hx, hx, ih h.2]

theorem allSome_map (l : List (Option α)) : allSome (l.map (Option.map f)) = (allSome l).map (List.map f) := by
  simp only [allSome, List.all_map, Function.comp_def, Option.isSome_map]
  split
  · simp only [Option.map_some, List.map_map]
    congr 1
    apply List.map_congr_left
    intro o _
    cases o <;> simp [hf.const]
  · rfl

/-- One word of `vpshufb`: the fold commutes with `f`. -/
theorem shufbWord_map (lo hi : α) (cw : BitVec 64) :
    (List.range 8).foldl (fun acc i =>
        let m := ((cw >>> (8 * i)) &&& 0xff#64).toNat
        if m &&& 0x80 ≠ 0 then acc
        else
          let src := if (m &&& 15) < 8 then LaneOps.and (LaneOps.shr (f lo) (8 * (m &&& 15))) (LaneOps.const 0xff#64)
                     else LaneOps.and (LaneOps.shr (f hi) (8 * ((m &&& 15) - 8))) (LaneOps.const 0xff#64)
          LaneOps.or acc (LaneOps.shl src (8 * i))) (LaneOps.const 0) =
    f ((List.range 8).foldl (fun acc i =>
        let m := ((cw >>> (8 * i)) &&& 0xff#64).toNat
        if m &&& 0x80 ≠ 0 then acc
        else
          let src := if (m &&& 15) < 8 then LaneOps.and (LaneOps.shr lo (8 * (m &&& 15))) (LaneOps.const 0xff#64)
                     else LaneOps.and (LaneOps.shr hi (8 * ((m &&& 15) - 8))) (LaneOps.const 0xff#64)
          LaneOps.or acc (LaneOps.shl src (8 * i))) (LaneOps.const 0)) := by
  rw [foldl_hom f _ _ ?_ _ _, hf.const]
  intro acc i
  dsimp only
  split
  · rfl
  · simp only [hf.or, hf.shl]; split <;> simp [hf.and, hf.shr, hf.const]

theorem shufb128_map' (lo hi : α) (c0 c1 : BitVec 64) :
    shufb128 (f lo) (f hi) c0 c1 = (f (shufb128 lo hi c0 c1).1, f (shufb128 lo hi c0 c1).2) := by
  simp only [shufb128]
  exact Prod.ext (shufbWord_map hf lo hi c0) (shufbWord_map hf lo hi c1)

theorem aluOp_map (op : AluOp) (x y : α) : aluOp op (f x) (f y) = f (aluOp op x y) := by
  cases op <;> simp [aluOp, hf.xor, hf.and, hf.or, hf.add]

/-! ## Registers as words, addresses -/

theorem gx_map_some (s : State α) (n : Nat) (a : Addr) (h : gx s n = some a) : gx (mapState f s) n = some a := by
  simp only [gx, getGD_map hf] at h ⊢
  rcases hc : LaneOps.asConst (s.getGD n) with _ | w
  · simp [hc] at h
  · rw [hf.asConst _ _ hc]; simp only [hc, Option.map_some] at h; simp only [Option.map_some, h]

theorem setX_map (s : State α) (n : Nat) (a : Addr) : setX (mapState f s) n a = mapState f (setX s n a) := by
  simp only [setX]; exact setGD_map' s n _ _ (hf.const _)

theorem memAddr?_map_some (s : State α) (m : MemOp) (a : Addr) (h : memAddr? s m = some a) :
    memAddr? (mapState f s) m = some a := by
  cases m with
  | base g disp =>
    simp only [memAddr?] at h ⊢
    rcases hx : gx s g with _ | x
    · simp [hx] at h
    · rw [gx_map_some hf _ _ _ hx]; simp only [hx, Option.map_some] at h; simp only [Option.map_some, h]
  | rip off => exact h

theorem readSrc_map_some (rodata : Array (BitVec 64)) (s : State α) (lanes : Nat) (src : Src) (bs : List α)
    (h : readSrc rodata s lanes src = some bs) : readSrc rodata (mapState f s) lanes src = some (bs.map f) := by
  cases src with
  | reg n => simp only [readSrc, Option.some.injEq] at h ⊢; rw [getV_map hf, ← List.map_take, h]
  | mem m =>
    simp only [readSrc] at h ⊢
    rcases ha : memAddr? s m with _ | a
    · simp [ha] at h
    · rw [memAddr?_map_some hf _ _ _ ha]; simp only [ha, Option.bind_some] at h ⊢
      rw [loadWords_map hf, h]; rfl
  | bcst m =>
    simp only [readSrc] at h ⊢
    rcases ha : memAddr? s m with _ | a
    · simp [ha] at h
    · rw [memAddr?_map_some hf _ _ _ ha]; simp only [ha, Option.bind_some] at h ⊢
      rw [loadWords_map hf]
      rcases hl : s.loadWords rodata a 1 with _ | l
      · simp [hl] at h
      · simp only [hl, Option.map_some, Option.some.injEq] at h ⊢
        rw [← h]; cases l <;> simp [hf.const, List.map_replicate]

/-! ## The combinators -/

theorem withX_map (s : State α) (n : Nat) (k : Addr → State α) (k' : Addr → State β)
    (hne : (withX s n k).err = false)
    (hk : ∀ a, gx s n = some a → (k a).err = false → k' a = mapState f (k a)) :
    withX (mapState f s) n k' = mapState f (withX s n k) := by
  simp only [withX] at hne ⊢
  rcases hx : gx s n with _ | a
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [gx_map_some hf _ _ _ hx, hk a hx hne]

theorem withMem_map (s : State α) (m : MemOp) (k : Addr → State α) (k' : Addr → State β)
    (hne : (withMem s m k).err = false)
    (hk : ∀ a, memAddr? s m = some a → (k a).err = false → k' a = mapState f (k a)) :
    withMem (mapState f s) m k' = mapState f (withMem s m k) := by
  simp only [withMem] at hne ⊢
  rcases hx : memAddr? s m with _ | a
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [memAddr?_map_some hf _ _ _ hx, hk a hx hne]

theorem withSrc_map (rodata : Array (BitVec 64)) (s : State α) (lanes : Nat) (b : Src)
    (k : List α → State α) (k' : List β → State β)
    (hne : (withSrc rodata s lanes b k).err = false)
    (hk : ∀ bs, readSrc rodata s lanes b = some bs → (k bs).err = false → k' (bs.map f) = mapState f (k bs)) :
    withSrc rodata (mapState f s) lanes b k' = mapState f (withSrc rodata s lanes b k) := by
  simp only [withSrc] at hne ⊢
  rcases hx : readSrc rodata s lanes b with _ | bs
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [readSrc_map_some hf _ _ _ _ _ hx, hk bs hx hne]

theorem withLoad_map (rodata : Array (BitVec 64)) (s : State α) (a : Addr) (n : Nat)
    (k : List α → State α) (k' : List β → State β)
    (hne : (withLoad rodata s a n k).err = false)
    (hk : ∀ ws, s.loadWords rodata a n = some ws → (k ws).err = false → k' (ws.map f) = mapState f (k ws)) :
    withLoad rodata (mapState f s) a n k' = mapState f (withLoad rodata s a n k) := by
  simp only [withLoad, loadWords_map hf] at hne ⊢
  rcases hx : s.loadWords rodata a n with _ | ws
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [Option.map_some, hk ws hx hne]

theorem withStore_map (s : State α) (a : Addr) (vs : List α) (vs' : List β) (hv : vs' = vs.map f)
    (k : State α → State α) (k' : State β → State β)
    (hne : (withStore s a vs k).err = false)
    (hk : ∀ s', s.storeWords a vs = some s' → (k s').err = false → k' (mapState f s') = mapState f (k s')) :
    withStore (mapState f s) a vs' k' = mapState f (withStore s a vs k) := by
  subst hv
  simp only [withStore, storeWords_map hf] at hne ⊢
  rcases hx : s.storeWords a vs with _ | s'
  · simp only [hx, fail_err] at hne; exact absurd hne (by decide)
  · simp only [hx] at hne; simp only [Option.map_some, hk s' hx hne]

theorem readG_map (rodata : Array (BitVec 64)) (s : State α) (b : GSrc) (k : α → State α) (k' : β → State β)
    (hne : (readG rodata s b k).err = false)
    (hk : ∀ y, (k y).err = false → k' (f y) = mapState f (k y)) :
    readG rodata (mapState f s) b k' = mapState f (readG rodata s b k) := by
  cases b with
  | reg g => simp only [readG, getGD_map hf] at hne ⊢; exact hk _ hne
  | imm i => simp only [readG] at hne ⊢; rw [← hf.const]; exact hk _ hne
  | mem m =>
    simp only [readG] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    apply withLoad_map hf _ _ _ _ _ _ hne2
    intro ws _ hne3
    rw [headD_map hf]; exact hk _ hne3

omit hf in
theorem binop_err {rodata : Array (BitVec 64)} {s : State α} {lanes d a : Nat} {b : Src} {g : α → α → α}
    (hne : (binop rodata s lanes d a b g).err = false) :
    (withSrc rodata s lanes b fun bs => next (writeV s d lanes (List.zipWith g ((s.getV a).take lanes) bs))).err = false := hne

theorem binop_map (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) (g : α → α → α) (g' : β → β → β)
    (hg : ∀ x y, g' (f x) (f y) = f (g x y)) (hne : (binop rodata s lanes d a b g).err = false) :
    binop rodata (mapState f s) lanes d a b g' = mapState f (binop rodata s lanes d a b g) := by
  simp only [binop]
  apply withSrc_map hf _ _ _ _ _ _ hne
  intro bs _ _
  rw [← next_map]; apply congrArg next
  apply writeV_map' hf
  rw [getV_map hf, ← List.map_take, zipWith_map_hom g g' hg]

/-- The vector instructions after `withSrc`/no source: `next (writeV ..)` with the lanes
built from the lane operations. -/
syntax "x86_vec" : tactic
macro_rules
  | `(tactic| x86_vec) => `(tactic| (
      rw [← next_map]; apply congrArg next
      apply writeV_map' hf
      simp only [getV_map hf, ← List.map_take, List.map_map, Function.comp_def, getD_map hf,
        getElem?_map_getD hf, optGetD_map hf, lane128_map hf, List.map_append, List.map_cons, List.map_nil,
        hf.const, hf.xor, hf.and, hf.or, hf.not, hf.shl, hf.shr, hf.rol, hf.add, hf.ternlog, map_ite,
        foldr_cons2_map, foldr_append_map, shufb128_map' hf]
      try rfl))

/-- `exec` commutes with a lane homomorphism, as long as the (symbolic) run does not fail;
one lemma per instruction. -/
theorem exec_map_vmov (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (dst : _) (src : _) (mask : _)
    (hne : (exec rodata (.vmov lanes dst src mask) st).err = false) :
    exec rodata (.vmov lanes dst src mask) (mapState f st) = mapState f (exec rodata (.vmov lanes dst src mask) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro vs _ _
    simp only [k_map]
    rw [← next_map]; apply congrArg next
    apply writeV_map' hf
    cases mask with
    | none => rfl
    | some k =>
      simp only [getV_map hf, List.map_map, Function.comp_def, getD_map hf, map_ite]
  · simp [exec, mapState, hh]

theorem exec_map_vstore (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (dst : _) (src : _)
    (hne : (exec rodata (.vstore lanes dst src) st).err = false) :
    exec rodata (.vstore lanes dst src) (mapState f st) = mapState f (exec rodata (.vstore lanes dst src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    apply withStore_map hf _ _ _ _ (by rw [getV_map hf, List.map_take]) _ _ hne2
    intro s' _ _; rfl
  · simp [exec, mapState, hh]

theorem exec_map_vpxor (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpxor lanes d a b) st).err = false) :
    exec rodata (.vpxor lanes d a b) (mapState f st) = mapState f (exec rodata (.vpxor lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_map hf _ _ _ _ _ _ _ _ (fun x y => (hf.xor x y).symm) hne
  · simp [exec, mapState, hh]

theorem exec_map_vpand (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpand lanes d a b) st).err = false) :
    exec rodata (.vpand lanes d a b) (mapState f st) = mapState f (exec rodata (.vpand lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_map hf _ _ _ _ _ _ _ _ (fun x y => (hf.and x y).symm) hne
  · simp [exec, mapState, hh]

theorem exec_map_vpandn (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpandn lanes d a b) st).err = false) :
    exec rodata (.vpandn lanes d a b) (mapState f st) = mapState f (exec rodata (.vpandn lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_map hf _ _ _ _ _ _ _ _ (fun x y => by simp [hf.and, hf.not]) hne
  · simp [exec, mapState, hh]

theorem exec_map_vpor (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpor lanes d a b) st).err = false) :
    exec rodata (.vpor lanes d a b) (mapState f st) = mapState f (exec rodata (.vpor lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_map hf _ _ _ _ _ _ _ _ (fun x y => (hf.or x y).symm) hne
  · simp [exec, mapState, hh]

theorem exec_map_vpaddq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpaddq lanes d a b) st).err = false) :
    exec rodata (.vpaddq lanes d a b) (mapState f st) = mapState f (exec rodata (.vpaddq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    exact binop_map hf _ _ _ _ _ _ _ _ (fun x y => (hf.add x y).symm) hne
  · simp [exec, mapState, hh]

theorem exec_map_vpsllq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vpsllq lanes d a imm) st).err = false) :
    exec rodata (.vpsllq lanes d a imm) (mapState f st) = mapState f (exec rodata (.vpsllq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; x86_vec
  · simp [exec, mapState, hh]

theorem exec_map_vpsrlq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vpsrlq lanes d a imm) st).err = false) :
    exec rodata (.vpsrlq lanes d a imm) (mapState f st) = mapState f (exec rodata (.vpsrlq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; x86_vec
  · simp [exec, mapState, hh]

theorem exec_map_vprolq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vprolq lanes d a imm) st).err = false) :
    exec rodata (.vprolq lanes d a imm) (mapState f st) = mapState f (exec rodata (.vprolq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; x86_vec
  · simp [exec, mapState, hh]

theorem exec_map_vpsllvq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpsllvq lanes d a b) st).err = false) :
    exec rodata (.vpsllvq lanes d a b) (mapState f st) = mapState f (exec rodata (.vpsllvq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ hne2
    rcases hall : (bs.map LaneOps.asConst).all Option.isSome with _ | _
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [asConst_map_all hf bs hall, hall, ↓reduceIte]; x86_vec
  · simp [exec, mapState, hh]

theorem exec_map_vpsrlvq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpsrlvq lanes d a b) st).err = false) :
    exec rodata (.vpsrlvq lanes d a b) (mapState f st) = mapState f (exec rodata (.vpsrlvq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ hne2
    rcases hall : (bs.map LaneOps.asConst).all Option.isSome with _ | _
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [asConst_map_all hf bs hall, hall, ↓reduceIte]; x86_vec
  · simp [exec, mapState, hh]

theorem exec_map_vpternlogq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vpternlogq lanes d a b imm) st).err = false) :
    exec rodata (.vpternlogq lanes d a b imm) (mapState f st) = mapState f (exec rodata (.vpternlogq lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ _; x86_vec
  · simp [exec, mapState, hh]

theorem exec_map_vpshufb (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (ctrl : _)
    (hne : (exec rodata (.vpshufb lanes d a ctrl) st).err = false) :
    exec rodata (.vpshufb lanes d a ctrl) (mapState f st) = mapState f (exec rodata (.vpshufb lanes d a ctrl) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro cs _ hne2
    rcases hall : (cs.map LaneOps.asConst).all Option.isSome with _ | _
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [asConst_map_all hf cs hall, hall, ↓reduceIte]
      rw [← next_map]; apply congrArg next
      apply writeV_map' hf
      simp only [getV_map hf, ← List.map_take, getD_map hf, shufb128_map' hf, foldr_cons2_map]
  · simp [exec, mapState, hh]

theorem exec_map_vpshufd (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vpshufd lanes d a imm) st).err = false) :
    exec rodata (.vpshufd lanes d a imm) (mapState f st) = mapState f (exec rodata (.vpshufd lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    have hl : ((List.range lanes).map fun i => (qwordSel imm (i % 2)).map fun q =>
        (((mapState f st).getV a).take lanes).getD (2 * (i / 2) + q) (LaneOps.const 0)) =
        ((List.range lanes).map fun i => (qwordSel imm (i % 2)).map fun q =>
        ((st.getV a).take lanes).getD (2 * (i / 2) + q) (LaneOps.const 0)).map (Option.map f) := by
      simp only [List.map_map, Function.comp_def, Option.map_map, getV_map hf, ← List.map_take, getD_map hf]
    rw [hl, allSome_map hf]
    rcases hs : allSome ((List.range lanes).map fun i => (qwordSel imm (i % 2)).map fun q =>
        ((st.getV a).take lanes).getD (2 * (i / 2) + q) (LaneOps.const 0)) with _ | r
    · simp only [hs, fail_err] at hne; exact absurd hne (by decide)
    · simp only [Option.map_some, next_map, writeV_map hf]
  · simp [exec, mapState, hh]

theorem exec_map_vpblendd (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vpblendd lanes d a b imm) st).err = false) :
    exec rodata (.vpblendd lanes d a b imm) (mapState f st) = mapState f (exec rodata (.vpblendd lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ hne2
    have hl : ((List.range lanes).map fun i =>
        if imm.testBit (2 * i) = imm.testBit (2 * i + 1) then
          some (if imm.testBit (2 * i) then (bs.map f).getD i (LaneOps.const 0)
                else (((mapState f st).getV a).take lanes).getD i (LaneOps.const 0))
        else none) =
        ((List.range lanes).map fun i =>
        if imm.testBit (2 * i) = imm.testBit (2 * i + 1) then
          some (if imm.testBit (2 * i) then bs.getD i (LaneOps.const 0)
                else ((st.getV a).take lanes).getD i (LaneOps.const 0))
        else none).map (Option.map f) := by
      simp only [List.map_map, Function.comp_def, getV_map hf, ← List.map_take]
      apply List.map_congr_left; intro i _
      split
      · simp only [Option.map_some, map_ite, getD_map hf]
      · rfl
    rw [hl, allSome_map hf]
    rcases hs : allSome ((List.range lanes).map fun i =>
        if imm.testBit (2 * i) = imm.testBit (2 * i + 1) then
          some (if imm.testBit (2 * i) then bs.getD i (LaneOps.const 0)
                else ((st.getV a).take lanes).getD i (LaneOps.const 0))
        else none) with _ | r
    · simp only [hs, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [Option.map_some, next_map, writeV_map hf]
  · simp [exec, mapState, hh]

theorem exec_map_vpalignr (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vpalignr lanes d a b imm) st).err = false) :
    exec rodata (.vpalignr lanes d a b imm) (mapState f st) = mapState f (exec rodata (.vpalignr lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ hne2
    by_cases hc : imm % 8 = 0 ∧ imm ≤ 32
    · simp only [hc, and_self, ↓reduceIte] at hne2 ⊢
      rw [← next_map]; apply congrArg next
      apply writeV_map' hf
      rw [getV_map hf, ← List.map_take]
      simp only [alignr_map hf, getD_map hf, foldr_cons2_map]
    · simp only [hc, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
  · simp [exec, mapState, hh]

theorem exec_map_vpunpcklqdq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpunpcklqdq lanes d a b) st).err = false) :
    exec rodata (.vpunpcklqdq lanes d a b) (mapState f st) = mapState f (exec rodata (.vpunpcklqdq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ _; x86_vec
  · simp [exec, mapState, hh]

theorem exec_map_vpunpckhqdq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpunpckhqdq lanes d a b) st).err = false) :
    exec rodata (.vpunpckhqdq lanes d a b) (mapState f st) = mapState f (exec rodata (.vpunpckhqdq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ _; x86_vec
  · simp [exec, mapState, hh]

theorem exec_map_vperm2i128 (rodata : Array (BitVec 64)) (st : State α) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vperm2i128 d a b imm) st).err = false) :
    exec rodata (.vperm2i128 d a b imm) (mapState f st) = mapState f (exec rodata (.vperm2i128 d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ _
    rw [← next_map]; apply congrArg next
    apply writeV_map' hf
    have hz : ([LaneOps.const 0, LaneOps.const 0] : List β) = [LaneOps.const 0, LaneOps.const 0].map f := by simp [hf.const]
    rw [getV_map hf, ← List.map_take]
    simp only [hz, lane128_map hf, List.map_append]
    congr 1 <;> (split <;> (try rfl) <;> split <;> rfl)
  · simp [exec, mapState, hh]

theorem exec_map_vinserti128 (rodata : Array (BitVec 64)) (st : State α) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vinserti128 d a b imm) st).err = false) :
    exec rodata (.vinserti128 d a b imm) (mapState f st) = mapState f (exec rodata (.vinserti128 d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ _
    rw [← next_map]; apply congrArg next
    apply writeV_map' hf
    rw [getV_map hf, ← List.map_take]
    simp only [map_ite_list, List.map_append, lane128_map hf]
  · simp [exec, mapState, hh]

theorem exec_map_vextracti128 (rodata : Array (BitVec 64)) (st : State α) (m : _) (a : _) (imm : _)
    (hne : (exec rodata (.vextracti128 m a imm) st).err = false) :
    exec rodata (.vextracti128 m a imm) (mapState f st) = mapState f (exec rodata (.vextracti128 m a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro ad _ hne2
    apply withStore_map hf _ _ _ _ (by rw [getV_map hf, ← List.map_take, lane128_map hf]) _ _ hne2
    intro s' _ _; rfl
  · simp [exec, mapState, hh]

theorem exec_map_vshufi64x2 (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vshufi64x2 lanes d a b imm) st).err = false) :
    exec rodata (.vshufi64x2 lanes d a b imm) (mapState f st) = mapState f (exec rodata (.vshufi64x2 lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ _
    rw [← next_map]; apply congrArg next
    apply writeV_map' hf
    rw [getV_map hf, ← List.map_take]
    simp only [ite_map_list, lane128_map hf, foldr_append_map]
  · simp [exec, mapState, hh]

theorem exec_map_vpermt2q (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (idx : _) (b : _)
    (hne : (exec rodata (.vpermt2q lanes d idx b) st).err = false) :
    exec rodata (.vpermt2q lanes d idx b) (mapState f st) = mapState f (exec rodata (.vpermt2q lanes d idx b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withSrc_map hf _ _ _ _ _ _ hne
    intro bs _ hne2
    have hv : ((mapState f st).getV idx).take lanes = ((st.getV idx).take lanes).map f := by
      rw [getV_map hf, List.map_take]
    rw [hv]
    rcases hall : (((st.getV idx).take lanes).map LaneOps.asConst).all Option.isSome with _ | _
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, fail_err] at hne2; exact absurd hne2 (by decide)
    · rw [asConst_map_all hf _ hall]
      simp only [hall, ↓reduceIte]
      rw [← next_map]; apply congrArg next
      apply writeV_map' hf
      rw [getV_map hf, ← List.map_take]
      simp only [List.map_map, Function.comp_def, getD_map hf, map_ite]
  · simp [exec, mapState, hh]

theorem exec_map_kmovw (rodata : Array (BitVec 64)) (st : State α) (k : _) (m : _)
    (hne : (exec rodata (.kmovw k m) st).err = false) :
    exec rodata (.kmovw k m) (mapState f st) = mapState f (exec rodata (.kmovw k m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    rw [read_map hf]
    rcases hc : LaneOps.asConst (st.read rodata a.region (a.off / 8)) with _ | w
    · simp only [hc, fail_err] at hne2; exact absurd hne2 (by decide)
    · simp only [hf.asConst _ _ hc]; rfl
  · simp [exec, mapState, hh]

theorem exec_map_vzeroupper (rodata : Array (BitVec 64)) (st : State α)
    (hne : (exec rodata (.vzeroupper) st).err = false) :
    exec rodata (.vzeroupper) (mapState f st) = mapState f (exec rodata (.vzeroupper) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_mov (rodata : Array (BitVec 64)) (st : State α) (d : _) (src : _)
    (hne : (exec rodata (.mov d src) st).err = false) :
    exec rodata (.mov d src) (mapState f st) = mapState f (exec rodata (.mov d src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
    rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [getGD_map hf]))
  · simp [exec, mapState, hh]

theorem exec_map_xchg (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _)
    (hne : (exec rodata (.xchg a b) st).err = false) :
    exec rodata (.xchg a b) (mapState f st) = mapState f (exec rodata (.xchg a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
    rw [← next_map, getGD_map hf, getGD_map hf, setGD_map, setGD_map]
  · simp [exec, mapState, hh]

theorem exec_map_movi (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.movi d imm) st).err = false) :
    exec rodata (.movi d imm) (mapState f st) = mapState f (exec rodata (.movi d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
    rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [hf.const]))
  · simp [exec, mapState, hh]

theorem exec_map_lea (rodata : Array (BitVec 64)) (st : State α) (d : _) (m : _)
    (hne : (exec rodata (.lea d m) st).err = false) :
    exec rodata (.lea d m) (mapState f st) = mapState f (exec rodata (.lea d m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ _; simp only [setX_map hf, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_add (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.add d imm) st).err = false) :
    exec rodata (.add d imm) (mapState f st) = mapState f (exec rodata (.add d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro a _ _; simp only [setX_map hf, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_sub (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.sub d imm) st).err = false) :
    exec rodata (.sub d imm) (mapState f st) = mapState f (exec rodata (.sub d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro a _ _; split <;> simp only [setX_map hf, setFlagsSub_map, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_andi (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.andi d imm) st).err = false) :
    exec rodata (.andi d imm) (mapState f st) = mapState f (exec rodata (.andi d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro a _ _; split <;> simp only [setX_map hf, next_map, fail_map]
  · simp [exec, mapState, hh]

theorem exec_map_shl (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.shl d imm) st).err = false) :
    exec rodata (.shl d imm) (mapState f st) = mapState f (exec rodata (.shl d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro a _ _; split <;> simp only [setX_map hf, next_map, fail_map]
  · simp [exec, mapState, hh]

theorem exec_map_dec (rodata : Array (BitVec 64)) (st : State α) (d : _)
    (hne : (exec rodata (.dec d) st).err = false) :
    exec rodata (.dec d) (mapState f st) = mapState f (exec rodata (.dec d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro a _ _; rw [← next_map, setX_map hf]; rfl
  · simp [exec, mapState, hh]

theorem exec_map_xorz (rodata : Array (BitVec 64)) (st : State α) (d : _)
    (hne : (exec rodata (.xorz d) st).err = false) :
    exec rodata (.xorz d) (mapState f st) = mapState f (exec rodata (.xorz d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
    rw [← next_map, setX_map hf]; rfl
  · simp [exec, mapState, hh]

theorem exec_map_cmpi (rodata : Array (BitVec 64)) (st : State α) (a : _) (imm : _)
    (hne : (exec rodata (.cmpi a imm) st).err = false) :
    exec rodata (.cmpi a imm) (mapState f st) = mapState f (exec rodata (.cmpi a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro x _ _; simp only [setFlagsSub_map, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_cmpr (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _)
    (hne : (exec rodata (.cmpr a b) st).err = false) :
    exec rodata (.cmpr a b) (mapState f st) = mapState f (exec rodata (.cmpr a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro x _ hne2
    apply withX_map hf _ _ _ _ hne2
    intro y _ _; simp only [setFlagsSub_map, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_cmpm (rodata : Array (BitVec 64)) (st : State α) (m : _) (b : _)
    (hne : (exec rodata (.cmpm m b) st).err = false) :
    exec rodata (.cmpm m b) (mapState f st) = mapState f (exec rodata (.cmpm m b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro ad _ hne2
    apply withLoad_map hf _ _ _ _ _ _ hne2
    intro ws _ hne3
    rw [headD_map hf]
    rcases hc : LaneOps.asConst (ws.headD (LaneOps.const 0)) with _ | v
    · simp only [hc, fail_err] at hne3; exact absurd hne3 (by decide)
    · simp only [hc] at hne3; simp only [hf.asConst _ _ hc]
      apply withX_map hf _ _ _ _ hne3
      intro y _ _; simp only [setFlagsSub_map, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_cmprm (rodata : Array (BitVec 64)) (st : State α) (a : _) (m : _)
    (hne : (exec rodata (.cmprm a m) st).err = false) :
    exec rodata (.cmprm a m) (mapState f st) = mapState f (exec rodata (.cmprm a m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro ad _ hne2
    apply withLoad_map hf _ _ _ _ _ _ hne2
    intro ws _ hne3
    rw [headD_map hf]
    rcases hc : LaneOps.asConst (ws.headD (LaneOps.const 0)) with _ | v
    · simp only [hc, fail_err] at hne3; exact absurd hne3 (by decide)
    · simp only [hc] at hne3; simp only [hf.asConst _ _ hc]
      apply withX_map hf _ _ _ _ hne3
      intro x _ _; simp only [setFlagsSub_map, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_test (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _)
    (hne : (exec rodata (.test a b) st).err = false) :
    exec rodata (.test a b) (mapState f st) = mapState f (exec rodata (.test a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro x _ hne2
    apply withX_map hf _ _ _ _ hne2
    intro y _ _; split <;> (first | rfl | simp only [fail_map])
  · simp [exec, mapState, hh]

theorem exec_map_bt (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _)
    (hne : (exec rodata (.bt a b) st).err = false) :
    exec rodata (.bt a b) (mapState f st) = mapState f (exec rodata (.bt a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, getGD_map hf] at hne ⊢
    rcases hc : LaneOps.asConst (st.getGD a) with _ | w
    · simp only [hc, fail_err] at hne; exact absurd hne (by decide)
    · simp only [hc] at hne; simp only [hf.asConst _ _ hc]
      apply withX_map hf _ _ _ _ hne
      intro y _ _; split <;> (first | rfl | simp only [fail_map])
  · simp [exec, mapState, hh]

theorem exec_map_btc (rodata : Array (BitVec 64)) (st : State α) (a : _) (imm : _)
    (hne : (exec rodata (.btc a imm) st).err = false) :
    exec rodata (.btc a imm) (mapState f st) = mapState f (exec rodata (.btc a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]
    rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [getGD_map hf, hf.xor, hf.const]))
  · simp [exec, mapState, hh]

theorem exec_map_alu (rodata : Array (BitVec 64)) (st : State α) (op : _) (d : _) (b : _)
    (hne : (exec rodata (.alu op d b) st).err = false) :
    exec rodata (.alu op d b) (mapState f st) = mapState f (exec rodata (.alu op d b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply readG_map hf _ _ _ _ _ hne
    intro y _
    rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [getGD_map hf, aluOp_map hf]))
  · simp [exec, mapState, hh]

theorem exec_map_andn (rodata : Array (BitVec 64)) (st : State α) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.andn d a b) st).err = false) :
    exec rodata (.andn d a b) (mapState f st) = mapState f (exec rodata (.andn d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply readG_map hf _ _ _ _ _ hne
    intro y _
    rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [getGD_map hf, hf.and, hf.not]))
  · simp [exec, mapState, hh]

theorem exec_map_rorx (rodata : Array (BitVec 64)) (st : State α) (d : _) (b : _) (imm : _)
    (hne : (exec rodata (.rorx d b imm) st).err = false) :
    exec rodata (.rorx d b imm) (mapState f st) = mapState f (exec rodata (.rorx d b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply readG_map hf _ _ _ _ _ hne
    intro y _
    rw [← next_map]; exact congrArg next (setGD_map' _ _ _ _ (by simp [hf.rol]))
  · simp [exec, mapState, hh]

theorem exec_map_xorm (rodata : Array (BitVec 64)) (st : State α) (m : _) (src : _)
    (hne : (exec rodata (.xorm m src) st).err = false) :
    exec rodata (.xorm m src) (mapState f st) = mapState f (exec rodata (.xorm m src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    apply withLoad_map hf _ _ _ _ _ _ hne2
    intro ws _ hne3
    apply withStore_map hf _ _ _ _ (by rw [headD_map hf, getGD_map hf]; simp only [List.map_cons, List.map_nil, hf.xor]) _ _ hne3
    intro s' _ _; rfl
  · simp [exec, mapState, hh]

theorem exec_map_storeqi (rodata : Array (BitVec 64)) (st : State α) (m : _) (imm : _)
    (hne : (exec rodata (.storeqi m imm) st).err = false) :
    exec rodata (.storeqi m imm) (mapState f st) = mapState f (exec rodata (.storeqi m imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    apply withStore_map hf _ _ _ _ (by simp [hf.const]) _ _ hne2
    intro s' _ _; rfl
  · simp [exec, mapState, hh]

theorem exec_map_addm (rodata : Array (BitVec 64)) (st : State α) (m : _) (imm : _)
    (hne : (exec rodata (.addm m imm) st).err = false) :
    exec rodata (.addm m imm) (mapState f st) = mapState f (exec rodata (.addm m imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    apply withLoad_map hf _ _ _ _ _ _ hne2
    intro ws _ hne3
    apply withStore_map hf _ _ _ _ (by rw [headD_map hf]; simp only [List.map_cons, List.map_nil, hf.add, hf.const]) _ _ hne3
    intro s' _ _; rfl
  · simp [exec, mapState, hh]

theorem exec_map_decm (rodata : Array (BitVec 64)) (st : State α) (m : _)
    (hne : (exec rodata (.decm m) st).err = false) :
    exec rodata (.decm m) (mapState f st) = mapState f (exec rodata (.decm m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    apply withLoad_map hf _ _ _ _ _ _ hne2
    intro ws _ hne3
    rw [headD_map hf]
    rcases hc : LaneOps.asConst (ws.headD (LaneOps.const 0)) with _ | v
    · simp only [hc, fail_err] at hne3; exact absurd hne3 (by decide)
    · simp only [hc] at hne3; simp only [hf.asConst _ _ hc]
      apply withStore_map hf _ _ _ _ (by simp [hf.const]) _ _ hne3
      intro s' _ _; rfl
  · simp [exec, mapState, hh]

theorem exec_map_jcc (rodata : Array (BitVec 64)) (st : State α) (c : _) (t : _)
    (hne : (exec rodata (.jcc c t) st).err = false) :
    exec rodata (.jcc c t) (mapState f st) = mapState f (exec rodata (.jcc c t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, condHolds_map]; rfl
  · simp [exec, mapState, hh]

theorem exec_map_jcct (rodata : Array (BitVec 64)) (st : State α) (c : _) (name : _)
    (hne : (exec rodata (.jcct c name) st).err = false) :
    exec rodata (.jcct c name) (mapState f st) = mapState f (exec rodata (.jcct c name) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, condHolds_map]
    split <;> rfl
  · simp [exec, mapState, hh]

theorem exec_map_jmp (rodata : Array (BitVec 64)) (st : State α) (t : _)
    (hne : (exec rodata (.jmp t) st).err = false) :
    exec rodata (.jmp t) (mapState f st) = mapState f (exec rodata (.jmp t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp [exec, mapState, hh]

theorem exec_map_call (rodata : Array (BitVec 64)) (st : State α) (t : _)
    (hne : (exec rodata (.call t) st).err = false) :
    exec rodata (.call t) (mapState f st) = mapState f (exec rodata (.call t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, pc_map, depth_map] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro sp _ hne2
    apply withStore_map hf _ _ _ _ (by simp [hf.const]) _ _ hne2
    intro s' _ _; rw [setX_map hf]; rfl
  · simp [exec, mapState, hh]

theorem exec_map_ret (rodata : Array (BitVec 64)) (st : State α)
    (hne : (exec rodata (.ret) st).err = false) :
    exec rodata (.ret) (mapState f st) = mapState f (exec rodata (.ret) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, depth_map] at hne ⊢
    by_cases hd : st.depth = 0
    · simp only [hd, ↓reduceIte]; rfl
    · simp only [hd, ↓reduceIte] at hne ⊢
      apply withX_map hf _ _ _ _ hne
      intro sp _ hne2
      apply withLoad_map hf _ _ _ _ _ _ hne2
      intro ws _ hne3
      rw [headD_map hf]
      rcases hc : LaneOps.asConst (ws.headD (LaneOps.const 0)) with _ | ra
      · simp only [hc, fail_err] at hne3; exact absurd hne3 (by decide)
      · simp only [hf.asConst _ _ hc, setX_map hf]; rfl
  · simp [exec, mapState, hh]

theorem exec_map_push (rodata : Array (BitVec 64)) (st : State α) (src : _)
    (hne : (exec rodata (.push src) st).err = false) :
    exec rodata (.push src) (mapState f st) = mapState f (exec rodata (.push src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro sp _ hne2
    apply withStore_map hf _ _ _ _ (by simp [getGD_map hf]) _ _ hne2
    intro s' _ _; simp only [setX_map hf, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_pop (rodata : Array (BitVec 64)) (st : State α) (d : _)
    (hne : (exec rodata (.pop d) st).err = false) :
    exec rodata (.pop d) (mapState f st) = mapState f (exec rodata (.pop d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro sp _ hne2
    apply withLoad_map hf _ _ _ _ _ _ hne2
    intro ws _ _
    rw [headD_map hf, setGD_map, setX_map hf, next_map]
  · simp [exec, mapState, hh]

theorem exec_map_storeq (rodata : Array (BitVec 64)) (st : State α) (m : _) (src : _)
    (hne : (exec rodata (.storeq m src) st).err = false) :
    exec rodata (.storeq m src) (mapState f st) = mapState f (exec rodata (.storeq m src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    apply withStore_map hf _ _ _ _ (by simp [getGD_map hf]) _ _ hne2
    intro s' _ _; rfl
  · simp [exec, mapState, hh]

theorem exec_map_loadq (rodata : Array (BitVec 64)) (st : State α) (d : _) (m : _)
    (hne : (exec rodata (.loadq d m) st).err = false) :
    exec rodata (.loadq d m) (mapState f st) = mapState f (exec rodata (.loadq d m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withMem_map hf _ _ _ _ hne
    intro a _ hne2
    apply withLoad_map hf _ _ _ _ _ _ hne2
    intro ws _ _
    rw [headD_map hf, setGD_map, next_map]
  · simp [exec, mapState, hh]

set_option linter.deprecated false in
theorem repBody_map (rodata : Array (BitVec 64)) (st : State α) (n src dst : Addr)
    (hne : (repBody rodata st n src dst).err = false) :
    repBody rodata (mapState f st) n src dst = mapState f (repBody rodata st n src dst) := by
  unfold repBody at hne ⊢
  by_cases hc : n.region = 0 ∧ n.off % 8 = 0 ∧ n.off ≥ 0
  · rw [if_pos hc] at hne
    rw [if_pos hc, if_pos hc]
    exact withLoad_map hf _ _ _ _ _ _ hne fun vs _ hne5 =>
      withStore_map hf _ _ _ _ rfl _ _ hne5 fun s' _ _ => by rw [setX_map hf, setX_map hf, setX_map hf, next_map]
  · rw [if_neg hc] at hne
    rw [if_neg hc, if_neg hc]
    exact absurd hne (by simp only [fail_err]; decide)

theorem exec_map_repmovsb (rodata : Array (BitVec 64)) (st : State α)
    (hne : (exec rodata (.repmovsb) st).err = false) :
    exec rodata (.repmovsb) (mapState f st) = mapState f (exec rodata (.repmovsb) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    apply withX_map hf _ _ _ _ hne
    intro n _ hne2
    apply withX_map hf _ _ _ _ hne2
    intro src _ hne3
    apply withX_map hf _ _ _ _ hne3
    intro dst _ hne4
    exact repBody_map hf rodata st n src dst hne4
  · simp [exec, mapState, hh]

theorem exec_map_tailcall (rodata : Array (BitVec 64)) (st : State α) (name : _)
    (hne : (exec rodata (.tailcall name) st).err = false) :
    exec rodata (.tailcall name) (mapState f st) = mapState f (exec rodata (.tailcall name) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp [exec, mapState, hh]

theorem exec_map_nop (rodata : Array (BitVec 64)) (st : State α)
    (hne : (exec rodata (.nop) st).err = false) :
    exec rodata (.nop) (mapState f st) = mapState f (exec rodata (.nop) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, next_map]
  · simp [exec, mapState, hh]

theorem exec_map (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (hne : (exec rodata i st).err = false) :
    exec rodata i (mapState f st) = mapState f (exec rodata i st) := by
  cases i with
  | vmov lanes dst src mask => exact exec_map_vmov hf rodata st lanes dst src mask hne
  | vstore lanes dst src => exact exec_map_vstore hf rodata st lanes dst src hne
  | vpxor lanes d a b => exact exec_map_vpxor hf rodata st lanes d a b hne
  | vpand lanes d a b => exact exec_map_vpand hf rodata st lanes d a b hne
  | vpandn lanes d a b => exact exec_map_vpandn hf rodata st lanes d a b hne
  | vpor lanes d a b => exact exec_map_vpor hf rodata st lanes d a b hne
  | vpaddq lanes d a b => exact exec_map_vpaddq hf rodata st lanes d a b hne
  | vpsllq lanes d a imm => exact exec_map_vpsllq hf rodata st lanes d a imm hne
  | vpsrlq lanes d a imm => exact exec_map_vpsrlq hf rodata st lanes d a imm hne
  | vprolq lanes d a imm => exact exec_map_vprolq hf rodata st lanes d a imm hne
  | vpsllvq lanes d a b => exact exec_map_vpsllvq hf rodata st lanes d a b hne
  | vpsrlvq lanes d a b => exact exec_map_vpsrlvq hf rodata st lanes d a b hne
  | vpternlogq lanes d a b imm => exact exec_map_vpternlogq hf rodata st lanes d a b imm hne
  | vpshufb lanes d a ctrl => exact exec_map_vpshufb hf rodata st lanes d a ctrl hne
  | vpshufd lanes d a imm => exact exec_map_vpshufd hf rodata st lanes d a imm hne
  | vpblendd lanes d a b imm => exact exec_map_vpblendd hf rodata st lanes d a b imm hne
  | vpalignr lanes d a b imm => exact exec_map_vpalignr hf rodata st lanes d a b imm hne
  | vpunpcklqdq lanes d a b => exact exec_map_vpunpcklqdq hf rodata st lanes d a b hne
  | vpunpckhqdq lanes d a b => exact exec_map_vpunpckhqdq hf rodata st lanes d a b hne
  | vperm2i128 d a b imm => exact exec_map_vperm2i128 hf rodata st d a b imm hne
  | vinserti128 d a b imm => exact exec_map_vinserti128 hf rodata st d a b imm hne
  | vextracti128 m a imm => exact exec_map_vextracti128 hf rodata st m a imm hne
  | vshufi64x2 lanes d a b imm => exact exec_map_vshufi64x2 hf rodata st lanes d a b imm hne
  | vpermt2q lanes d idx b => exact exec_map_vpermt2q hf rodata st lanes d idx b hne
  | kmovw k m => exact exec_map_kmovw hf rodata st k m hne
  | vzeroupper => exact exec_map_vzeroupper hf rodata st hne
  | mov d src => exact exec_map_mov hf rodata st d src hne
  | xchg a b => exact exec_map_xchg hf rodata st a b hne
  | movi d imm => exact exec_map_movi hf rodata st d imm hne
  | lea d m => exact exec_map_lea hf rodata st d m hne
  | add d imm => exact exec_map_add hf rodata st d imm hne
  | sub d imm => exact exec_map_sub hf rodata st d imm hne
  | andi d imm => exact exec_map_andi hf rodata st d imm hne
  | shl d imm => exact exec_map_shl hf rodata st d imm hne
  | dec d => exact exec_map_dec hf rodata st d hne
  | xorz d => exact exec_map_xorz hf rodata st d hne
  | cmpi a imm => exact exec_map_cmpi hf rodata st a imm hne
  | cmpr a b => exact exec_map_cmpr hf rodata st a b hne
  | cmpm m b => exact exec_map_cmpm hf rodata st m b hne
  | cmprm a m => exact exec_map_cmprm hf rodata st a m hne
  | test a b => exact exec_map_test hf rodata st a b hne
  | bt a b => exact exec_map_bt hf rodata st a b hne
  | btc a imm => exact exec_map_btc hf rodata st a imm hne
  | alu op d b => exact exec_map_alu hf rodata st op d b hne
  | andn d a b => exact exec_map_andn hf rodata st d a b hne
  | rorx d b imm => exact exec_map_rorx hf rodata st d b imm hne
  | xorm m src => exact exec_map_xorm hf rodata st m src hne
  | storeqi m imm => exact exec_map_storeqi hf rodata st m imm hne
  | addm m imm => exact exec_map_addm hf rodata st m imm hne
  | decm m => exact exec_map_decm hf rodata st m hne
  | jcc c t => exact exec_map_jcc hf rodata st c t hne
  | jmp t => exact exec_map_jmp hf rodata st t hne
  | jcct c name => exact exec_map_jcct hf rodata st c name hne
  | call t => exact exec_map_call hf rodata st t hne
  | ret => exact exec_map_ret hf rodata st hne
  | push src => exact exec_map_push hf rodata st src hne
  | pop d => exact exec_map_pop hf rodata st d hne
  | storeq m src => exact exec_map_storeq hf rodata st m src hne
  | loadq d m => exact exec_map_loadq hf rodata st d m hne
  | repmovsb => exact exec_map_repmovsb hf rodata st hne
  | tailcall name => exact exec_map_tailcall hf rodata st name hne
  | nop => exact exec_map_nop hf rodata st hne

/-! Errors are sticky: an erroneous state stays erroneous (one lemma per instruction). -/
omit hf in
theorem err_exec_vmov (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (dst : _) (src : _) (mask : _) (h : st.err = true) :
    (exec rodata (.vmov lanes dst src mask) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vstore (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (dst : _) (src : _) (h : st.err = true) :
    (exec rodata (.vstore lanes dst src) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpxor (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpxor lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpand (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpand lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpandn (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpandn lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpor (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpor lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpaddq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpaddq lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpsllq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vpsllq lanes d a imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpsrlq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vpsrlq lanes d a imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vprolq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vprolq lanes d a imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpsllvq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpsllvq lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpsrlvq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpsrlvq lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpternlogq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vpternlogq lanes d a b imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpshufb (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (ctrl : _) (h : st.err = true) :
    (exec rodata (.vpshufb lanes d a ctrl) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpshufd (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vpshufd lanes d a imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpblendd (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vpblendd lanes d a b imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpalignr (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vpalignr lanes d a b imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpunpcklqdq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpunpcklqdq lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpunpckhqdq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpunpckhqdq lanes d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vperm2i128 (rodata : Array (BitVec 64)) (st : State α) (d : _) (a : _) (b : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vperm2i128 d a b imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vinserti128 (rodata : Array (BitVec 64)) (st : State α) (d : _) (a : _) (b : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vinserti128 d a b imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vextracti128 (rodata : Array (BitVec 64)) (st : State α) (m : _) (a : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vextracti128 m a imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vshufi64x2 (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _) (h : st.err = true) :
    (exec rodata (.vshufi64x2 lanes d a b imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vpermt2q (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (idx : _) (b : _) (h : st.err = true) :
    (exec rodata (.vpermt2q lanes d idx b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_kmovw (rodata : Array (BitVec 64)) (st : State α) (k : _) (m : _) (h : st.err = true) :
    (exec rodata (.kmovw k m) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_vzeroupper (rodata : Array (BitVec 64)) (st : State α) (h : st.err = true) :
    (exec rodata (.vzeroupper) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_mov (rodata : Array (BitVec 64)) (st : State α) (d : _) (src : _) (h : st.err = true) :
    (exec rodata (.mov d src) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_xchg (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.xchg a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_movi (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _) (h : st.err = true) :
    (exec rodata (.movi d imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_lea (rodata : Array (BitVec 64)) (st : State α) (d : _) (m : _) (h : st.err = true) :
    (exec rodata (.lea d m) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_add (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _) (h : st.err = true) :
    (exec rodata (.add d imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_sub (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _) (h : st.err = true) :
    (exec rodata (.sub d imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_andi (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _) (h : st.err = true) :
    (exec rodata (.andi d imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_shl (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _) (h : st.err = true) :
    (exec rodata (.shl d imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_dec (rodata : Array (BitVec 64)) (st : State α) (d : _) (h : st.err = true) :
    (exec rodata (.dec d) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_xorz (rodata : Array (BitVec 64)) (st : State α) (d : _) (h : st.err = true) :
    (exec rodata (.xorz d) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_cmpi (rodata : Array (BitVec 64)) (st : State α) (a : _) (imm : _) (h : st.err = true) :
    (exec rodata (.cmpi a imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_cmpr (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.cmpr a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_cmpm (rodata : Array (BitVec 64)) (st : State α) (m : _) (b : _) (h : st.err = true) :
    (exec rodata (.cmpm m b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_cmprm (rodata : Array (BitVec 64)) (st : State α) (a : _) (m : _) (h : st.err = true) :
    (exec rodata (.cmprm a m) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_test (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.test a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_bt (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.bt a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_btc (rodata : Array (BitVec 64)) (st : State α) (a : _) (imm : _) (h : st.err = true) :
    (exec rodata (.btc a imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_alu (rodata : Array (BitVec 64)) (st : State α) (op : _) (d : _) (b : _) (h : st.err = true) :
    (exec rodata (.alu op d b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_andn (rodata : Array (BitVec 64)) (st : State α) (d : _) (a : _) (b : _) (h : st.err = true) :
    (exec rodata (.andn d a b) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_rorx (rodata : Array (BitVec 64)) (st : State α) (d : _) (b : _) (imm : _) (h : st.err = true) :
    (exec rodata (.rorx d b imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_xorm (rodata : Array (BitVec 64)) (st : State α) (m : _) (src : _) (h : st.err = true) :
    (exec rodata (.xorm m src) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_storeqi (rodata : Array (BitVec 64)) (st : State α) (m : _) (imm : _) (h : st.err = true) :
    (exec rodata (.storeqi m imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_addm (rodata : Array (BitVec 64)) (st : State α) (m : _) (imm : _) (h : st.err = true) :
    (exec rodata (.addm m imm) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_decm (rodata : Array (BitVec 64)) (st : State α) (m : _) (h : st.err = true) :
    (exec rodata (.decm m) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_jcc (rodata : Array (BitVec 64)) (st : State α) (c : _) (t : _) (h : st.err = true) :
    (exec rodata (.jcc c t) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_jmp (rodata : Array (BitVec 64)) (st : State α) (t : _) (h : st.err = true) :
    (exec rodata (.jmp t) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_jcct (rodata : Array (BitVec 64)) (st : State α) (c : _) (name : _) (h : st.err = true) :
    (exec rodata (.jcct c name) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, condHolds, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_call (rodata : Array (BitVec 64)) (st : State α) (t : _) (h : st.err = true) :
    (exec rodata (.call t) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_ret (rodata : Array (BitVec 64)) (st : State α) (h : st.err = true) :
    (exec rodata (.ret) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_push (rodata : Array (BitVec 64)) (st : State α) (src : _) (h : st.err = true) :
    (exec rodata (.push src) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_pop (rodata : Array (BitVec 64)) (st : State α) (d : _) (h : st.err = true) :
    (exec rodata (.pop d) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_storeq (rodata : Array (BitVec 64)) (st : State α) (m : _) (src : _) (h : st.err = true) :
    (exec rodata (.storeq m src) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_loadq (rodata : Array (BitVec 64)) (st : State α) (d : _) (m : _) (h : st.err = true) :
    (exec rodata (.loadq d m) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_repmovsb (rodata : Array (BitVec 64)) (st : State α) (h : st.err = true) :
    (exec rodata (.repmovsb) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_tailcall (rodata : Array (BitVec 64)) (st : State α) (name : _) (h : st.err = true) :
    (exec rodata (.tailcall name) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec_nop (rodata : Array (BitVec 64)) (st : State α) (h : st.err = true) :
    (exec rodata (.nop) st).err = true := by
  cases hh : st.halted
  · simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withX, withMem, withSrc, withLoad, withStore,
      readG, binop, repBody, next, setX, State.setGD, State.setV, writeV, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
      (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))
  · simp [exec, hh, h]

omit hf in
theorem err_exec (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (h : st.err = true) : (exec rodata i st).err = true := by
  cases i with
  | vmov lanes dst src mask => exact err_exec_vmov rodata st lanes dst src mask h
  | vstore lanes dst src => exact err_exec_vstore rodata st lanes dst src h
  | vpxor lanes d a b => exact err_exec_vpxor rodata st lanes d a b h
  | vpand lanes d a b => exact err_exec_vpand rodata st lanes d a b h
  | vpandn lanes d a b => exact err_exec_vpandn rodata st lanes d a b h
  | vpor lanes d a b => exact err_exec_vpor rodata st lanes d a b h
  | vpaddq lanes d a b => exact err_exec_vpaddq rodata st lanes d a b h
  | vpsllq lanes d a imm => exact err_exec_vpsllq rodata st lanes d a imm h
  | vpsrlq lanes d a imm => exact err_exec_vpsrlq rodata st lanes d a imm h
  | vprolq lanes d a imm => exact err_exec_vprolq rodata st lanes d a imm h
  | vpsllvq lanes d a b => exact err_exec_vpsllvq rodata st lanes d a b h
  | vpsrlvq lanes d a b => exact err_exec_vpsrlvq rodata st lanes d a b h
  | vpternlogq lanes d a b imm => exact err_exec_vpternlogq rodata st lanes d a b imm h
  | vpshufb lanes d a ctrl => exact err_exec_vpshufb rodata st lanes d a ctrl h
  | vpshufd lanes d a imm => exact err_exec_vpshufd rodata st lanes d a imm h
  | vpblendd lanes d a b imm => exact err_exec_vpblendd rodata st lanes d a b imm h
  | vpalignr lanes d a b imm => exact err_exec_vpalignr rodata st lanes d a b imm h
  | vpunpcklqdq lanes d a b => exact err_exec_vpunpcklqdq rodata st lanes d a b h
  | vpunpckhqdq lanes d a b => exact err_exec_vpunpckhqdq rodata st lanes d a b h
  | vperm2i128 d a b imm => exact err_exec_vperm2i128 rodata st d a b imm h
  | vinserti128 d a b imm => exact err_exec_vinserti128 rodata st d a b imm h
  | vextracti128 m a imm => exact err_exec_vextracti128 rodata st m a imm h
  | vshufi64x2 lanes d a b imm => exact err_exec_vshufi64x2 rodata st lanes d a b imm h
  | vpermt2q lanes d idx b => exact err_exec_vpermt2q rodata st lanes d idx b h
  | kmovw k m => exact err_exec_kmovw rodata st k m h
  | vzeroupper => exact err_exec_vzeroupper rodata st h
  | mov d src => exact err_exec_mov rodata st d src h
  | xchg a b => exact err_exec_xchg rodata st a b h
  | movi d imm => exact err_exec_movi rodata st d imm h
  | lea d m => exact err_exec_lea rodata st d m h
  | add d imm => exact err_exec_add rodata st d imm h
  | sub d imm => exact err_exec_sub rodata st d imm h
  | andi d imm => exact err_exec_andi rodata st d imm h
  | shl d imm => exact err_exec_shl rodata st d imm h
  | dec d => exact err_exec_dec rodata st d h
  | xorz d => exact err_exec_xorz rodata st d h
  | cmpi a imm => exact err_exec_cmpi rodata st a imm h
  | cmpr a b => exact err_exec_cmpr rodata st a b h
  | cmpm m b => exact err_exec_cmpm rodata st m b h
  | cmprm a m => exact err_exec_cmprm rodata st a m h
  | test a b => exact err_exec_test rodata st a b h
  | bt a b => exact err_exec_bt rodata st a b h
  | btc a imm => exact err_exec_btc rodata st a imm h
  | alu op d b => exact err_exec_alu rodata st op d b h
  | andn d a b => exact err_exec_andn rodata st d a b h
  | rorx d b imm => exact err_exec_rorx rodata st d b imm h
  | xorm m src => exact err_exec_xorm rodata st m src h
  | storeqi m imm => exact err_exec_storeqi rodata st m imm h
  | addm m imm => exact err_exec_addm rodata st m imm h
  | decm m => exact err_exec_decm rodata st m h
  | jcc c t => exact err_exec_jcc rodata st c t h
  | jmp t => exact err_exec_jmp rodata st t h
  | jcct c name => exact err_exec_jcct rodata st c name h
  | call t => exact err_exec_call rodata st t h
  | ret => exact err_exec_ret rodata st h
  | push src => exact err_exec_push rodata st src h
  | pop d => exact err_exec_pop rodata st d h
  | storeq m src => exact err_exec_storeq rodata st m src h
  | loadq d m => exact err_exec_loadq rodata st d m h
  | repmovsb => exact err_exec_repmovsb rodata st h
  | tailcall name => exact err_exec_tailcall rodata st name h
  | nop => exact err_exec_nop rodata st h

end X86
end Keccaktree.Asm
