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
variable {α β : Type} [LaneOps α] [LaneOps β] {f : α → β} (hf : IsHom f)
include hf

theorem getV_map (s : State α) (n : Nat) : (mapState f s).getV n = (s.getV n).map f := by
  simp only [State.getV, mapState, Vector.getD]
  rcases h : s.v[n]? with _ | v <;> simp [h, hf.const, Vector.toList_map]

omit hf in
@[simp] theorem getG_map (s : State α) (n : Nat) : (mapState f s).getG n = s.getG n := rfl
omit hf in
@[simp] theorem memAddr_map (s : State α) (m : MemOp) : memAddr (mapState f s) m = memAddr s m := rfl
@[simp] theorem setG_map (s : State α) (n : Nat) (a : Addr) : (mapState f s).setG n a = mapState f (s.setG n a) := by
  simp [State.setG, mapState, Vector.map_setIfInBounds, hf.const]
omit hf in
@[simp] theorem fail_map (s : State α) : (mapState f s).fail = mapState f s.fail := rfl

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

theorem readSrc_map (rodata : Array (BitVec 64)) (s : State α) (lanes : Nat) (src : Src) :
    readSrc rodata (mapState f s) lanes src = (readSrc rodata s lanes src).map (List.map f) := by
  cases src with
  | reg n => simp [readSrc, getV_map hf, List.map_take]
  | mem m => simp [readSrc, loadWords_map hf, memAddr_map]
  | bcst m =>
    simp only [readSrc, loadWords_map hf, memAddr_map]
    rcases h : s.loadWords rodata (memAddr s m) 1 with _ | l
    · rfl
    · cases l <;> simp [hf.const, List.map_replicate]

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
theorem foldl_hom {γ δ ι : Type} (g : γ → δ) (step : γ → ι → γ) (step' : δ → ι → δ)
    (h : ∀ acc i, g (step acc i) = step' (g acc) i) (l : List ι) (init : γ) :
    g (l.foldl step init) = l.foldl step' (g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ih, h]

theorem ternlog_map (imm : Nat) (a b c : α) :
    LaneOps.ternlog imm (f a) (f b) (f c) = f (LaneOps.ternlog imm a b c) := (hf.ternlog imm a b c).symm

theorem lane128_map (xs : List α) (j : Nat) :
    lane128 (xs.map f) j = (lane128 xs j).map f := by
  simp [lane128, List.getD_eq_getElem?_getD]
  constructor <;> (rcases xs[2 * j]? with _ | x <;> rcases xs[2 * j + 1]? with _ | y <;> simp [hf.const])

theorem binop_map (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) (g : α → α → α) (g' : β → β → β)
    (hg : ∀ x y, f (g x y) = g' (f x) (f y)) :
    binop (rodata) (mapState f s) lanes d a b g' = mapState f (binop rodata s lanes d a b g) := by
  simp only [binop, readSrc_map hf]
  rcases readSrc rodata s lanes b with _ | bs
  · rfl
  · simp only [Option.map_some, getV_map hf, List.map_take]
    rw [← writeV_map hf]
    congr 1
    rw [List.map_zipWith, ← List.map_take, List.zipWith_map]
    congr 1
    funext x y
    exact (hg x y).symm

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
@[simp] theorem g_map (s : State α) : (mapState f s).g = s.g := rfl
omit hf in
@[simp] theorem zf_map (s : State α) : (mapState f s).zf = s.zf := rfl
omit hf in
@[simp] theorem cf_map (s : State α) : (mapState f s).cf = s.cf := rfl
omit hf in
@[simp] theorem tail_map (s : State α) : (mapState f s).tail = s.tail := rfl
omit hf in
@[simp] theorem gd_map (s : State α) : (mapState f s).gd = s.gd.map f := rfl
omit hf in
@[simp] theorem nf_map (s : State α) : (mapState f s).nf = s.nf := rfl
omit hf in
@[simp] theorem vf_map (s : State α) : (mapState f s).vf = s.vf := rfl
omit hf in
@[simp] theorem vl_map (s : State α) : (mapState f s).vl = s.vl := rfl
omit hf in
@[simp] theorem map_upd_pc (s : State α) (p : Nat) : mapState f { s with pc := p } = { mapState f s with pc := p } := rfl
omit hf in
@[simp] theorem map_upd_pc_depth (s : State α) (p d : Nat) :
    mapState f { s with pc := p, depth := d } = { mapState f s with pc := p, depth := d } := rfl
omit hf in
@[simp] theorem map_upd_flags (s : State α) (z c : Bool) (p : Nat) :
    mapState f { s with zf := z, cf := c, pc := p } = { mapState f s with zf := z, cf := c, pc := p } := rfl
omit hf in
@[simp] theorem map_upd_zf (s : State α) (z : Bool) (p : Nat) :
    mapState f { s with zf := z, pc := p } = { mapState f s with zf := z, pc := p } := rfl
omit hf in
@[simp] theorem map_upd_halted (s : State α) : mapState f { s with halted := true } = { mapState f s with halted := true } := rfl
omit hf in
@[simp] theorem map_upd_tail (s : State α) (n : String) :
    mapState f { s with halted := true, tail := some n } = { mapState f s with halted := true, tail := some n } := rfl
omit hf in
@[simp] theorem map_upd_k (s : State α) (k : Vector Nat 8) (p : Nat) :
    mapState f { s with k := k, pc := p } = { mapState f s with k := k, pc := p } := rfl
omit hf in
@[simp] theorem setFlagsSub_map (s : State α) (a b : Addr) :
    setFlagsSub (mapState f s) a b = mapState f (setFlagsSub s a b) := by
  simp only [setFlagsSub]; split <;> rfl

theorem getD_map (l : List α) (i : Nat) : (l.map f).getD i (LaneOps.const 0) = f (l.getD i (LaneOps.const 0)) := by
  simp [List.getD_eq_getElem?_getD]
  rcases l[i]? with _ | x <;> simp [hf.const]

theorem binop_xor_map (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) :
    binop (rodata) (mapState f s) lanes d a b LaneOps.xor = mapState f (binop rodata s lanes d a b LaneOps.xor) :=
  binop_map hf rodata s lanes d a b _ _ hf.xor
theorem binop_and_map (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) :
    binop (rodata) (mapState f s) lanes d a b LaneOps.and = mapState f (binop rodata s lanes d a b LaneOps.and) :=
  binop_map hf rodata s lanes d a b _ _ hf.and
theorem binop_or_map (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) :
    binop (rodata) (mapState f s) lanes d a b LaneOps.or = mapState f (binop rodata s lanes d a b LaneOps.or) :=
  binop_map hf rodata s lanes d a b _ _ hf.or
theorem binop_add_map (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) :
    binop (rodata) (mapState f s) lanes d a b LaneOps.add = mapState f (binop rodata s lanes d a b LaneOps.add) :=
  binop_map hf rodata s lanes d a b _ _ hf.add
theorem binop_andn_map (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) :
    binop (rodata) (mapState f s) lanes d a b (fun x y => LaneOps.and (LaneOps.not x) y) =
      mapState f (binop rodata s lanes d a b (fun x y => LaneOps.and (LaneOps.not x) y)) :=
  binop_map hf rodata s lanes d a b _ _ (fun x y => by simp [hf.and, hf.not])

theorem map_shl (l : List α) (imm : Nat) :
    (l.map f).map (fun x => if imm < 64 then LaneOps.shl x imm else LaneOps.const 0) =
      (l.map (fun x => if imm < 64 then LaneOps.shl x imm else LaneOps.const 0)).map f := by
  simp only [List.map_map]; congr 1; funext x; simp only [Function.comp]; split <;> simp [hf.shl, hf.const]
theorem map_shr (l : List α) (imm : Nat) :
    (l.map f).map (fun x => if imm < 64 then LaneOps.shr x imm else LaneOps.const 0) =
      (l.map (fun x => if imm < 64 then LaneOps.shr x imm else LaneOps.const 0)).map f := by
  simp only [List.map_map]; congr 1; funext x; simp only [Function.comp]; split <;> simp [hf.shr, hf.const]
theorem map_rol (l : List α) (imm : Nat) :
    (l.map f).map (fun x => LaneOps.rol x (imm % 64)) = (l.map (fun x => LaneOps.rol x (imm % 64))).map f := by
  simp only [List.map_map]; congr 1; funext x; simp [Function.comp, hf.rol]

omit hf in
@[simp] theorem map_fail (s : State α) : mapState f s.fail = (mapState f s).fail := rfl
omit hf in
@[simp] theorem fail_err (s : State α) : s.fail.err = true := rfl
omit hf in
@[simp] theorem v_map (s : State α) : (mapState f s).v = s.v.map (·.map f) := rfl
omit hf in
@[simp] theorem mem_map (s : State α) : (mapState f s).mem = fun r q => f (s.mem r q) := rfl

theorem optGetD_map (o : Option α) : (o.map f).getD (LaneOps.const 0) = f (o.getD (LaneOps.const 0)) := by
  rcases o with _ | x <;> simp [hf.const]

theorem getElem?_map_getD (l : List α) (i : Nat) :
    (l.map f)[i]?.getD (LaneOps.const 0) = f (l[i]?.getD (LaneOps.const 0)) := by
  rw [List.getElem?_map]; exact optGetD_map hf _

omit hf in
theorem ite_map_list (c : Prop) [Decidable c] (l1 l2 : List α) :
    (if c then l1.map f else l2.map f) = (if c then l1 else l2).map f := by
  split <;> rfl

/-- `writeV_map` with the lanes given pointwise. -/
theorem writeV_map' (s : State α) (n lanes : Nat) {ι : Type} (g : ι → α) (r : List ι) :
    writeV (mapState f s) n lanes (r.map fun i => f (g i)) = mapState f (writeV s n lanes (r.map g)) := by
  rw [← writeV_map hf, List.map_map]; rfl

omit hf in
theorem foldr_cons2_map {ι : Type} (x y : ι → α) (r : List ι) :
    List.foldr (fun j acc => f (x j) :: f (y j) :: acc) [] r = (List.foldr (fun j acc => x j :: y j :: acc) [] r).map f := by
  induction r with
  | nil => rfl
  | cons j r ih => simp [List.foldr_cons, ih]

theorem writeV_foldr2_map (s : State α) (n lanes : Nat) {ι : Type} (x y : ι → α) (r : List ι) :
    writeV (mapState f s) n lanes (List.foldr (fun j acc => f (x j) :: f (y j) :: acc) [] r) =
      mapState f (writeV s n lanes (List.foldr (fun j acc => x j :: y j :: acc) [] r)) := by
  rw [foldr_cons2_map, writeV_map hf]

theorem storeWords_const_map (s : State α) (a : Addr) (w : BitVec 64) :
    (mapState f s).storeWords a [LaneOps.const w] = (s.storeWords a [LaneOps.const w]).map (mapState f) := by
  have := storeWords_map hf s a [LaneOps.const w]
  simpa [hf.const] using this


omit hf in
theorem ite_map (c : Prop) [Decidable c] (x y : α) : (if c then f x else f y) = f (if c then x else y) := by
  split <;> rfl

omit hf in
theorem foldr_append_map {ι : Type} (g : ι → List α) (r : List ι) :
    List.foldr (fun j acc => (g j).map f ++ acc) [] r = (List.foldr (fun j acc => g j ++ acc) [] r).map f := by
  induction r with
  | nil => rfl
  | cons j r ih => simp [List.foldr_cons, ih]

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

theorem byteOf_map (w : α) (j : Nat) :
    LaneOps.and (LaneOps.shr (f w) (8 * j)) (LaneOps.const 0xff#64) = f (LaneOps.and (LaneOps.shr w (8 * j)) (LaneOps.const 0xff#64)) := by
  simp [hf.and, hf.shr, hf.const]

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

/-- `exec` commutes with a lane homomorphism, as long as the (symbolic) run
does not fail; one lemma per instruction. -/
theorem exec_map_vmov (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (dst : _) (src : _) (mask : _)
    (hne : (exec rodata (.vmov lanes dst src mask) st).err = false) :
    exec (rodata) (.vmov lanes dst src mask) (mapState f st) = mapState f (exec rodata (.vmov lanes dst src mask) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf, k_map, pc_map] at hne ⊢
    rcases h1 : readSrc rodata st lanes src with _ | vs
    · rfl
    · simp only [Option.map_some]
      cases mask with
      | none => rw [writeV_map hf]; rfl
      | some k =>
        simp only [getElem?_map_getD hf, List.getD_eq_getElem?_getD, ite_map, writeV_map' hf]
        rfl
  · simp [exec, mapState, hh]

theorem exec_map_vstore (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (dst : _) (src : _)
    (hne : (exec rodata (.vstore lanes dst src) st).err = false) :
    exec (rodata) (.vstore lanes dst src) (mapState f st) = mapState f (exec rodata (.vstore lanes dst src) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vpxor (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpxor lanes d a b) st).err = false) :
    exec (rodata) (.vpxor lanes d a b) (mapState f st) = mapState f (exec rodata (.vpxor lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vpand (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpand lanes d a b) st).err = false) :
    exec (rodata) (.vpand lanes d a b) (mapState f st) = mapState f (exec rodata (.vpand lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vpandn (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpandn lanes d a b) st).err = false) :
    exec (rodata) (.vpandn lanes d a b) (mapState f st) = mapState f (exec rodata (.vpandn lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vpor (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpor lanes d a b) st).err = false) :
    exec (rodata) (.vpor lanes d a b) (mapState f st) = mapState f (exec rodata (.vpor lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vpaddq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpaddq lanes d a b) st).err = false) :
    exec (rodata) (.vpaddq lanes d a b) (mapState f st) = mapState f (exec rodata (.vpaddq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vpsllq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vpsllq lanes d a imm) st).err = false) :
    exec (rodata) (.vpsllq lanes d a imm) (mapState f st) = mapState f (exec rodata (.vpsllq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vpsrlq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vpsrlq lanes d a imm) st).err = false) :
    exec (rodata) (.vpsrlq lanes d a imm) (mapState f st) = mapState f (exec rodata (.vpsrlq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vprolq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (imm : _)
    (hne : (exec rodata (.vprolq lanes d a imm) st).err = false) :
    exec (rodata) (.vprolq lanes d a imm) (mapState f st) = mapState f (exec rodata (.vprolq lanes d a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vpternlogq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vpternlogq lanes d a b imm) st).err = false) :
    exec (rodata) (.vpternlogq lanes d a b imm) (mapState f st) = mapState f (exec rodata (.vpternlogq lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf, k_map, pc_map] at hne ⊢
    rcases h1 : readSrc rodata st lanes b with _ | bs
    · rfl
    · simp only [Option.map_some, ← List.map_take, List.getD_eq_getElem?_getD, getElem?_map_getD hf, ternlog_map hf,
        writeV_map' hf]
      rfl
  · simp [exec, mapState, hh]

theorem exec_map_vpshufb (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (ctrl : _)
    (hne : (exec rodata (.vpshufb lanes d a ctrl) st).err = false) :
    exec (rodata) (.vpshufb lanes d a ctrl) (mapState f st) = mapState f (exec rodata (.vpshufb lanes d a ctrl) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf, k_map, pc_map] at hne ⊢
    rcases h1 : readSrc rodata st lanes ctrl with _ | cs
    · rfl
    · simp only [Option.map_some, ← List.map_take, h1] at hne ⊢
      rcases hall : (List.map LaneOps.asConst cs).all Option.isSome with _ | _
      · simp only [hall] at hne; exact absurd hne (by simp [State.fail])
      · simp only [asConst_map_all hf _ hall, hall, ↓reduceIte, List.getD_eq_getElem?_getD, getElem?_map_getD hf,
          shufb128_map' hf, writeV_foldr2_map hf]
        rfl
  · simp [exec, mapState, hh]

theorem exec_map_vpunpcklqdq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpunpcklqdq lanes d a b) st).err = false) :
    exec (rodata) (.vpunpcklqdq lanes d a b) (mapState f st) = mapState f (exec rodata (.vpunpcklqdq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf, k_map, pc_map] at hne ⊢
    rcases h1 : readSrc rodata st lanes b with _ | bs
    · rfl
    · simp only [Option.map_some, ← List.map_take, List.getD_eq_getElem?_getD, getElem?_map_getD hf, writeV_foldr2_map hf]
      rfl
  · simp [exec, mapState, hh]

theorem exec_map_vpunpckhqdq (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _)
    (hne : (exec rodata (.vpunpckhqdq lanes d a b) st).err = false) :
    exec (rodata) (.vpunpckhqdq lanes d a b) (mapState f st) = mapState f (exec rodata (.vpunpckhqdq lanes d a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf, k_map, pc_map] at hne ⊢
    rcases h1 : readSrc rodata st lanes b with _ | bs
    · rfl
    · simp only [Option.map_some, ← List.map_take, List.getD_eq_getElem?_getD, getElem?_map_getD hf, writeV_foldr2_map hf]
      rfl
  · simp [exec, mapState, hh]

theorem exec_map_vperm2i128 (rodata : Array (BitVec 64)) (st : State α) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vperm2i128 d a b imm) st).err = false) :
    exec (rodata) (.vperm2i128 d a b imm) (mapState f st) = mapState f (exec rodata (.vperm2i128 d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf, k_map, pc_map] at hne ⊢
    rcases h1 : readSrc rodata st 4 b with _ | bs
    · rfl
    · simp only [Option.map_some, ← List.map_take, lane128_map hf]
      have hz : ([LaneOps.const 0, LaneOps.const 0] : List β) = [LaneOps.const 0, LaneOps.const 0].map f := by simp [hf.const]
      simp only [hz]
      split <;> split <;> (try split) <;> (try split) <;> simp only [← List.map_append, writeV_map hf] <;> rfl
  · simp [exec, mapState, hh]

theorem exec_map_vshufi64x2 (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (a : _) (b : _) (imm : _)
    (hne : (exec rodata (.vshufi64x2 lanes d a b imm) st).err = false) :
    exec (rodata) (.vshufi64x2 lanes d a b imm) (mapState f st) = mapState f (exec rodata (.vshufi64x2 lanes d a b imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf, k_map, pc_map] at hne ⊢
    rcases h1 : readSrc rodata st lanes b with _ | bs
    · rfl
    · simp only [Option.map_some, ← List.map_take, ite_map_list, lane128_map hf, foldr_append_map, writeV_map hf]
      rfl
  · simp [exec, mapState, hh]

theorem exec_map_vpermt2q (rodata : Array (BitVec 64)) (st : State α) (lanes : _) (d : _) (idx : _) (b : _)
    (hne : (exec rodata (.vpermt2q lanes d idx b) st).err = false) :
    exec (rodata) (.vpermt2q lanes d idx b) (mapState f st) = mapState f (exec rodata (.vpermt2q lanes d idx b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf, k_map, pc_map] at hne ⊢
    rcases h1 : readSrc rodata st lanes b with _ | bs
    · rfl
    · simp only [Option.map_some, ← List.map_take, h1] at hne ⊢
      rcases hall : (List.map LaneOps.asConst (List.take lanes (st.getV idx))).all Option.isSome with _ | _
      · simp only [hall] at hne; exact absurd hne (by simp [State.fail])
      · simp only [asConst_map_all hf _ hall, hall, ↓reduceIte, List.getD_eq_getElem?_getD, getElem?_map_getD hf, ite_map,
          writeV_map' hf]
        rfl
  · simp [exec, mapState, hh]

theorem exec_map_kmovw (rodata : Array (BitVec 64)) (st : State α) (k : _) (m : _)
    (hne : (exec rodata (.kmovw k m) st).err = false) :
    exec (rodata) (.kmovw k m) (mapState f st) = mapState f (exec rodata (.kmovw k m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_vzeroupper (rodata : Array (BitVec 64)) (st : State α) 
    (hne : (exec rodata (.vzeroupper ) st).err = false) :
    exec (rodata) (.vzeroupper ) (mapState f st) = mapState f (exec rodata (.vzeroupper ) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_mov (rodata : Array (BitVec 64)) (st : State α) (d : _) (s : _)
    (hne : (exec rodata (.mov d s) st).err = false) :
    exec (rodata) (.mov d s) (mapState f st) = mapState f (exec rodata (.mov d s) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_movi (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.movi d imm) st).err = false) :
    exec (rodata) (.movi d imm) (mapState f st) = mapState f (exec rodata (.movi d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_lea (rodata : Array (BitVec 64)) (st : State α) (d : _) (m : _)
    (hne : (exec rodata (.lea d m) st).err = false) :
    exec (rodata) (.lea d m) (mapState f st) = mapState f (exec rodata (.lea d m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_add (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.add d imm) st).err = false) :
    exec (rodata) (.add d imm) (mapState f st) = mapState f (exec rodata (.add d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_sub (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.sub d imm) st).err = false) :
    exec (rodata) (.sub d imm) (mapState f st) = mapState f (exec rodata (.sub d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_andi (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.andi d imm) st).err = false) :
    exec (rodata) (.andi d imm) (mapState f st) = mapState f (exec rodata (.andi d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_shl (rodata : Array (BitVec 64)) (st : State α) (d : _) (imm : _)
    (hne : (exec rodata (.shl d imm) st).err = false) :
    exec (rodata) (.shl d imm) (mapState f st) = mapState f (exec rodata (.shl d imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_dec (rodata : Array (BitVec 64)) (st : State α) (d : _)
    (hne : (exec rodata (.dec d) st).err = false) :
    exec (rodata) (.dec d) (mapState f st) = mapState f (exec rodata (.dec d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_xorz (rodata : Array (BitVec 64)) (st : State α) (d : _)
    (hne : (exec rodata (.xorz d) st).err = false) :
    exec (rodata) (.xorz d) (mapState f st) = mapState f (exec rodata (.xorz d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_cmpi (rodata : Array (BitVec 64)) (st : State α) (a : _) (imm : _)
    (hne : (exec rodata (.cmpi a imm) st).err = false) :
    exec (rodata) (.cmpi a imm) (mapState f st) = mapState f (exec rodata (.cmpi a imm) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_cmpr (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _)
    (hne : (exec rodata (.cmpr a b) st).err = false) :
    exec (rodata) (.cmpr a b) (mapState f st) = mapState f (exec rodata (.cmpr a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_test (rodata : Array (BitVec 64)) (st : State α) (a : _) (b : _)
    (hne : (exec rodata (.test a b) st).err = false) :
    exec (rodata) (.test a b) (mapState f st) = mapState f (exec rodata (.test a b) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_jcc (rodata : Array (BitVec 64)) (st : State α) (c : _) (t : _)
    (hne : (exec rodata (.jcc c t) st).err = false) :
    exec (rodata) (.jcc c t) (mapState f st) = mapState f (exec rodata (.jcc c t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_jmp (rodata : Array (BitVec 64)) (st : State α) (t : _)
    (hne : (exec rodata (.jmp t) st).err = false) :
    exec (rodata) (.jmp t) (mapState f st) = mapState f (exec rodata (.jmp t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_call (rodata : Array (BitVec 64)) (st : State α) (t : _)
    (hne : (exec rodata (.call t) st).err = false) :
    exec (rodata) (.call t) (mapState f st) = mapState f (exec rodata (.call t) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_ret (rodata : Array (BitVec 64)) (st : State α) 
    (hne : (exec rodata (.ret ) st).err = false) :
    exec (rodata) (.ret ) (mapState f st) = mapState f (exec rodata (.ret ) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, loadWords_map hf, memAddr_map, getG_map,
      readSrc_map hf, getV_map hf, storeWords_const_map hf, k_map, pc_map, depth_map] at hne ⊢
    by_cases hd : st.depth = 0
    · simp only [hd, ↓reduceIte]; rfl
    · simp only [hd, ↓reduceIte] at hne ⊢
      rcases h1 : st.loadWords rodata (st.getG 4) 1 with _ | l
      · rfl
      · rcases l with _ | ⟨r, l⟩
        · rfl
        · rcases l with _ | ⟨r2, l⟩
          · simp only [Option.map_some, List.map_cons, List.map_nil]
            rcases h2 : LaneOps.asConst r with _ | w
            · simp only [h1, h2] at hne; exact absurd hne (by simp [State.fail])
            · rw [hf.asConst r w h2]; simp only [h2]; simp only [setG_map hf, map_upd_pc, map_upd_pc_depth]
          · rfl
  · simp [exec, mapState, hh]

theorem exec_map_push (rodata : Array (BitVec 64)) (st : State α) (s : _)
    (hne : (exec rodata (.push s) st).err = false) :
    exec (rodata) (.push s) (mapState f st) = mapState f (exec rodata (.push s) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_pop (rodata : Array (BitVec 64)) (st : State α) (d : _)
    (hne : (exec rodata (.pop d) st).err = false) :
    exec (rodata) (.pop d) (mapState f st) = mapState f (exec rodata (.pop d) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, loadWords_map hf, memAddr_map, getG_map,
      readSrc_map hf, getV_map hf, storeWords_const_map hf, k_map, pc_map, depth_map] at hne ⊢
    rcases h1 : st.loadWords rodata (st.getG 4) 1 with _ | l
    · rfl
    · rcases l with _ | ⟨r, l⟩
      · rfl
      · rcases l with _ | ⟨r2, l⟩
        · simp only [Option.map_some, List.map_cons, List.map_nil]
          rcases h2 : LaneOps.asConst r with _ | w
          · simp only [h1, h2] at hne; exact absurd hne (by simp [State.fail])
          · rw [hf.asConst r w h2]; simp only [h2]; split <;> simp_all only [setG_map hf, ↓reduceIte] <;> simp only [mapState, hne]
        · rfl
  · simp [exec, mapState, hh]

theorem exec_map_storeq (rodata : Array (BitVec 64)) (st : State α) (m : _) (s : _)
    (hne : (exec rodata (.storeq m s) st).err = false) :
    exec (rodata) (.storeq m s) (mapState f st) = mapState f (exec rodata (.storeq m s) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_loadq (rodata : Array (BitVec 64)) (st : State α) (d : _) (m : _)
    (hne : (exec rodata (.loadq d m) st).err = false) :
    exec (rodata) (.loadq d m) (mapState f st) = mapState f (exec rodata (.loadq d m) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, loadWords_map hf, memAddr_map, getG_map,
      readSrc_map hf, getV_map hf, storeWords_const_map hf, k_map, pc_map, depth_map] at hne ⊢
    rcases h1 : st.loadWords rodata (memAddr st m) 1 with _ | l
    · rfl
    · rcases l with _ | ⟨r, l⟩
      · rfl
      · rcases l with _ | ⟨r2, l⟩
        · simp only [Option.map_some, List.map_cons, List.map_nil]
          rcases h2 : LaneOps.asConst r with _ | w
          · simp only [h1, h2] at hne; exact absurd hne (by simp [State.fail])
          · rw [hf.asConst r w h2]; simp only [h2]; split <;> simp_all only [setG_map hf, ↓reduceIte] <;> simp only [mapState, hne]
        · rfl
  · simp [exec, mapState, hh]

theorem exec_map_repmovsb (rodata : Array (BitVec 64)) (st : State α) 
    (hne : (exec rodata (.repmovsb ) st).err = false) :
    exec (rodata) (.repmovsb ) (mapState f st) = mapState f (exec rodata (.repmovsb ) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_tailcall (rodata : Array (BitVec 64)) (st : State α) (name : _)
    (hne : (exec rodata (.tailcall name) st).err = false) :
    exec (rodata) (.tailcall name) (mapState f st) = mapState f (exec rodata (.tailcall name) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

theorem exec_map_nop (rodata : Array (BitVec 64)) (st : State α) 
    (hne : (exec rodata (.nop ) st).err = false) :
    exec (rodata) (.nop ) (mapState f st) = mapState f (exec rodata (.nop ) st) := by
  cases hh : st.halted
  · simp only [exec, hh, halted_map, Bool.false_eq_true, ↓reduceIte, readSrc_map hf, getV_map hf,
      binop_xor_map hf, binop_and_map hf, binop_or_map hf, binop_add_map hf, binop_andn_map hf,
      ← List.map_take, map_shl hf, map_shr hf, map_rol hf, writeV_map hf, storeWords_map hf, loadWords_map hf,
      read_map hf, getG_map, setG_map hf, memAddr_map, k_map, pc_map, depth_map, zf_map, cf_map,
      map_upd_pc, map_upd_pc_depth, map_upd_flags, map_upd_zf, map_upd_halted, map_upd_tail, map_upd_k,
      setFlagsSub_map, fail_map, Option.map_some, Option.map_none, storeWords_const_map hf] at hne ⊢
    all_goals (first | rfl | skip)
    all_goals (try (symm; (repeat' split) <;> (try subst_vars) <;> (try simp_all only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, map_upd_pc, pc_map, writeV_map hf, fail_map, fail_err,
      hf.asConst, Bool.true_eq_false, map_upd_pc_depth, setG_map hf, getG_map, k_map, depth_map])))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all only [writeV_map hf, storeWords_map hf, Option.map_some, Option.some.injEq]))
    all_goals (first | rfl | skip)
    all_goals (try (subst_vars; simp_all [mapState, writeV_map hf, State.setG, hf.const]))
    all_goals (try (rename_i hex; obtain ⟨a, ha, rfl⟩ := hex; rename_i heq; cases Option.some.inj (ha.symm.trans heq); simp_all [State.setG, hf.const]))
    all_goals (try (rename_i h1 h2; cases h1.symm.trans h2))
    all_goals (try (rename_i h1 h2; cases h2.symm.trans h1))
  · simp [exec, mapState, hh]

/-- `exec` commutes with a lane homomorphism whenever the (symbolic) run does not fail. -/
theorem exec_map (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (hne : (exec rodata i st).err = false) :
    exec (rodata) i (mapState f st) = mapState f (exec rodata i st) := by
  cases i with
  | vmov x0 x1 x2 x3 => exact exec_map_vmov hf rodata st x0 x1 x2 x3 hne
  | vstore x0 x1 x2 => exact exec_map_vstore hf rodata st x0 x1 x2 hne
  | vpxor x0 x1 x2 x3 => exact exec_map_vpxor hf rodata st x0 x1 x2 x3 hne
  | vpand x0 x1 x2 x3 => exact exec_map_vpand hf rodata st x0 x1 x2 x3 hne
  | vpandn x0 x1 x2 x3 => exact exec_map_vpandn hf rodata st x0 x1 x2 x3 hne
  | vpor x0 x1 x2 x3 => exact exec_map_vpor hf rodata st x0 x1 x2 x3 hne
  | vpaddq x0 x1 x2 x3 => exact exec_map_vpaddq hf rodata st x0 x1 x2 x3 hne
  | vpsllq x0 x1 x2 x3 => exact exec_map_vpsllq hf rodata st x0 x1 x2 x3 hne
  | vpsrlq x0 x1 x2 x3 => exact exec_map_vpsrlq hf rodata st x0 x1 x2 x3 hne
  | vprolq x0 x1 x2 x3 => exact exec_map_vprolq hf rodata st x0 x1 x2 x3 hne
  | vpternlogq x0 x1 x2 x3 x4 => exact exec_map_vpternlogq hf rodata st x0 x1 x2 x3 x4 hne
  | vpshufb x0 x1 x2 x3 => exact exec_map_vpshufb hf rodata st x0 x1 x2 x3 hne
  | vpunpcklqdq x0 x1 x2 x3 => exact exec_map_vpunpcklqdq hf rodata st x0 x1 x2 x3 hne
  | vpunpckhqdq x0 x1 x2 x3 => exact exec_map_vpunpckhqdq hf rodata st x0 x1 x2 x3 hne
  | vperm2i128 x0 x1 x2 x3 => exact exec_map_vperm2i128 hf rodata st x0 x1 x2 x3 hne
  | vshufi64x2 x0 x1 x2 x3 x4 => exact exec_map_vshufi64x2 hf rodata st x0 x1 x2 x3 x4 hne
  | vpermt2q x0 x1 x2 x3 => exact exec_map_vpermt2q hf rodata st x0 x1 x2 x3 hne
  | kmovw x0 x1 => exact exec_map_kmovw hf rodata st x0 x1 hne
  | vzeroupper => exact exec_map_vzeroupper hf rodata st  hne
  | mov x0 x1 => exact exec_map_mov hf rodata st x0 x1 hne
  | movi x0 x1 => exact exec_map_movi hf rodata st x0 x1 hne
  | lea x0 x1 => exact exec_map_lea hf rodata st x0 x1 hne
  | add x0 x1 => exact exec_map_add hf rodata st x0 x1 hne
  | sub x0 x1 => exact exec_map_sub hf rodata st x0 x1 hne
  | andi x0 x1 => exact exec_map_andi hf rodata st x0 x1 hne
  | shl x0 x1 => exact exec_map_shl hf rodata st x0 x1 hne
  | dec x0 => exact exec_map_dec hf rodata st x0 hne
  | xorz x0 => exact exec_map_xorz hf rodata st x0 hne
  | cmpi x0 x1 => exact exec_map_cmpi hf rodata st x0 x1 hne
  | cmpr x0 x1 => exact exec_map_cmpr hf rodata st x0 x1 hne
  | test x0 x1 => exact exec_map_test hf rodata st x0 x1 hne
  | jcc x0 x1 => exact exec_map_jcc hf rodata st x0 x1 hne
  | jmp x0 => exact exec_map_jmp hf rodata st x0 hne
  | call x0 => exact exec_map_call hf rodata st x0 hne
  | ret => exact exec_map_ret hf rodata st  hne
  | push x0 => exact exec_map_push hf rodata st x0 hne
  | pop x0 => exact exec_map_pop hf rodata st x0 hne
  | storeq x0 x1 => exact exec_map_storeq hf rodata st x0 x1 hne
  | loadq x0 x1 => exact exec_map_loadq hf rodata st x0 x1 hne
  | repmovsb => exact exec_map_repmovsb hf rodata st  hne
  | tailcall x0 => exact exec_map_tailcall hf rodata st x0 hne
  | nop => exact exec_map_nop hf rodata st  hne

omit hf in
theorem storeWords_err (st s' : State α) (a : Addr) (vs : List α) (h : st.storeWords a vs = some s') : s'.err = st.err := by
  simp only [State.storeWords] at h
  split at h
  · cases h; rfl
  · cases h

omit hf in
/-- Errors are sticky: an erroneous state stays erroneous. -/
theorem err_exec (rodata : Array (BitVec 64)) (i : Instr) (st : State α) (h : st.err = true) : (exec rodata i st).err = true := by
  cases i <;> simp only [exec, binop, writeV, State.setV, State.setG, setFlagsSub, State.fail, h] <;>
    (repeat' split) <;> (try simp_all) <;>
    (try (rw [storeWords_err _ _ _ _ ‹State.storeWords _ _ _ = some _›]; exact h))

omit hf in
theorem err_execTrace (rodata : Array (BitVec 64)) (l : List Instr) (st : State α) (h : st.err = true) :
    (execTrace rodata l st).err = true := by
  induction l generalizing st with
  | nil => exact h
  | cons i l ih => simp only [execTrace, List.foldl_cons]; exact ih _ (err_exec rodata i st h)

theorem execTrace_map (rodata : Array (BitVec 64)) (l : List Instr) (st : State α)
    (hne : (execTrace rodata l st).err = false) :
    execTrace (rodata) l (mapState f st) = mapState f (execTrace rodata l st) := by
  induction l generalizing st with
  | nil => rfl
  | cons i l ih =>
    simp only [execTrace, List.foldl_cons] at hne ⊢
    have h1 : (exec rodata i st).err = false := by
      cases hc : (exec rodata i st).err
      · rfl
      · have := err_execTrace rodata l (exec rodata i st) hc
        simp_all [execTrace]
    rw [exec_map hf rodata i st h1]
    exact ih _ hne

end X86
end Keccaktree.Asm
