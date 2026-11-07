import Keccaktree.Asm.EntryCtl
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Runtime-settable words of the constant image

Two kernels read a `.data` word that the library's calibration (or a user,
through `keccaktree_avx2_small_tail` / `keccaktree_avx2_x10_mid_tail`) sets
at runtime; the model takes the `.data` words as part of the constant image
(word 112).  This file shows that the image matters only where it is read:

* `exec_rodata_eq`: two images that agree except on word `w` give the same
  step for an instruction that does not read word `w` (`noReadW`, decided on
  the addresses the instruction loads from);
* `execTrace_rodata_eq` / `pathW`: a recorded path whose symbolic run never
  reads word `w` runs the same under both images (kernel-checked on the
  symbolic cut, like `pathOk`), for every concrete state of the cut;
* `exec_cmprm_word`: the policy compare `cmp reg, [rip + 8w]` with the word
  holding the number `v`;
* the behaviour classes of the two thresholds.
-/
namespace Keccaktree.Asm.X86

variable {α : Type} [LaneOps α]

/-- The images agree except (possibly) on word `w`. -/
def AgreeExcept (r1 r2 : Array (BitVec 64)) (w : Nat) : Prop :=
  ∀ q : Nat, q ≠ w → r1.getD q 0#64 = r2.getD q 0#64

/-- `n` words at `a` do not include word `w` of the constant image. -/
def avoidsW (w : Nat) (a : Addr) (n : Nat) : Bool :=
  a.region != rRodata || decide (a.off / 8 + n ≤ (w : Int)) || decide ((w : Int) < a.off / 8)

def memW (s : State α) (w : Nat) (m : MemOp) (n : Nat) : Bool :=
  match memAddr? s m with
  | some a => avoidsW w a n
  | none => false

def srcW (s : State α) (w : Nat) (lanes : Nat) : Src → Bool
  | .reg _ => true
  | .mem m => memW s w m lanes
  | .bcst m => memW s w m 1

def gsrcW (s : State α) (w : Nat) : GSrc → Bool
  | .mem m => memW s w m 1
  | _ => true

def spW (s : State α) (w : Nat) : Bool :=
  match gx s 4 with
  | some sp => avoidsW w sp 1
  | none => false

/-- The instruction does not load word `w` of the constant image (from state `s`). -/
def noReadW (w : Nat) (i : Instr) (s : State α) : Bool :=
  match i with
  | .vmov lanes _ src _ => srcW s w lanes src
  | .vpxor lanes _ _ b | .vpand lanes _ _ b | .vpandn lanes _ _ b | .vpor lanes _ _ b
  | .vpaddq lanes _ _ b | .vpsllvq lanes _ _ b | .vpsrlvq lanes _ _ b | .vpternlogq lanes _ _ b _
  | .vpshufb lanes _ _ b | .vpblendd lanes _ _ b _ | .vpalignr lanes _ _ b _
  | .vpunpcklqdq lanes _ _ b | .vpunpckhqdq lanes _ _ b | .vshufi64x2 lanes _ _ b _
  | .vpermt2q lanes _ _ b => srcW s w lanes b
  | .vperm2i128 _ _ b _ => srcW s w 4 b
  | .vinserti128 _ _ b _ => srcW s w 2 b
  | .kmovw _ m | .xorm m _ | .addm m _ | .decm m | .cmpm m _ | .cmprm _ m | .loadq _ m => memW s w m 1
  | .alu _ _ b | .andn _ _ b | .rorx _ b _ => gsrcW s w b
  | .ret | .pop _ => spW s w
  | .repmovsb =>
    match gx s 1, gx s 6 with
    | some n, some src => n.region == 0 && avoidsW w src (n.off.toNat / 8)
    | _, _ => false
  | _ => true

section
variable {r1 r2 : Array (BitVec 64)} {w : Nat} (hr : AgreeExcept r1 r2 w)
include hr

theorem read_eqW (s : State α) (r : Region) (q : Int) (h : r ≠ rRodata ∨ q ≠ (w : Int)) :
    s.read r1 r q = s.read r2 r q := by
  simp only [State.read]
  split
  · rename_i hr4
    split
    · rename_i hq
      rcases h with h | h
      · exact absurd hr4 h
      · rw [hr q.toNat (by omega)]
    · rfl
  · rfl

theorem loadWords_eqW (s : State α) (a : Addr) (n : Nat) (h : avoidsW w a n = true) :
    s.loadWords r1 a n = s.loadWords r2 a n := by
  simp only [State.loadWords]
  split
  · congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    apply read_eqW hr
    simp only [avoidsW, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; simp only [Int.ofNat_eq_coe]; omega
    · right; simp only [Int.ofNat_eq_coe]; omega
  · rfl

theorem readSrc_eqW (s : State α) (lanes : Nat) (b : Src) (h : srcW s w lanes b = true) :
    readSrc r1 s lanes b = readSrc r2 s lanes b := by
  cases b with
  | reg n => rfl
  | mem m =>
    simp only [srcW, memW] at h
    simp only [readSrc]
    cases hm : memAddr? s m with
    | none => rfl
    | some a => simp only [hm] at h; simp only [Option.bind_some, loadWords_eqW hr s a lanes h]
  | bcst m =>
    simp only [srcW, memW] at h
    simp only [readSrc]
    cases hm : memAddr? s m with
    | none => rfl
    | some a => simp only [hm] at h; simp only [Option.bind_some, loadWords_eqW hr s a 1 h]
end

theorem avoidsW_one {w : Nat} {a : Addr} (h : avoidsW w a 1 = true) : a.region ≠ rRodata ∨ a.off / 8 ≠ (w : Int) := by
  simp only [avoidsW, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · right; omega
  · right; omega

set_option hygiene false in
macro "rod_mem" m:term : tactic => `(tactic| (
  cases hm : memAddr? s $m <;> simp only [memW, hm] at h ⊢
  try rw [loadWords_eqW hr s _ 1 h]))

theorem exec_rodata_eq {r1 r2 : Array (BitVec 64)} {w : Nat} (hr : AgreeExcept r1 r2 w) (i : Instr) (s : State α)
    (h : noReadW w i s = true) : exec r1 i s = exec r2 i s := by
  cases i <;> simp only [noReadW, srcW, gsrcW] at h <;>
    simp only [exec, withX, withMem, withSrc, withLoad, readG, binop, repBody]
  all_goals (try rw [readSrc_eqW hr _ _ _ h])
  all_goals (try rfl)
  case kmovw k m =>
    cases hm : memAddr? s m <;> simp only [memW, hm] at h ⊢
    rw [read_eqW hr s _ _ (avoidsW_one h)]
  case xorm m _ => rod_mem m
  case addm m _ => rod_mem m
  case decm m => rod_mem m
  case cmpm m _ => rod_mem m
  case cmprm _ m => rod_mem m
  case loadq _ m => rod_mem m
  case alu _ _ b => cases b <;> simp only [] at h ⊢ <;> try rfl
                    rename_i m; rod_mem m
  case andn _ _ b => cases b <;> simp only [] at h ⊢ <;> try rfl
                     rename_i m; rod_mem m
  case rorx _ b _ => cases b <;> simp only [] at h ⊢ <;> try rfl
                     rename_i m; rod_mem m
  case pop d =>
    cases hg : gx s 4 <;> simp only [spW, hg] at h ⊢
    rw [loadWords_eqW hr s _ 1 h]
  case ret =>
    split
    · rfl
    · cases hg : gx s 4 <;> simp only [spW, hg] at h ⊢
      rw [loadWords_eqW hr s _ 1 h]
  case repmovsb =>
    cases h1 : gx s 1 <;> cases h6 : gx s 6 <;> simp only [h1, h6, Bool.and_eq_true] at h ⊢
    cases h7 : gx s 7 <;> simp only []
    rw [loadWords_eqW hr s _ _ h.2]

/-! ## Paths that do not read the word -/

/-- The symbolic run of a recorded path (like `pathOk`) that never loads word `w`. -/
def pathW (rodata : Array (BitVec 64)) (prog : Array Instr) (w : Nat) : List Nat → State E → Bool
  | [], s => !s.err
  | p :: rest, s => !s.err && !s.halted && s.pc == p && noReadW w (prog.getD p .nop) s &&
      pathW rodata prog w rest (exec rodata (prog.getD p .nop) s)

theorem pathW_err (rodata : Array (BitVec 64)) (prog : Array Instr) (w : Nat) (idx : List Nat) (s : State E)
    (h : pathW rodata prog w idx s = true) : s.err = false := by
  cases idx <;> simp_all [pathW]

/-- **A path that never loads word `w` runs the same under both images**, from every concrete
state of the symbolic cut. -/
theorem pathW_run {r1 r2 : Array (BitVec 64)} {w : Nat} (hr : AgreeExcept r1 r2 w) (prog : Array Instr) :
    ∀ (idx : List Nat) (t : State E), pathW r1 prog w idx t = true → ∀ env : Nat → BitVec 64,
      X86.isa.run r2 prog idx.length (mapState (E.eval env) t) = X86.isa.run r1 prog idx.length (mapState (E.eval env) t)
  | [], t, _, env => rfl
  | p :: rest, t, h, env => by
    simp only [pathW, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨⟨⟨⟨he, hh⟩, hpc⟩, hw⟩, hrest⟩ := h
    have hne : (exec r1 (prog.getD p .nop) t).err = false := pathW_err r1 prog w rest _ hrest
    have heq : exec r1 (prog.getD p .nop) t = exec r2 (prog.getD p .nop) t := exec_rodata_eq hr _ t hw
    have hh' : (mapState (E.eval env) t).halted = false := by simpa [mapState] using hh
    have hpc' : (mapState (E.eval env) t).pc = p := by simpa [mapState] using hpc
    simp only [List.length_cons]
    rw [x86_run_succ r2 prog _ _ hh', x86_run_succ r1 prog _ _ hh', hpc']
    show X86.isa.run r2 prog rest.length (exec r2 (prog.getD p .nop) (mapState (E.eval env) t)) =
      X86.isa.run r1 prog rest.length (exec r1 (prog.getD p .nop) (mapState (E.eval env) t))
    rw [exec_map (E.eval_isHom env) r1 _ t hne, exec_map (E.eval_isHom env) r2 _ t (heq ▸ hne), ← heq]
    exact pathW_run hr prog rest _ hrest env

/-- `pathW` implies `pathOk` (the recorded path is followed). -/
theorem pathOk_of_pathW (rodata : Array (BitVec 64)) (prog : Array Instr) (w : Nat) :
    ∀ (idx : List Nat) (t : State E), pathW rodata prog w idx t = true → X86.isa.pathOk rodata prog idx t = true
  | [], t, h => by simpa [pathW, Isa.pathOk] using h
  | p :: rest, t, h => by
    simp only [pathW, Bool.and_eq_true] at h
    simp only [Isa.pathOk, Bool.and_eq_true]
    exact ⟨h.1.1, pathOk_of_pathW rodata prog w rest _ h.2⟩

/-! ## At relocated positions -/

theorem avoidsW_reloc (ρ : Reloc) (hρ : ρ.ok) (w : Nat) (a : Addr) (n : Nat) :
    avoidsW w (ρ.addr a) n = avoidsW w a n := by
  by_cases ha : a.region = rRodata
  · rw [Reloc.addr_rodata ρ hρ a ha]
  · have : (a.region != rRodata) = true := by simpa using ha
    simp only [avoidsW, Reloc.addr_region, this, Bool.true_or]

theorem memW_reloc (ρ : Reloc) (hρ : ρ.ok) (s : State E) (w : Nat) (m : MemOp) (n : Nat) (h : memW s w m n = true)
    (hok : ∀ g disp, m = .base g disp → (s.getGD g).relocOk ρ) : memW (relocState ρ s) w m n = true := by
  simp only [memW] at h ⊢
  cases hm : memAddr? s m with
  | none => simp [hm] at h
  | some a =>
    simp only [hm] at h
    rw [memAddr?_reloc ρ hρ s m a hm hok]
    simpa [avoidsW_reloc ρ hρ] using h

theorem srcW_reloc (ρ : Reloc) (hρ : ρ.ok) (s : State E) (w lanes : Nat) (b : Src) (h : srcW s w lanes b = true)
    (hok : ∀ m g disp, (b = .mem m ∨ b = .bcst m) → m = .base g disp → (s.getGD g).relocOk ρ) :
    srcW (relocState ρ s) w lanes b = true := by
  cases b with
  | reg n => rfl
  | mem m => exact memW_reloc ρ hρ s w m lanes h (fun g d hm => hok m g d (Or.inl rfl) hm)
  | bcst m => exact memW_reloc ρ hρ s w m 1 h (fun g d hm => hok m g d (Or.inr rfl) hm)

theorem spW_reloc (ρ : Reloc) (hρ : ρ.ok) (s : State E) (w : Nat) (h : spW s w = true)
    (hok : (s.getGD 4).relocOk ρ) : spW (relocState ρ s) w = true := by
  simp only [spW] at h ⊢
  cases hg : gx s 4 with
  | none => simp [hg] at h
  | some a =>
    simp only [hg] at h
    rw [gx_reloc ρ hρ s 4 a hg hok]
    simpa [avoidsW_reloc ρ hρ] using h

set_option hygiene false in
macro "rel_src" : tactic => `(tactic| (
  exact srcW_reloc ρ hρ s w _ _ h (fun m g disp hb hm => hok _ (by rcases hb with rfl | rfl <;> subst hm <;> simp [decodes]))))
set_option hygiene false in
macro "rel_mem" : tactic => `(tactic| (
  exact memW_reloc ρ hρ s w _ _ h (fun g disp hm => hok _ (by subst hm; simp [decodes]))))

theorem noReadW_reloc (ρ : Reloc) (hρ : ρ.ok) (rodata : Array (BitVec 64)) (w : Nat) (i : Instr) (s : State E)
    (h : noReadW w i s = true) (hok : ∀ e ∈ decodes rodata i s, E.relocOk ρ e) :
    noReadW w i (relocState ρ s) = true := by
  cases i <;> simp only [noReadW] at h ⊢
  case vmov => rel_src
  case vpxor => rel_src
  case vpand => rel_src
  case vpandn => rel_src
  case vpor => rel_src
  case vpaddq => rel_src
  case vpsllvq => rel_src
  case vpsrlvq => rel_src
  case vpternlogq => rel_src
  case vpshufb => rel_src
  case vpblendd => rel_src
  case vpalignr => rel_src
  case vpunpcklqdq => rel_src
  case vpunpckhqdq => rel_src
  case vshufi64x2 => rel_src
  case vpermt2q => rel_src
  case vperm2i128 => rel_src
  case vinserti128 => rel_src
  case kmovw => rel_mem
  case xorm => rel_mem
  case addm => rel_mem
  case decm => rel_mem
  case cmpm => rel_mem
  case cmprm => rel_mem
  case loadq => rel_mem
  case alu b => cases b <;> simp only [gsrcW] at h ⊢ <;> try rfl
                rel_mem
  case andn b => cases b <;> simp only [gsrcW] at h ⊢ <;> try rfl
                 rel_mem
  case rorx b _ => cases b <;> simp only [gsrcW] at h ⊢ <;> try rfl
                   rel_mem
  case ret => exact spW_reloc ρ hρ s w h (hok _ (by simp [decodes]))
  case pop => exact spW_reloc ρ hρ s w h (hok _ (by simp [decodes]))
  case repmovsb =>
    cases h1 : gx s 1 with
    | none => simp [h1] at h
    | some n =>
      cases h6 : gx s 6 with
      | none => simp [h1, h6] at h
      | some src =>
        simp only [h1, h6, Bool.and_eq_true, beq_iff_eq] at h
        rw [gx_reloc ρ hρ s 1 n h1 (hok _ (by simp [decodes])), gx_reloc ρ hρ s 6 src h6 (hok _ (by simp [decodes])),
          Reloc.addr_region0 ρ hρ n h.1]
        simp [h.1, avoidsW_reloc ρ hρ, h.2]

/-- **`pathW` at a relocated cut** (same side condition as `pathOk_reloc`). -/
theorem pathW_reloc (ρ : Reloc) (hρ : ρ.ok) (rodata : Array (BitVec 64)) (prog : Array Instr) (w : Nat) :
    ∀ (idx : List Nat) (t : State E), pathW rodata prog w idx t = true →
    (∀ e ∈ X86.isaReloc.traceDecodes rodata (idx.map (prog.getD · .nop)) t, E.relocOk ρ e) →
    pathW rodata prog w idx (relocState ρ t) = true
  | [], t, h, _ => by simpa [pathW, relocState] using h
  | p :: rest, t, h, hok => by
    simp only [pathW, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h ⊢
    obtain ⟨⟨⟨⟨he, hh⟩, hpc⟩, hw⟩, hrest⟩ := h
    simp only [List.map_cons, Isa.Relocatable.traceDecodes, List.mem_append] at hok
    have hne : (exec rodata (prog.getD p .nop) t).err = false := pathW_err rodata prog w rest _ hrest
    refine ⟨⟨⟨⟨by simpa [relocState] using he, by simpa [relocState] using hh⟩, by simpa [relocState] using hpc⟩,
      noReadW_reloc ρ hρ rodata w _ t hw (fun e he' => hok e (Or.inl he'))⟩, ?_⟩
    rw [exec_reloc ρ hρ rodata _ t hne (fun e he' => hok e (Or.inl he'))]
    exact pathW_reloc ρ hρ rodata prog w rest _ hrest (fun e he' => hok e (Or.inr he'))

/-! ## The policy compare and the behaviour classes -/

/-- `cmp reg, qword ptr [rip + 8w]` with word `w` holding any 64-bit number `v` (and `reg` the
number `x`): an unsigned comparison. -/
theorem exec_cmprm_word (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (a : Gpr) (w : Nat) (x : Nat) (v : Nat)
    (hh : S.halted = false) (hx : S.getGD a = gprWord ⟨0, x⟩) (hxwf : (⟨0, (x : Int)⟩ : Addr).wf)
    (hv : rodata.getD w 0#64 = BitVec.ofNat 64 v) (hv64 : v < 2 ^ 64) :
    exec rodata (.cmprm a (.rip (8 * w))) S =
      next { S with zf := decide ((x : Int) = v), cf := decide ((x : Int) < v) } := by
  have hg := gx_of_word S a ⟨0, x⟩ hx hxwf
  have hx64 : x < 2 ^ 64 := by have := hxwf.2; simp only at this; omega
  have hw8 : ((8 * w : Nat) : Int) / 8 = (w : Int) := by omega
  have hm8 : ((8 * w : Nat) : Int) % 8 = 0 := by omega
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, withMem, memAddr?, withLoad, State.loadWords, hm8,
    State.read, rRodata, List.range_one, List.map_cons, List.map_nil, hw8, List.headD_cons, withX, hg]
  have hz : (w : Int) + Int.ofNat 0 = w := by show (w : Int) + 0 = w; omega
  have hc : (LaneOps.asConst (LaneOps.const (BitVec.ofNat 64 v) : BitVec 64) : Option (BitVec 64)) =
      some (BitVec.ofNat 64 v) := rfl
  simp only [hz, ge_iff_le, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, hv, hc, setFlagsNum]
  have e0 : BitVec.ofInt 64 (x : Int) = BitVec.ofNat 64 x := BitVec.ofInt_natCast 64 x
  have e1 : (BitVec.ofNat 64 x = BitVec.ofNat 64 v) ↔ ((x : Int) = v) := by
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hv64] at this; omega
    · intro h; have : x = v := by omega
      rw [this]
  have e2 : (BitVec.ofNat 64 x).toNat < (BitVec.ofNat 64 v).toNat ↔ ((x : Int) < v) := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hv64]; omega
  rw [e0]
  simp only [decide_eq_decide.mpr e1, decide_eq_decide.mpr e2, hh]

/-- The class representative of a threshold `v` for a compare whose register lies in `[lo, hi]`:
`x > v ↔ x > classRep lo hi v` for every such `x` (`ja` after `cmp x, v`). -/
def classRep (lo hi v : Nat) : Nat := max (lo - 1) (min v hi)

theorem classRep_gt (lo hi v x : Nat) (hlo : 1 ≤ lo) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    (x > v ↔ x > classRep lo hi v) := by
  simp only [classRep]; omega

/-- avx2_x4 `.Lsmall_tail_max` (word 112): compared with the remaining count `2..3`; classes
`{≤ 1}, {2}, {≥ 3}`.  avx2_x10 `.Lmid_tail_max` (word 112): compared with `5..9`; classes
`{≤ 4}, {5}, {6}, {7}, {8}, {≥ 9}`. -/
theorem classes_small_tail (v : Nat) : classRep 2 3 v ∈ [1, 2, 3] := by
  simp only [classRep, List.mem_cons, List.mem_nil_iff, or_false]; omega
theorem classes_mid_tail (v : Nat) : classRep 5 9 v ∈ [4, 5, 6, 7, 8, 9] := by
  simp only [classRep, List.mem_cons, List.mem_nil_iff, or_false]; omega

/-- The image with word `w` set to the number `v`. -/
def setWord (rodata : Array (BitVec 64)) (w v : Nat) : Array (BitVec 64) := rodata.set! w (BitVec.ofNat 64 v)

theorem setWord_agree (rodata : Array (BitVec 64)) (w v v' : Nat) : AgreeExcept (setWord rodata w v) (setWord rodata w v') w := by
  intro q hq
  simp only [setWord, Array.set!]
  by_cases hs : q < rodata.size
  · simp [Array.getD, hs, Array.getElem_setIfInBounds, Ne.symm hq]
  · simp [Array.getD, hs]

theorem setWord_getD (rodata : Array (BitVec 64)) (w v : Nat) (hw : w < rodata.size) :
    (setWord rodata w v).getD w 0#64 = BitVec.ofNat 64 v := by
  simp [setWord, Array.set!, Array.getD, hw]

/-- **The policy compare in a class.** `cmp reg, [rip + 8w]; ja t` with the register holding
`x ∈ [lo, hi]` takes the same branch for every threshold `v` of a class; the two runs differ only
in ZF/CF afterwards (dirty flags, to be written before their next read: `run_ovr_path`). -/
theorem policy_ja_class (rodata : Array (BitVec 64)) (prog : Array Instr) (S : State (BitVec 64)) (a : Gpr) (w : Nat)
    (t : Nat) (x : Nat) (lo hi v : Nat) (hw : w < rodata.size) (hlo : 1 ≤ lo) (hx1 : lo ≤ x) (hx2 : x ≤ hi)
    (hhi : hi < 2 ^ 64) (hv64 : v < 2 ^ 64)
    (hi1 : prog.getD S.pc .nop = .cmprm a (.rip (8 * w))) (hi2 : prog.getD (S.pc + 1) .nop = .jcc .a t)
    (hh : S.halted = false) (hx : S.getGD a = gprWord ⟨0, x⟩) (hxwf : (⟨0, (x : Int)⟩ : Addr).wf) :
    X86.isa.run (setWord rodata w v) prog 2 S =
      ovr { zf := true, cf := true } { ctl0 with zf := decide ((x : Int) = v), cf := decide ((x : Int) < v) }
        (X86.isa.run (setWord rodata w (classRep lo hi v)) prog 2 S) := by
  have hrep : classRep lo hi v < 2 ^ 64 := by simp only [classRep]; omega
  have hgt := classRep_gt lo hi v x hlo hx1 hx2
  rw [x86_run_succ _ _ _ _ hh, x86_run_succ _ _ _ _ hh, hi1,
    exec_cmprm_word _ S a w x v hh hx hxwf (setWord_getD rodata w v hw) hv64,
    exec_cmprm_word _ S a w x _ hh hx hxwf (setWord_getD rodata w _ hw) hrep]
  simp only [next]
  rw [x86_run_succ _ _ _ _ (by simpa using hh), x86_run_succ _ _ _ _ (by simpa using hh)]
  simp only [hi2]
  show exec _ (.jcc .a t) _ = ovr _ _ (exec _ (.jcc .a t) _)
  have hgtb : ∀ y z : Int, (!decide (y < z) && !decide (y = z)) = decide (y > z) := by
    intro y z
    by_cases h1 : y < z <;> by_cases h2 : y = z <;> simp [h1, h2] <;> omega
  have hdec : (!decide ((x : Int) < v) && !decide ((x : Int) = v)) =
      (!decide ((x : Int) < (classRep lo hi v : Nat)) && !decide ((x : Int) = (classRep lo hi v : Nat))) := by
    rw [hgtb, hgtb]
    apply decide_eq_decide.mpr
    have := hgt; constructor <;> intro h <;> omega
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, condHolds, ovr, hdec, Bool.cond_true, Bool.cond_false,
    List.contains_nil]
  congr 1
  apply Vector.ext; intro i hi; simp

end Keccaktree.Asm.X86
