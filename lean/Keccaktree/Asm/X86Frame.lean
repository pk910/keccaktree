import Keccaktree.Asm.KernelGlue
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Count steps of an x86 kernel frame, for every count

The frame of a kernel tests its node count (and small codes derived from it) with
`cmp`/`test`/`bt`/`jcc`, decrements it by the batch size, and dispatches tail calls.
These instructions only touch general registers holding numbers, the flags and `pc`;
they run on concrete states whose count is any value (a Lean variable), between the
generated segments (which treat the count as data).

`Fr rodata prog S m pc zf cf vals R`: after `m` steps from `S` the state is `S` except
for the general registers `R`, the flags (now `zf`, `cf`) and `pc`; it has not failed or
halted; each `(n, v) ∈ vals` says register `n` holds the word `BitVec.ofInt 64 v`.
One lemma per instruction form advances it by one step; `Fr.cut` hands the state over
to the next generated segment (`cut_transfer` with the count registers as fixed words).
-/
namespace Keccaktree.Asm.X86
open Keccaktree.Asm

/-- `T` agrees with `S` except on the general registers `R`, the flags and `pc`. -/
def Near (R : List Nat) (S T : State (BitVec 64)) : Prop :=
  T.v = S.v ∧ (∀ n, n ∉ R → T.getGD n = S.getGD n) ∧ T.k = S.k ∧ T.nf = S.nf ∧ T.vf = S.vf ∧
  T.vl = S.vl ∧ T.mem = S.mem ∧ T.depth = S.depth

/-- `m` count steps from `S`. -/
structure Fr (rodata : Array (BitVec 64)) (prog : Array Instr) (S : State (BitVec 64)) (m : Nat)
    (pc : Nat) (zf cf : Bool) (vals : List (Nat × Int)) (R : List Nat) : Prop where
  near : Near R S (X86.isa.run rodata prog m S)
  g : (X86.isa.run rodata prog m S).g = Vector.replicate 32 ⟨0, 0⟩
  pc : (X86.isa.run rodata prog m S).pc = pc
  zf : (X86.isa.run rodata prog m S).zf = zf
  cf : (X86.isa.run rodata prog m S).cf = cf
  vals : ∀ p ∈ vals, (X86.isa.run rodata prog m S).getGD p.1 = BitVec.ofInt 64 p.2
  err : (X86.isa.run rodata prog m S).err = false
  halted : (X86.isa.run rodata prog m S).halted = false
  tail : (X86.isa.run rodata prog m S).tail = none

/-- The words of `vals` with register `n` replaced. -/
def setVal (vals : List (Nat × Int)) (n : Nat) (v : Int) : List (Nat × Int) :=
  (n, v) :: vals.filter (fun p => p.1 != n)

theorem replicate_setIfInBounds (n : Nat) :
    (Vector.replicate 32 (⟨0, 0⟩ : Addr)).setIfInBounds n ⟨0, 0⟩ = Vector.replicate 32 ⟨0, 0⟩ := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_setIfInBounds, Vector.getElem_replicate]
  split <;> rfl

theorem getGD_setGD (S : State (BitVec 64)) (n n' : Nat) (x : BitVec 64) (hn : n < 32) :
    (S.setGD n x).getGD n' = if n' = n then x else S.getGD n' := by
  simp only [State.getGD, State.setGD, Vector.getD]
  by_cases h : n' = n
  · subst h; simp [hn]
  · simp only [h, ↓reduceIte]
    simp only [Vector.toArray_setIfInBounds]
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm h)]

theorem run_succ (rodata : Array (BitVec 64)) (prog : Array Instr) (S : State (BitVec 64)) (m : Nat)
    (hh : (X86.isa.run rodata prog m S).halted = false) :
    X86.isa.run rodata prog (m + 1) S = exec rodata (prog.getD (X86.isa.run rodata prog m S).pc .nop) (X86.isa.run rodata prog m S) := by
  rw [Isa.run_add, X86.run_one rodata prog _ hh]

variable {rodata : Array (BitVec 64)} {prog : Array Instr} {S : State (BitVec 64)} {m pc : Nat} {zf cf : Bool}
  {vals : List (Nat × Int)} {R : List Nat}

/-- No step yet. -/
theorem Fr.start (S : State (BitVec 64)) (vals : List (Nat × Int)) (hg : S.g = Vector.replicate 32 ⟨0, 0⟩)
    (hv : ∀ p ∈ vals, S.getGD p.1 = BitVec.ofInt 64 p.2) (he : S.err = false) (hh : S.halted = false)
    (ht : S.tail = none) : Fr rodata prog S 0 S.pc S.zf S.cf vals [] :=
  ⟨⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hg, rfl, rfl, rfl, hv, he, hh, ht⟩

theorem Fr.val (h : Fr rodata prog S m pc zf cf vals R) (n : Nat) (v : Int) (hp : (n, v) ∈ vals) :
    (X86.isa.run rodata prog m S).getGD n = BitVec.ofInt 64 v := h.vals _ hp

theorem gx_num (T : State (BitVec 64)) (n : Nat) (v : Int) (h : T.getGD n = BitVec.ofInt 64 v)
    (h0 : 0 ≤ v) (h1 : v < 2 ^ 55) : gx T n = some ⟨0, v⟩ := by
  apply gx_of_word T n ⟨0, v⟩ _ ⟨h0, h1⟩
  rw [h]; rfl

/-- The facts a step lemma may use about the state it runs on. -/
def At (pc : Nat) (zf cf : Bool) (vals : List (Nat × Int)) (T : State (BitVec 64)) : Prop :=
  T.halted = false ∧ T.pc = pc ∧ T.zf = zf ∧ T.cf = cf ∧ ∀ p ∈ vals, T.getGD p.1 = BitVec.ofInt 64 p.2

theorem Fr.at (h : Fr rodata prog S m pc zf cf vals R) : At pc zf cf vals (X86.isa.run rodata prog m S) :=
  ⟨h.halted, h.pc, h.zf, h.cf, h.vals⟩

/-- A step that only changes flags and `pc`. -/
theorem Fr.flags (h : Fr rodata prog S m pc zf cf vals R) (pc' : Nat) (zf' cf' : Bool)
    (hU' : ∀ T, At pc zf cf vals T → exec rodata (prog.getD pc .nop) T = { T with zf := zf', cf := cf', pc := pc' }) :
    Fr rodata prog S (m + 1) pc' zf' cf' vals R := by
  have hr := run_succ rodata prog S m h.halted
  rw [h.pc, hU' _ h.at] at hr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := h.near
  exact { near := by rw [hr]; exact ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩
          g := by rw [hr]; exact h.g
          pc := by rw [hr]
          zf := by rw [hr]
          cf := by rw [hr]
          vals := by rw [hr]; exact h.vals
          err := by rw [hr]; exact h.err
          halted := by rw [hr]; exact h.halted
          tail := by rw [hr]; exact h.tail }

/-- A step that writes general register `n` with the word of `v` and may set the flags. -/
theorem Fr.write (h : Fr rodata prog S m pc zf cf vals R) (n : Nat) (hn : n < 32) (v : Int) (zf' cf' : Bool)
    (hU' : ∀ T, At pc zf cf vals T →
      exec rodata (prog.getD pc .nop) T = { T.setGD n (BitVec.ofInt 64 v) with zf := zf', cf := cf', pc := pc + 1 }) :
    Fr rodata prog S (m + 1) (pc + 1) zf' cf' (setVal vals n v) (n :: R) := by
  have hr := run_succ rodata prog S m h.halted
  rw [h.pc, hU' _ h.at] at hr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := h.near
  exact { near := by
            rw [hr]
            refine ⟨n1, fun n' hn' => ?_, n3, n4, n5, n6, n7, n8⟩
            show ((X86.isa.run rodata prog m S).setGD n (BitVec.ofInt 64 v)).getGD n' = _
            rw [getGD_setGD _ _ _ _ hn, if_neg (fun e : n' = n => hn' (by rw [e]; exact List.mem_cons_self))]
            exact n2 n' (fun hm => hn' (List.mem_cons_of_mem _ hm))
          g := by
            rw [hr]
            show (X86.isa.run rodata prog m S).g.setIfInBounds n ⟨0, 0⟩ = _
            rw [h.g, replicate_setIfInBounds]
          pc := by rw [hr]
          zf := by rw [hr]
          cf := by rw [hr]
          vals := by
            rw [hr]
            intro p hp
            show ((X86.isa.run rodata prog m S).setGD n (BitVec.ofInt 64 v)).getGD p.1 = _
            rw [getGD_setGD _ _ _ _ hn]
            simp only [setVal, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hp
            rcases hp with rfl | ⟨hp, hne⟩
            · simp
            · rw [if_neg hne]; exact h.vals p hp
          err := by rw [hr]; exact h.err
          halted := by rw [hr]; exact h.halted
          tail := by rw [hr]; exact h.tail }

theorem Fr.pc_congr (h : Fr rodata prog S m pc zf cf vals R) {pc' : Nat} (e : pc = pc') :
    Fr rodata prog S m pc' zf cf vals R := e ▸ h

/-! ## The instruction forms -/

theorem Fr.cmpi (h : Fr rodata prog S m pc zf cf vals R) (n : Nat) (imm v : Int)
    (hi : prog.getD pc .nop = .cmpi n imm) (hv : (n, v) ∈ vals) (h0 : 0 ≤ v) (h1 : v < 2 ^ 55) :
    Fr rodata prog S (m + 1) (pc + 1) (decide (v = imm)) (decide (v < imm)) vals R := by
  apply h.flags
  rintro T ⟨hh, hp, -, -, hvs⟩
  have hg := gx_num T n v (hvs _ hv) h0 h1
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg, setFlagsSub, Addr.num, next, hp]
  all_goals rfl

theorem Fr.test (h : Fr rodata prog S m pc zf cf vals R) (n : Nat) (v : Int)
    (hi : prog.getD pc .nop = .test n n) (hv : (n, v) ∈ vals) (h0 : 0 ≤ v) (h1 : v < 2 ^ 55) :
    Fr rodata prog S (m + 1) (pc + 1) (decide (v = 0)) false vals R := by
  apply h.flags
  rintro T ⟨hh, hp, -, -, hvs⟩
  have hg := gx_num T n v (hvs _ hv) h0 h1
  have := ofInt_eq_zero_iff v h0 h1
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg, and_self, BitVec.and_self, this, next, hp]
  all_goals rfl

/-- The outcome of a condition on the flags. -/
def condF (zf cf : Bool) : Cond → Bool
  | .e => zf | .ne => !zf | .b => cf | .a => !cf && !zf | .ae => !cf | .be => cf || zf

theorem condHolds_eq (T : State (BitVec 64)) (c : Cond) : condHolds T c = condF T.zf T.cf c := by
  cases c <;> rfl

theorem Fr.jcc (h : Fr rodata prog S m pc zf cf vals R) (c : Cond) (t : Nat)
    (hi : prog.getD pc .nop = .jcc c t) :
    Fr rodata prog S (m + 1) (if condF zf cf c then t else pc + 1) zf cf vals R := by
  apply h.flags
  rintro T ⟨hh, hp, hz, hc, -⟩
  rw [hi, exec_jcc_eq rodata _ c t hh, condHolds_eq, hz, hc, hp]
  all_goals (cases T; simp only at *; subst_vars; rfl)

theorem Fr.jmp (h : Fr rodata prog S m pc zf cf vals R) (t : Nat) (hi : prog.getD pc .nop = .jmp t) :
    Fr rodata prog S (m + 1) t zf cf vals R := by
  apply h.flags
  rintro T ⟨hh, hp, hz, hc, -⟩
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte]
  all_goals (cases T; simp only at *; subst_vars; rfl)

theorem Fr.jcct_not (h : Fr rodata prog S m pc zf cf vals R) (c : Cond) (name : String)
    (hi : prog.getD pc .nop = .jcct c name) (hc : condF zf cf c = false) :
    Fr rodata prog S (m + 1) (pc + 1) zf cf vals R := by
  apply h.flags
  rintro T ⟨hh, hp, hz, hc', -⟩
  have h2 : condHolds T c = false := by rw [condHolds_eq, hz, hc']; exact hc
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, h2, next, hp]
  all_goals (cases T; simp only at *; subst_vars; rfl)

theorem Fr.nop (h : Fr rodata prog S m pc zf cf vals R) (hi : prog.getD pc .nop = .nop ∨ prog.getD pc .nop = .vzeroupper) :
    Fr rodata prog S (m + 1) (pc + 1) zf cf vals R := by
  apply h.flags
  rintro T ⟨hh, hp, hz, hc, -⟩
  rcases hi with hi | hi <;> simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, next, hp] <;>
    (cases T; simp only at *; subst_vars; rfl)

theorem Fr.movi (h : Fr rodata prog S m pc zf cf vals R) (n : Nat) (hn : n < 32) (imm : Int)
    (hi : prog.getD pc .nop = .movi n imm) :
    Fr rodata prog S (m + 1) (pc + 1) zf cf (setVal vals n imm) (n :: R) := by
  apply h.write n hn imm
  rintro T ⟨hh, hp, hz, hc, -⟩
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, next, hp]
  all_goals (cases T; simp only at *; subst_vars; rfl)

theorem Fr.mov (h : Fr rodata prog S m pc zf cf vals R) (d s : Nat) (hd : d < 32) (v : Int)
    (hi : prog.getD pc .nop = .mov d s) (hv : (s, v) ∈ vals) :
    Fr rodata prog S (m + 1) (pc + 1) zf cf (setVal vals d v) (d :: R) := by
  apply h.write d hd v
  rintro T ⟨hh, hp, hz, hc, hvs⟩
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, next, hp, hvs _ hv]
  all_goals (cases T; simp only at *; subst_vars; rfl)

theorem Fr.xorz (h : Fr rodata prog S m pc zf cf vals R) (d : Nat) (hd : d < 32)
    (hi : prog.getD pc .nop = .xorz d) :
    Fr rodata prog S (m + 1) (pc + 1) true false (setVal vals d 0) (d :: R) := by
  apply h.write d hd 0
  rintro T ⟨hh, hp, -, -, -⟩
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, next, hp]
  all_goals (cases T; simp only at *; subst_vars; rfl)

theorem Fr.sub (h : Fr rodata prog S m pc zf cf vals R) (n : Nat) (hn : n < 32) (imm v : Int)
    (hi : prog.getD pc .nop = .sub n imm) (hv : (n, v) ∈ vals) (h0 : 0 ≤ v) (h1 : v < 2 ^ 55) :
    Fr rodata prog S (m + 1) (pc + 1) (decide (v = imm)) (decide (v < imm)) (setVal vals n (v - imm)) (n :: R) := by
  apply h.write n hn (v - imm)
  rintro T ⟨hh, hp, -, -, hvs⟩
  have hg := gx_num T n v (hvs _ hv) h0 h1
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg, setFlagsSub, Addr.num, next, hp, setX]
  all_goals (cases T; simp only at *; subst_vars; rfl)

/-- `bt a, b`: the carry is bit `b` (a number) of the constant word in `a`. -/
theorem Fr.bt (h : Fr rodata prog S m pc zf cf vals R) (a b : Nat) (w v : Int)
    (hi : prog.getD pc .nop = .bt a b) (hw : (a, w) ∈ vals) (hv : (b, v) ∈ vals) (h0 : 0 ≤ v) (h1 : v < 2 ^ 55) :
    Fr rodata prog S (m + 1) (pc + 1) zf ((BitVec.ofInt 64 w).getLsbD (v.toNat % 64)) vals R := by
  apply h.flags
  rintro T ⟨hh, hp, hz, -, hvs⟩
  have hg := gx_num T b v (hvs _ hv) h0 h1
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, withX, hg, hvs _ hw, h0, and_self, next, hp]
  all_goals (cases T; simp only at *; subst_vars; rfl)

/-- `cmp a, qword [rip + off]` against a constant word (a runtime threshold): an unsigned compare. -/
theorem Fr.cmprm (h : Fr rodata prog S m pc zf cf vals R) (a off : Nat) (v : Int)
    (hi : prog.getD pc .nop = .cmprm a (.rip off)) (hal : (off : Int) % 8 = 0) (hpos : 0 ≤ (off : Int) / 8)
    (hv : (a, v) ∈ vals) (h0 : 0 ≤ v) (h1 : v < 2 ^ 55) :
    Fr rodata prog S (m + 1) (pc + 1) (decide (BitVec.ofInt 64 v = rodata.getD ((off : Int) / 8).toNat 0))
      (decide ((BitVec.ofInt 64 v).toNat < (rodata.getD ((off : Int) / 8).toNat 0).toNat)) vals R := by
  apply h.flags
  rintro T ⟨hh, hp, -, -, hvs⟩
  have hg := gx_num T a v (hvs _ hv) h0 h1
  simp only [hi, exec, hh, Bool.false_eq_true, ↓reduceIte, withMem, memAddr?, withLoad, State.loadWords, hal,
    List.range_one, List.map_cons, List.map_nil, State.read, rRodata, Int.ofNat_eq_coe, Int.cast_ofNat_Int, Int.add_zero,
    List.headD_cons, ge_iff_le, hpos]
  simp only [withX, hg, setFlagsNum, next, hp, ↓reduceIte, hh]
  rfl

/-! ## Handing a count-step state over to the next segment -/

theorem envOf_near (R : List Nat) (S T : State (BitVec 64)) (h : Near R S T) (i : Nat)
    (hi : ∀ n ∈ R, i ≠ 256 + n) : envOf T i = envOf S i := by
  obtain ⟨h1, h2, -, -, -, -, h7, -⟩ := h
  unfold envOf
  split
  · simp only [State.getV, h1]
  · split
    · have := h2 (i - 256) (fun hm => hi (i - 256) hm (by omega))
      exact this
    · rw [h7]

/-- What a state at the end of a segment (or at the entry) offers the next segment: its control
words are the closed ones relocated by `ρ`, and its control part is the closed one. -/
def PreCut (ρ : Reloc) (L : List Nat) (sc S : State (BitVec 64)) : Prop :=
  (∀ i ∈ L, i < 288 ∨ memVarRegion i = rStack → cutVar L S i = E.reloc ρ (cutVar L sc i)) ∧
  S.k = sc.k ∧ S.nf = sc.nf ∧ S.vf = sc.vf ∧ S.vl = sc.vl ∧ S.depth = sc.depth

theorem PreCut.of_cut (ρ : Reloc) (hρ : ρ.ok) (L : List Nat) (sc S : State (BitVec 64))
    (h : relocState ρ (cutOf L sc) = cutOf L S) : PreCut ρ L sc S := by
  have f := cut_fields ρ L sc S h
  exact ⟨fun i _ hc => cut_word ρ hρ L sc S h i hc, f.2.1, f.2.2.2.2.1, f.2.2.2.2.2.1, f.2.2.2.2.2.2.1,
    f.2.2.2.2.2.2.2.2⟩

/-- **Hand-over from count steps to a segment.**  The next segment's control words are control words
of the previous cut not written by the count steps (`σ` moves them, e.g. one batch further), or
count registers whose value the count steps know. -/
theorem Fr.cut {ρ σ : Reloc} (hρ : ρ.ok) (hσ : σ.ok) (L L' : List Nat) (sc sc' : State (BitVec 64))
    (hA : PreCut ρ L sc S) (h : Fr rodata prog S m pc zf cf vals R)
    (fixed : List (Nat × Int)) (hfix : ∀ p ∈ fixed, p ∈ vals)
    (hchk : (L'.all fun i => (decide (i < 288) || memVarRegion i == rStack) &&
       ((L.contains i && R.all (fun n => i != 256 + n) && (cutVar L sc i == E.reloc σ (cutVar L' sc' i))) ||
        fixed.any (fun p => i == 256 + p.1 && decide (p.1 < 32) && (cutVar L' sc' i == .const (BitVec.ofInt 64 p.2)) &&
          ((wordGpr (BitVec.ofInt 64 p.2)).region == 0)))) = true)
    (hctl : sc'.g = Vector.replicate 32 ⟨0, 0⟩ ∧ sc.k = sc'.k ∧ sc.nf = sc'.nf ∧ sc.vf = sc'.vf ∧
      sc.vl = sc'.vl ∧ sc.depth = sc'.depth)
    (hz : zf = sc'.zf) (hc : cf = sc'.cf) (hpc : pc = sc'.pc) :
    relocState (ρ.add σ) (cutOf L' sc') = cutOf L' (X86.isa.run rodata prog m S) := by
  obtain ⟨hw, hk, hnf, hvf, hvl, hd⟩ := hA
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := h.near
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hctl
  apply relocState_cutOf (ρ.add σ) L' sc' (X86.isa.run rodata prog m S)
  · intro i hi
    have hci := List.all_eq_true.mp hchk i hi
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem,
      List.all_eq_true, List.any_eq_true, bne_iff_ne, ne_eq] at hci
    obtain ⟨hcell, ⟨⟨hin, hR⟩, hv⟩ | ⟨p, hp, ⟨⟨⟨hip, hp32⟩, hcv⟩, hreg⟩⟩⟩ := hci
    · have henv : envOf (X86.isa.run rodata prog m S) i = envOf S i :=
        envOf_near R S _ h.near i (fun n hn => hR n hn)
      rw [cutVar_eq_of_env L L' S _ i hi hin henv, hw i hin hcell, hv, E.reloc_add ρ σ hρ hσ]
    · have hval := h.vals p (hfix p hp)
      subst hip
      have he : envOf (X86.isa.run rodata prog m S) (256 + p.1) = BitVec.ofInt 64 p.2 := by
        rw [envOf_gdVar _ _ hp32]; exact hval
      rw [hcv]
      simp only [cutVar, List.contains_iff_mem.mpr hi, ↓reduceIte, he, hreg, ne_eq, not_true_eq_false, false_and]
      rfl
  · intro i hi hge
    have hci := (List.all_eq_true.mp hchk i hi)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hci
    have hr : memVarRegion i = rStack := by
      rcases hci.1 with h' | h'
      · omega
      · exact h'
    rw [hr, Reloc.add_wshift ρ σ hρ hσ, SliceCert.stack_wshift ρ hρ, SliceCert.stack_wshift σ hσ]
    rfl
  · exact ⟨h.g.trans c1.symm, n3.trans (hk.trans c2), h.zf.trans hz, h.cf.trans hc, n4.trans (hnf.trans c3),
      n5.trans (hvf.trans c4), n6.trans (hvl.trans c5), h.pc.trans hpc, n8.trans (hd.trans c6)⟩

/-- A taken conditional tail call: the run halts with the tail call. -/
theorem Fr.jcct_taken (h : Fr rodata prog S m pc zf cf vals R) (c : Cond) (name : String)
    (hi : prog.getD pc .nop = .jcct c name) (hc : condF zf cf c = true) :
    X86.isa.run rodata prog (m + 1) S =
      { X86.isa.run rodata prog m S with halted := true, tail := some name } := by
  rw [run_succ rodata prog S m h.halted, h.pc, hi]
  have h2 : condHolds (X86.isa.run rodata prog m S) c = true := by rw [condHolds_eq, h.zf, h.cf]; exact hc
  simp only [exec, h.halted, Bool.false_eq_true, ↓reduceIte, h2]

end Keccaktree.Asm.X86
