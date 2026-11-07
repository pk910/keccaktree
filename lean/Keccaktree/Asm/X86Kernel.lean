import Keccaktree.Asm.X86Frame
import Keccaktree.Asm.Final
import Keccaktree.Asm.Node
import Keccaktree.Asm.LibX86
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The x86 kernels on any number of nodes: shared definitions

* `rho m`: relocation by `m` nodes (64 input bytes, 32 output bytes per node);
* the calling convention `LibX86.Entry` (a fresh call's control state; `LibX86.mkKernel` lifts a
  theorem from it to any flags/masks left by a tail call) and `LibX86.Digest`;
* `entrySc`, `PreCut.entry`: the entry state as the "end" of a pseudo-segment, so that the frame's
  count steps (`Fr`) and `Fr.cut` apply from the entry on.
-/
namespace Keccaktree.Asm.X86K
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Asm.LibX86

/-! ## Relocation by whole nodes -/

/-- `m` nodes further: 64 input bytes and 32 output bytes per node. -/
def rho (m : Nat) : Reloc :=
  ⟨fun r => if r = rInput then 64 * (m : Int) else if r = rOutput then 32 * (m : Int) else 0⟩

theorem rho_δ (m : Nat) (r : Region) :
    (rho m).δ r = if r = rInput then 64 * (m : Int) else if r = rOutput then 32 * (m : Int) else 0 := rfl

theorem rho_ok (m : Nat) : (rho m).ok := by
  refine ⟨rfl, rfl, rfl, fun r => ?_⟩
  rw [rho_δ]
  by_cases h1 : r = rInput
  · subst h1; simp only [↓reduceIte]; exact ⟨by omega, 8 * (m : Int), by omega⟩
  · by_cases h2 : r = rOutput
    · subst h2; simp only [show rOutput ≠ rInput by decide, ↓reduceIte]; exact ⟨by omega, 4 * (m : Int), by omega⟩
    · simp only [h1, h2, ↓reduceIte]; exact ⟨by omega, 0, by omega⟩

theorem rho_within (m : Nat) (h : 64 * m ≤ 2 ^ 54) : (rho m).within (2 ^ 54) := by
  intro r
  have h' : 64 * (m : Int) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  rw [rho_δ, show (2 : Int) ^ 54 = 18014398509481984 from rfl, show (2 : Int) ^ 55 = 36028797018963968 from rfl]
  by_cases h1 : r = rInput
  · subst h1; simp only [↓reduceIte]; omega
  · by_cases h2 : r = rOutput
    · subst h2; simp only [show rOutput ≠ rInput by decide, ↓reduceIte]; omega
    · simp only [h1, h2, ↓reduceIte]; omega

theorem rho_wshift_in (m : Nat) : (rho m).wshift rInput = 8 * (m : Int) := by
  simp only [Reloc.wshift, rho_δ, ↓reduceIte]; omega

theorem rho_wshift_out (m : Nat) : (rho m).wshift rOutput = 4 * (m : Int) := by
  simp only [Reloc.wshift, rho_δ, show rOutput ≠ rInput by decide, ↓reduceIte]; omega

theorem rho_wshift_stack (m : Nat) : (rho m).wshift rStack = 0 := SliceCert.stack_wshift _ (rho_ok m)

theorem rho_add (a b : Nat) : (rho a).add (rho b) = rho (a + b) := by
  show Reloc.mk _ = Reloc.mk _
  congr 1; funext r
  show (rho a).δ r + (rho b).δ r = (rho (a + b)).δ r
  simp only [rho_δ]
  by_cases h1 : r = rInput
  · subst h1; simp only [↓reduceIte]; omega
  · by_cases h2 : r = rOutput
    · subst h2; simp only [show rOutput ≠ rInput by decide, ↓reduceIte]; omega
    · simp only [h1, h2, ↓reduceIte]; omega

theorem rho_var_in (m : Nat) (q : Int) : (rho m).var (memVar rInput q) = memVar rInput (q + 8 * (m : Int)) := by
  rw [Reloc.var_memVar, rho_wshift_in]

theorem rho_var_out (m : Nat) (q : Int) : (rho m).var (memVar rOutput q) = memVar rOutput (q + 4 * (m : Int)) := by
  rw [Reloc.var_memVar, rho_wshift_out]

theorem reloc_ptr_stack (m : Nat) (o : Int) : E.reloc (rho m) (.ptr ⟨rStack, o⟩) = .ptr ⟨rStack, o⟩ := by
  show E.ptr ⟨rStack, o + (rho m).δ rStack⟩ = _
  rw [rho_δ, if_neg (by decide), if_neg (by decide), Int.add_zero]

theorem reloc_ptr_in (m : Nat) (o : Int) : E.reloc (rho m) (.ptr ⟨rInput, o⟩) = .ptr ⟨rInput, o + 64 * (m : Int)⟩ := by
  show E.ptr ⟨rInput, o + (rho m).δ rInput⟩ = _
  rw [rho_δ, if_pos rfl]

theorem reloc_ptr_out (m : Nat) (o : Int) : E.reloc (rho m) (.ptr ⟨rOutput, o⟩) = .ptr ⟨rOutput, o + 32 * (m : Int)⟩ := by
  show E.ptr ⟨rOutput, o + (rho m).δ rOutput⟩ = _
  rw [rho_δ, if_neg (by decide), if_pos rfl]

/-! ## The digests (shared with `LibX86`) -/

theorem digest_congr (input : Int → BitVec 64) (S T : State (BitVec 64)) (n : Nat)
    (h : ∀ w : Nat, w < 4 → T.mem rOutput (Int.ofNat (4 * n + w)) = S.mem rOutput (Int.ofNat (4 * n + w)))
    (hd : Digest input S n) : Digest input T n := by
  intro w i hw hi
  rw [h w hw]
  exact hd w i hw hi

/-! ## The entry as a pseudo-cut -/

/-- The control words at a call: `rsp`, `rsi`, `rdi`. -/
def entryCtl : List Nat := [260, 262, 263]

/-- The closed control state at a call at node offset 0. -/
def entrySc : State (BitVec 64) :=
  { v := Vector.replicate 32 (Vector.replicate 8 0), g := Vector.replicate 32 ⟨0, 0⟩,
    gd := ((((Vector.replicate 32 (0 : BitVec 64)).set 4 (gprWord ⟨rStack, 1048576⟩)).set 6
      (gprWord ⟨rInput, 0⟩)).set 7 (gprWord ⟨rOutput, 0⟩)),
    k := Vector.replicate 8 0, zf := false, cf := false, nf := false, vf := false, vl := 0,
    mem := fun _ _ => 0, pc := 0, depth := 0, err := false, halted := false, tail := none }

theorem entry_bounds (off count : Nat) (h : 64 * (off + count) ≤ 2 ^ 54) :
    (⟨rInput, 64 * (off : Int)⟩ : Addr).wf ∧ (⟨rOutput, 32 * (off : Int)⟩ : Addr).wf := by
  have hb : 64 * (off + count) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  constructor
  · show 0 ≤ 64 * (off : Int) ∧ 64 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  · show 0 ≤ 32 * (off : Int) ∧ 32 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega

theorem PreCut.entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (hE : Entry off count input S)
    (hb : 64 * (off + count) ≤ 2 ^ 54) : PreCut (rho off) entryCtl entrySc S := by
  obtain ⟨hwi, hwo⟩ := entry_bounds off count hb
  obtain ⟨g, k, -, -, n, v, l, d⟩ := hE.ctrl
  refine ⟨fun i hi _ => ?_, k, n, v, l, d⟩
  simp only [entryCtl, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · rw [cutVar_ptr_of entryCtl S 260 ⟨rStack, 1048576⟩ (by decide) ((envOf_gdVar S 4 (by decide)).trans hE.rsp)
      (by decide) (by decide), show cutVar entryCtl entrySc 260 = .ptr ⟨rStack, 1048576⟩ by decide +kernel, reloc_ptr_stack]
  · rw [cutVar_ptr_of entryCtl S 262 ⟨rInput, 64 * (off : Int)⟩ (by decide) ((envOf_gdVar S 6 (by decide)).trans hE.rsi)
      hwi (by show rInput ≠ 0; decide), show cutVar entryCtl entrySc 262 = .ptr ⟨rInput, 0⟩ by decide +kernel,
      reloc_ptr_in, Int.zero_add]
  · rw [cutVar_ptr_of entryCtl S 263 ⟨rOutput, 32 * (off : Int)⟩ (by decide) ((envOf_gdVar S 7 (by decide)).trans hE.rdi)
      hwo (by show rOutput ≠ 0; decide), show cutVar entryCtl entrySc 263 = .ptr ⟨rOutput, 0⟩ by decide +kernel,
      reloc_ptr_out, Int.zero_add]

/-- The count steps start at a kernel call. -/
theorem Fr.entry (rodata : Array (BitVec 64)) (prog : Array Instr) (off count : Nat) (input : Int → BitVec 64)
    (S : State (BitVec 64)) (hE : Entry off count input S) :
    Fr rodata prog S 0 S.pc S.zf S.cf [(2, (count : Int))] [] := by
  apply Fr.start S _ hE.ctrl.1 _ hE.ok.1 hE.ok.2.1 hE.ok.2.2
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  subst hp
  exact hE.rdx


/-! ## A generated segment, bundled -/

/-- What a generated segment (`Gen*/Seg.lean`) proves, at every relocated position. -/
structure SegFacts (rodata : Array (BitVec 64)) (prog : Array Instr) where
  ctl0 : List Nat
  sc0 : State (BitVec 64)
  ctlK : List Nat
  scK : State (BitVec 64)
  len : Nat
  wok : Region × Int → Bool
  run : ∀ (ρ : Reloc), ρ.ok → ρ.within (2 ^ 54) → ∀ S0 : State (BitVec 64),
    relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0 → SliceCert.Ok S0 →
    SliceCert.Ok (X86.isa.run rodata prog len S0) ∧
    relocState ρ (cutOf ctlK scK) = cutOf ctlK (X86.isa.run rodata prog len S0)
  frame : ∀ (ρ : Reloc), ρ.ok → ρ.within (2 ^ 54) → ∀ S0 : State (BitVec 64),
    relocState ρ (cutOf ctl0 sc0) = cutOf ctl0 S0 → SliceCert.Ok S0 →
    ∀ (r : Region) (q : Int), wok (r, q - ρ.wshift r) = false → (X86.isa.run rodata prog len S0).mem r q = S0.mem r q

/-! ## Glue between the pieces of a kernel run -/

/-- The fetch-execute loop is idle once halted: a longer run gives the same state. -/
theorem run_pad (rodata : Array (BitVec 64)) (prog : Array Instr) (S : State (BitVec 64)) (m n : Nat)
    (hm : m ≤ n) (hh : (X86.isa.run rodata prog m S).halted = true) :
    X86.isa.run rodata prog n S = X86.isa.run rodata prog m S := by
  rw [show n = m + (n - m) by omega, Isa.run_add, Isa.run_halted _ _ _ _ _ hh]

/-- A `PreCut` with respect to another closed state that agrees on the control words and parts. -/
theorem PreCut.transfer {ρ : Reloc} {L : List Nat} {sc sc' S : State (BitVec 64)} (h : PreCut ρ L sc S)
    (hv : (L.all fun i => cutVar L sc i == cutVar L sc' i) = true)
    (hf : sc.k = sc'.k ∧ sc.nf = sc'.nf ∧ sc.vf = sc'.vf ∧ sc.vl = sc'.vl ∧ sc.depth = sc'.depth) :
    PreCut ρ L sc' S := by
  obtain ⟨hw, hk, hn, hvf, hvl, hd⟩ := h
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf
  refine ⟨fun i hi hc => ?_, hk.trans f1, hn.trans f2, hvf.trans f3, hvl.trans f4, hd.trans f5⟩
  have := List.all_eq_true.mp hv i hi
  rw [beq_iff_eq] at this
  rw [hw i hi hc, this]

/-- One segment after another at the same relocation (the end cut of `A` is the start cut of `B`
up to closed facts). -/
theorem seg_chain {rodata : Array (BitVec 64)} {prog : Array Instr} (A B : SegFacts rodata prog) (ρ : Reloc)
    (hρ : ρ.ok) (S : State (BitVec 64)) (h : relocState ρ (cutOf A.ctlK A.scK) = cutOf A.ctlK S)
    (hL : (B.ctl0.all fun i => A.ctlK.contains i && (decide (i < 288) || memVarRegion i == rStack)) = true)
    (hv : (B.ctl0.all fun i => cutVar A.ctlK A.scK i == cutVar B.ctl0 B.sc0 i) = true)
    (hc : A.scK.g = B.sc0.g ∧ A.scK.k = B.sc0.k ∧ A.scK.zf = B.sc0.zf ∧ A.scK.cf = B.sc0.cf ∧ A.scK.nf = B.sc0.nf ∧
      A.scK.vf = B.sc0.vf ∧ A.scK.vl = B.sc0.vl ∧ A.scK.pc = B.sc0.pc ∧ A.scK.depth = B.sc0.depth) :
    relocState ρ (cutOf B.ctl0 B.sc0) = cutOf B.ctl0 S := by
  have f := cut_fields ρ _ _ S h
  obtain ⟨g1, k1, z1, c1, n1, v1, l1, p1, d1⟩ := f
  obtain ⟨g2, k2, z2, c2, n2, v2, l2, p2, d2⟩ := hc
  exact cut_transfer ρ ρ hρ hρ A.ctlK B.ctl0 A.scK B.sc0 S S h (hL_dec _ _ hL) (fun _ _ => rfl)
    (hval_same ρ _ _ _ _ hv)
    ⟨g1.trans g2, k1.trans k2, z1.trans z2, c1.trans c2, n1.trans n2, v1.trans v2, l1.trans l2, p1.trans p2, d1.trans d2⟩

/-- A `ret` at call depth 0 ends the run. -/
theorem run_ret0 (rodata : Array (BitVec 64)) (prog : Array Instr) (T : State (BitVec 64)) (hh : T.halted = false)
    (hi : prog.getD T.pc .nop = .ret) (hd : T.depth = 0) :
    X86.isa.run rodata prog 1 T = { T with halted := true } := by
  rw [X86.run_one rodata prog T hh, hi]
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, hd]

/-- A tail call ends the run. -/
theorem run_tail (rodata : Array (BitVec 64)) (prog : Array Instr) (T : State (BitVec 64)) (hh : T.halted = false)
    (name : String) (hi : prog.getD T.pc .nop = .tailcall name) :
    X86.isa.run rodata prog 1 T = { T with halted := true, tail := some name } := by
  rw [X86.run_one rodata prog T hh, hi]
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte]

/-- A taken conditional tail call ends the run. -/
theorem run_jcct (rodata : Array (BitVec 64)) (prog : Array Instr) (T : State (BitVec 64)) (hh : T.halted = false)
    (c : Cond) (name : String) (hi : prog.getD T.pc .nop = .jcct c name) (hc : condF T.zf T.cf c = true) :
    X86.isa.run rodata prog 1 T = { T with halted := true, tail := some name } := by
  rw [X86.run_one rodata prog T hh, hi]
  have h2 : condHolds T c = true := by rw [condHolds_eq]; exact hc
  simp only [exec, hh, Bool.false_eq_true, ↓reduceIte, h2]

/-- A control word of a relocated cut that is a closed number. -/
theorem cut_num (ρ : Reloc) (hρ : ρ.ok) (L : List Nat) (sc S : State (BitVec 64))
    (h : relocState ρ (cutOf L sc) = cutOf L S) (i : Nat) (hi : i ∈ L) (hcell : i < 288) (w : BitVec 64)
    (hw : cutVar L sc i = .const w) : envOf S i = w := by
  have := cut_word ρ hρ L sc S h i (Or.inl hcell)
  rw [hw] at this
  exact cut_const L S i hi w this

/-- A control word of a relocated cut that is a closed pointer. -/
theorem cut_ptr' (ρ : Reloc) (hρ : ρ.ok) (L : List Nat) (sc S : State (BitVec 64))
    (h : relocState ρ (cutOf L sc) = cutOf L S) (i : Nat) (hi : i ∈ L) (hcell : i < 288) (a : Addr)
    (hw : cutVar L sc i = .ptr a) : envOf S i = gprWord (ρ.addr a) := by
  have := cut_word ρ hρ L sc S h i (Or.inl hcell)
  rw [hw] at this
  exact cut_ptr L S i hi _ this

theorem rho_addr_in (m : Nat) (o : Int) : (rho m).addr ⟨rInput, o⟩ = ⟨rInput, o + 64 * (m : Int)⟩ := by
  show (⟨rInput, o + (rho m).δ rInput⟩ : Addr) = _
  rw [rho_δ, if_pos rfl]

theorem rho_addr_out (m : Nat) (o : Int) : (rho m).addr ⟨rOutput, o⟩ = ⟨rOutput, o + 32 * (m : Int)⟩ := by
  show (⟨rOutput, o + (rho m).δ rOutput⟩ : Addr) = _
  rw [rho_δ, if_neg (by decide), if_pos rfl]

theorem rho_addr_stack (m : Nat) (o : Int) : (rho m).addr ⟨rStack, o⟩ = ⟨rStack, o⟩ := by
  show (⟨rStack, o + (rho m).δ rStack⟩ : Addr) = _
  rw [rho_δ, if_neg (by decide), if_neg (by decide), Int.add_zero]

/-- **The hand-over at a tail call**: the state a tail call leaves (its control words `rdx`, `rsp`,
`rsi`, `rdi` are closed words of the last segment's end cut, relocated by `rho m`) is the entry state
of the called kernel on `r` nodes at node offset `m + b`. -/
theorem handover (ρm : Nat) (L : List Nat) (sc T Y : State (BitVec 64)) (input : Int → BitVec 64)
    (h : relocState (rho ρm) (cutOf L sc) = cutOf L T) (r b : Nat)
    (hchk : L.contains 258 && L.contains 260 && L.contains 262 && L.contains 263 &&
      (cutVar L sc 258 == .const (gprWord ⟨0, r⟩)) && (cutVar L sc 260 == .ptr ⟨rStack, 1048576⟩) &&
      (cutVar L sc 262 == .ptr ⟨rInput, 64 * (b : Int)⟩) && (cutVar L sc 263 == .ptr ⟨rOutput, 32 * (b : Int)⟩) &&
      (sc.g == Vector.replicate 32 ⟨0, 0⟩) && (sc.depth == 0) = true)
    (hY : Y.gd = T.gd ∧ Y.mem = T.mem ∧ Y.g = T.g ∧ Y.depth = T.depth ∧ Y.err = false ∧ Y.halted = false ∧ Y.tail = none)
    (hinp : ∀ q, T.mem rInput q = input q) :
    Entry (ρm + b) r input (normCtl Y) := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h258, h260⟩, h262⟩, h263⟩, c258⟩, c260⟩, c262⟩, c263⟩, cg⟩, cd⟩ := hchk
  have hρ := rho_ok ρm
  have f := cut_fields _ _ _ T h
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := hY
  have gd : ∀ n, n < 32 → (normCtl Y).getGD n = envOf T (256 + n) := by
    intro n hn; rw [envOf_gdVar T n hn]; show Y.gd.getD n 0 = T.gd.getD n 0; rw [y1]
  refine ⟨⟨?_, normCtl_k Y, rfl, rfl, rfl, rfl, rfl, ?_⟩, ⟨y5, y6, y7⟩, ?_, ?_, ?_, ?_, fun q => ?_⟩
  · show Y.g = _; rw [y3, f.1, cg]
  · show Y.depth = 0; rw [y4, f.2.2.2.2.2.2.2.2]; exact of_decide_eq_true cd
  · rw [gd 2 (by decide), cut_num _ hρ L sc T h 258 h258 (by decide) _ c258]
  · rw [gd 4 (by decide), cut_ptr' _ hρ L sc T h 260 h260 (by decide) _ c260, rho_addr_stack]
  · rw [gd 6 (by decide), cut_ptr' _ hρ L sc T h 262 h262 (by decide) _ c262, rho_addr_in]
    congr 2; push_cast; omega
  · rw [gd 7 (by decide), cut_ptr' _ hρ L sc T h 263 h263 (by decide) _ c263, rho_addr_out]
    congr 2; push_cast; omega
  · show Y.mem rInput q = input q; rw [y2]; exact hinp q

/-- The flag condition of a count step, decided (literal values) or by `omega` (symbolic counts). -/
macro "fr_cond" : tactic => `(tactic| first
  | decide
  | (simp only [condF, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false',
      Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_false_iff, Bool.or_eq_false_iff, Bool.not_true, Bool.not_false]
     <;> omega))

/-! ## Outcomes within a step bound; the facts carried along a run -/

section Run
variable (rodata : Array (BitVec 64)) (prog : Array Instr) (targets : List String)

/-- Every run of at least `k` steps from `U` is an outcome of the call from `S0`. -/
def Done (off c : Nat) (input : Int → BitVec 64) (S0 U : State (BitVec 64)) (k : Nat) : Prop :=
  ∀ n, k ≤ n → Library.Outcome EntryX86 Digest targets off c input S0 (X86.isa.run rodata prog n U)

variable {rodata prog targets}

theorem Done.mono {off c : Nat} {input : Int → BitVec 64} {S0 U : State (BitVec 64)} {k k' : Nat}
    (h : Done rodata prog targets off c input S0 U k) (hk : k ≤ k') : Done rodata prog targets off c input S0 U k' :=
  fun n hn => h n (by omega)

theorem Done.run {off c : Nat} {input : Int → BitVec 64} {S0 U U' : State (BitVec 64)} {k a : Nat}
    (hr : X86.isa.run rodata prog a U = U') (h : Done rodata prog targets off c input S0 U' k) :
    Done rodata prog targets off c input S0 U (a + k) := by
  intro n hn
  rw [show n = a + (n - a) by omega, Isa.run_add, hr]
  exact h _ (by omega)

/-- What every intermediate state of a call carries: it runs, the message is in place, the output
words before the call's nodes are untouched, and the first `done` nodes are hashed. -/
structure Inv (off c : Nat) (input : Int → BitVec 64) (S0 S : State (BitVec 64)) (done : Nat) : Prop where
  ok : SliceCert.Ok S
  inp : ∀ q, S.mem rInput q = input q
  pre : ∀ q : Int, q < 4 * (off : Int) → S.mem rOutput q = S0.mem rOutput q
  dig : ∀ n, n < done → Digest input S (off + n)

theorem Inv.of_mem {off c : Nat} {input : Int → BitVec 64} {S0 S T : State (BitVec 64)} {done : Nat}
    (h : Inv off c input S0 S done) (hok : SliceCert.Ok T) (hm : T.mem = S.mem) : Inv off c input S0 T done :=
  ⟨hok, fun q => by rw [hm]; exact h.inp q, fun q hq => by rw [hm]; exact h.pre q hq,
    fun n hn => digest_congr input S T _ (fun w _ => by rw [hm]) (h.dig n hn)⟩

/-- Count steps keep the memory. -/
theorem Inv.fr {off c : Nat} {input : Int → BitVec 64} {S0 S : State (BitVec 64)} {done m pc : Nat} {zf cf : Bool}
    {vals : List (Nat × Int)} {R : List Nat} (h : Inv off c input S0 S done) (f : Fr rodata prog S m pc zf cf vals R) :
    Inv off c input S0 (X86.isa.run rodata prog m S) done :=
  h.of_mem ⟨f.err, f.halted, f.tail⟩ f.near.2.2.2.2.2.2.1

/-- A segment at node `m` (at or after the nodes done) keeps the message, the earlier outputs and
the digests done, when it writes neither the input nor output words before its own nodes. -/
theorem Inv.seg {off c : Nat} {input : Int → BitVec 64} {S0 S : State (BitVec 64)} {done : Nat}
    (X : SegFacts rodata prog) (m : Nat) (hm : off + done ≤ m) (hw : 64 * m ≤ 2 ^ 54)
    (hcut : relocState (rho m) (cutOf X.ctl0 X.sc0) = cutOf X.ctl0 S) (h : Inv off c input S0 S done)
    (win : ∀ q, X.wok (rInput, q) = false) (wout : ∀ q : Int, q < 0 → X.wok (rOutput, q) = false) :
    Inv off c input S0 (X86.isa.run rodata prog X.len S) done := by
  have hρ := rho_ok m
  have hw' := rho_within m hw
  have fr := X.frame (rho m) hρ hw' S hcut h.ok
  have hout : ∀ q : Int, q < 4 * (m : Int) → (X86.isa.run rodata prog X.len S).mem rOutput q = S.mem rOutput q := by
    intro q hq; apply fr; rw [rho_wshift_out]; exact wout _ (by omega)
  refine ⟨(X.run (rho m) hρ hw' S hcut h.ok).1, fun q => (fr rInput q (win _)).trans (h.inp q),
    fun q hq => (hout q (by omega)).trans (h.pre q hq), fun n hn => ?_⟩
  apply digest_congr input S _ _ _ (h.dig n hn)
  intro w hw4
  exact hout _ (by simp only [Int.ofNat_eq_coe]; omega)

end Run

end Keccaktree.Asm.X86K
