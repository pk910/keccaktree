import Keccaktree.Asm.X86Frame
import Keccaktree.Asm.Final
import Keccaktree.Asm.Node
import Keccaktree.Asm.Library
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The x86 kernels on any number of nodes: shared definitions

* `rho m`: relocation by `m` nodes (64 input bytes, 32 output bytes per node);
* `Entry off count input S`: the state at a kernel call (or a tail call) on `count` nodes at node
  offset `off`: `rdx = count`, `rsp` at the top of the stack, `rsi`/`rdi` at node `off`, the
  message in the input region; the flags are arbitrary (the frame's first count step or the
  generated prologue proved for every flag value overwrites them);
* `Digest input S n`: the output words of node `n` hold the keccak256 digest of input node `n`;
* `entrySc`, `PreCut.entry`: the entry state as the "end" of a pseudo-segment, so that the frame's
  count steps (`Fr`) and `Fr.cut` apply from the entry on.
-/
namespace Keccaktree.Asm.X86K
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak

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

/-! ## The calling convention and the digests -/

/-- The state at a call (or tail call) of an x86 kernel on `count` nodes at node offset `off`. -/
structure Entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.nf = false ∧ S.vf = false ∧
    S.vl = 0 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  rdx : S.getGD 2 = gprWord ⟨0, count⟩
  rsp : S.getGD 4 = gprWord ⟨rStack, 1048576⟩
  rsi : S.getGD 6 = gprWord ⟨rInput, 64 * off⟩
  rdi : S.getGD 7 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q
  bound : 64 * (off + count) ≤ 2 ^ 54

/-- The library's x86 calling convention (every x86 kernel; the name selects nothing). -/
def EntryX86 (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  Entry off count input S

/-- The words of node `n` of the message. -/
def nodeWords (input : Int → BitVec 64) (n : Nat) (w : Nat) : BitVec 64 := input (Int.ofNat (8 * n + w))

/-- Output words `4n..4n+3` hold the keccak256 digest of input node `n`. -/
def Digest (input : Int → BitVec 64) (S : State (BitVec 64)) (n : Nat) : Prop :=
  ∀ w i : Nat, w < 4 → i < 8 →
    (S.mem rOutput (Int.ofNat (4 * n + w))).extractLsb' (8 * i) 8 = Spec.keccak256 64 (nodeBytes (nodeWords input n)) (8 * w + i)

theorem digest_congr (input : Int → BitVec 64) (S T : State (BitVec 64)) (n : Nat)
    (h : ∀ w : Nat, w < 4 → T.mem rOutput (Int.ofNat (4 * n + w)) = S.mem rOutput (Int.ofNat (4 * n + w)))
    (hd : Digest input S n) : Digest input T n := by
  intro w i hw hi
  rw [h w hw]
  exact hd w i hw hi

theorem digest_local : Library.DigestLocal Digest := by
  intro input S S' n h hd w i hw hi
  rw [h (Int.ofNat (4 * n + w)) (by simp only [Int.ofNat_eq_coe]; omega) (by simp only [Int.ofNat_eq_coe]; omega)]
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

theorem PreCut.entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (hE : Entry off count input S) :
    PreCut (rho off) entryCtl entrySc S := by
  obtain ⟨hwi, hwo⟩ := entry_bounds off count hE.bound
  obtain ⟨g, k, n, v, l, d⟩ := hE.ctrl
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

end Keccaktree.Asm.X86K
