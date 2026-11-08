import Keccaktree.Asm.Library
import Keccaktree.Asm.LibX86
import Keccaktree.Asm.Iter
import Keccaktree.Asm.Node
import Keccaktree.Proof
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Nodes: relocation by whole nodes and the digest predicate (shared by the all-count theorems)

`rho m` moves the input pointer by `64·m` bytes and the output pointer by `32·m` bytes (`m`
nodes).  The digest predicate is the library's (`LibX86.Digest`, `LibX86.nodeWords`).
-/
namespace Keccaktree.Asm.Nodes
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak
open Keccaktree.Asm.LibX86 (nodeWords Digest)

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

theorem rho_var_stack (m i : Nat) (h : 288 ≤ i) (hr : memVarRegion i = rStack) : (rho m).var i = i := by
  unfold Reloc.var
  rw [if_neg (by omega), hr, rho_wshift_stack, Int.add_zero, ← hr]
  exact memVar_region_index i h

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

theorem digest_congr (input : Int → BitVec 64) (S T : State (BitVec 64)) (n : Nat)
    (h : ∀ w : Nat, w < 4 → T.mem rOutput (Int.ofNat (4 * n + w)) = S.mem rOutput (Int.ofNat (4 * n + w)))
    (hd : Digest input S n) : Digest input T n := by
  intro w i hw hi
  rw [h w hw]
  exact hd w i hw hi

end Keccaktree.Asm.Nodes
