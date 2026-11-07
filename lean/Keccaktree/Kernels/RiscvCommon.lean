import Keccaktree.Asm.RiscvSteps
import Keccaktree.Asm.Node
import Keccaktree.Asm.LibRv
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Shared definitions of the RISC-V all-count theorems

Relocation by whole nodes (`rho m`: 64 input bytes and 32 output bytes per node), the digest
predicate of the library (`LibX86.Digest input S n`: output words `4n..4n+3` hold keccak256 of input
node `n`), and the lemmas every RISC-V kernel's `All.lean` uses.
-/
namespace Keccaktree.Kernels.RiscvCommon
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak

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

theorem rho_const (m : Nat) (w : BitVec 64) : E.reloc (rho m) (.const w) = .const w := rfl

-- The digest predicate and node words of the library (`LibX86.Digest`, shared by every ISA).
export Keccaktree.Asm.LibX86 (nodeWords Digest digest_local)

theorem digest_congr (input : Int → BitVec 64) (S T : State (BitVec 64)) (n : Nat)
    (h : ∀ w : Nat, w < 4 → T.mem rOutput (Int.ofNat (4 * n + w)) = S.mem rOutput (Int.ofNat (4 * n + w)))
    (hd : Digest input S n) : Digest input T n := by
  intro w i hw hi
  rw [h w hw]
  exact hd w i hw hi

/-- The digest of node `m` from its four output lanes after the 24 rounds. -/
theorem digest_of (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat)
    (hw : ∀ w : Nat, w < 4 → S.mem rOutput (Int.ofNat (4 * m + w)) = L (Spec.rounds 24 (absorbNode (nodeWords input m))) w) :
    Digest input S m := by
  intro w i hw' hi
  rw [hw w hw', absorbNode_keccak, squeezeByte_eq]
  have e1 : (8 * w + i) / 8 = w := by omega
  have e2 : (8 * w + i) % 8 = i := by omega
  rw [e1, e2]
  simp only [Spec.keccakF, Fin.val_mk]

/-- An input word of node `m + n`, read through the relocation by `m` nodes. -/
theorem env_in (input : Int → BitVec 64) (S : State (BitVec 64)) (m n j : Nat) (hin : ∀ q, S.mem rInput q = input q) :
    envOf S ((rho m).var (memVar rInput (Int.ofNat (8 * n + j)))) = nodeWords input (m + n) j := by
  rw [rho_var_in, envOf_mem, hin]
  unfold nodeWords
  congr 1
  simp only [Int.ofNat_eq_coe]
  omega

/-- An output word of node `m + n`, read through the relocation by `m` nodes. -/
theorem env_out (S : State (BitVec 64)) (m n j : Nat) :
    envOf S ((rho m).var (memVar rOutput (Int.ofNat (4 * n + j)))) = S.mem rOutput (Int.ofNat (4 * (m + n) + j)) := by
  rw [rho_var_out, envOf_mem]
  congr 1
  simp only [Int.ofNat_eq_coe]
  omega

end Keccaktree.Kernels.RiscvCommon
