import Keccaktree.Asm.Cut
import Keccaktree.Proof
/-!
The specification state of one 64-byte node given as 8 little-endian words
(as the kernels load it), and what its lanes are: the words in lanes 0..7,
the padding in lanes 8 and 16, zero elsewhere.  These discharge the entry
invariant (`Inv0`) of a kernel's first slice.
-/
namespace Keccaktree.Asm.X86
open Keccak

/-- The bytes of a node from its words. -/
def nodeBytes (w : Nat → BitVec 64) (i : Nat) : BitVec 8 := (w (i / 8) >>> (8 * (i % 8))).truncate 8

/-- The sponge state after absorbing the padded node. -/
def absorbNode (w : Nat → BitVec 64) : Spec.State :=
  Spec.absorb ⟨fun _ _ => 0#64⟩ (fun i => Spec.padded 64 (nodeBytes w) (136 * 0 + i))

/-- keccak256 of the node, as `Spec.keccak256` sees it. -/
theorem absorbNode_keccak (w : Nat → BitVec 64) :
    Spec.keccak256 64 (nodeBytes w) = Spec.squeezeByte (Spec.keccakF (absorbNode w)) := by
  simp only [Spec.keccak256, Spec.paddedLen, Spec.absorbBlocks, absorbNode, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul]

macro "lane_simp_node" : tactic =>
  `(tactic| simp +decide only [L, absorbNode, Spec.absorb, Spec.padded, Spec.paddedLen, Spec.ld64, nodeBytes,
      Fin.isValue, Keccaktree.Proof.Fin.val_lit0, Keccaktree.Proof.Fin.val_lit1, Keccaktree.Proof.Fin.val_lit2, Keccaktree.Proof.Fin.val_lit3, Keccaktree.Proof.Fin.val_lit4,
      Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff])

theorem absorbNode_lane0 (w) : L (absorbNode w) 0 = w 0 := by lane_simp_node; bv_decide
theorem absorbNode_lane1 (w) : L (absorbNode w) 1 = w 1 := by lane_simp_node; bv_decide
theorem absorbNode_lane2 (w) : L (absorbNode w) 2 = w 2 := by lane_simp_node; bv_decide
theorem absorbNode_lane3 (w) : L (absorbNode w) 3 = w 3 := by lane_simp_node; bv_decide
theorem absorbNode_lane4 (w) : L (absorbNode w) 4 = w 4 := by lane_simp_node; bv_decide
theorem absorbNode_lane5 (w) : L (absorbNode w) 5 = w 5 := by lane_simp_node; bv_decide
theorem absorbNode_lane6 (w) : L (absorbNode w) 6 = w 6 := by lane_simp_node; bv_decide
theorem absorbNode_lane7 (w) : L (absorbNode w) 7 = w 7 := by lane_simp_node; bv_decide
theorem absorbNode_lane8 (w) : L (absorbNode w) 8 = 1#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane16 (w) : L (absorbNode w) 16 = 0x8000000000000000#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane9 (w) : L (absorbNode w) 9 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane10 (w) : L (absorbNode w) 10 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane11 (w) : L (absorbNode w) 11 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane12 (w) : L (absorbNode w) 12 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane13 (w) : L (absorbNode w) 13 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane14 (w) : L (absorbNode w) 14 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane15 (w) : L (absorbNode w) 15 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane17 (w) : L (absorbNode w) 17 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane18 (w) : L (absorbNode w) 18 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane19 (w) : L (absorbNode w) 19 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane20 (w) : L (absorbNode w) 20 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane21 (w) : L (absorbNode w) 21 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane22 (w) : L (absorbNode w) 22 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane23 (w) : L (absorbNode w) 23 = 0#64 := by lane_simp_node; bv_decide
theorem absorbNode_lane24 (w) : L (absorbNode w) 24 = 0#64 := by lane_simp_node; bv_decide

theorem absorbNode_zero (w) (k : Nat) (hk : 8 < k ∧ k < 25 ∧ k ≠ 16) : L (absorbNode w) k = 0#64 :=
  match k, hk with
  | 9, _ => absorbNode_lane9 w
  | 10, _ => absorbNode_lane10 w
  | 11, _ => absorbNode_lane11 w
  | 12, _ => absorbNode_lane12 w
  | 13, _ => absorbNode_lane13 w
  | 14, _ => absorbNode_lane14 w
  | 15, _ => absorbNode_lane15 w
  | 17, _ => absorbNode_lane17 w
  | 18, _ => absorbNode_lane18 w
  | 19, _ => absorbNode_lane19 w
  | 20, _ => absorbNode_lane20 w
  | 21, _ => absorbNode_lane21 w
  | 22, _ => absorbNode_lane22 w
  | 23, _ => absorbNode_lane23 w
  | 24, _ => absorbNode_lane24 w
  | 16, h => absurd rfl h.2.2
  | k + 25, h => absurd h.2.1 (by omega)
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h => absurd h.1 (by omega)

end Keccaktree.Asm.X86
