"""Shared pieces of the AArch64 all-count theorems (rendered by gen_all_arm.py)."""


def inv0(name, mod, n):
    """`<mod>.Inv0` at node offset `m`: the input words of nodes m..m+n-1 and their constant lanes."""
    consts = ', '.join(f'absorbNode_lane{k} _' for _ in range(n) for k in range(8, 25))
    q = ', '.join('?_' for _ in range(8 * n))
    return f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `{mod}`'s input invariant at node `m`, from the message. -/
theorem {name} (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat) (hin : ∀ q, S.mem rInput q = input q) :
    {mod}.Inv0 (fun i => envOf S ((rho m).var i)) (fun j => absorbNode (nodeWords input (m + j.val))) := by
  have key : ∀ q : Int, envOf S ((rho m).var (memVar rInput q)) = input (q + 8 * (m : Int)) := by
    intro q; rw [rho_var_in, envOf_mem, hin]
  refine ⟨{q}, {consts}⟩
  all_goals
    show envOf S ((rho m).var (memVar rInput _)) = _
    rw [key]
    simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, absorbNode_lane0, absorbNode_lane1, absorbNode_lane2,
      absorbNode_lane3, absorbNode_lane4, absorbNode_lane5, absorbNode_lane6, absorbNode_lane7, nodeWords, rotl0]
    congr 1
    simp only [Int.ofNat_eq_coe, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
    omega

'''


def digest(name, mod, n, j, K):
    """node `j` of `<mod>`'s output invariant at node offset `m` is the digest of node `m + j`"""
    hs = ', '.join(f'h{i}' for i in range(4 * n))
    cases = ''
    for w in range(4):
        cases += f'''    · have := h{4 * j + w}; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
'''
    return f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Node `{j}` of `{mod}`'s output invariant at node `m` is the digest of node `m + {j}`. -/
theorem {name} (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat)
    (h : {mod}.Inv{K} (fun i => envOf S ((rho m).var i)) ({mod}.AAt (fun j => absorbNode (nodeWords input (m + j.val))) {K})) :
    Digest input S (m + {j}) := by
  have key : ∀ w : Nat, envOf S ((rho m).var (memVar rOutput (Int.ofNat (4 * {j} + w)))) = S.mem rOutput (Int.ofNat (4 * (m + {j}) + w)) := by
    intro w; rw [rho_var_out, envOf_mem]; congr 1; simp only [Int.ofNat_eq_coe]; omega
  obtain ⟨{hs}⟩ := h
  have hw : ∀ w : Nat, w < 4 → S.mem rOutput (Int.ofNat (4 * (m + {j}) + w)) =
      L ({mod}.AAt (fun j => absorbNode (nodeWords input (m + j.val))) {K} ⟨{j}, by decide⟩) w := by
    intro w hw
    rw [← key w]
    rcases w with _ | _ | _ | _ | w
{cases}    · omega
  intro w i hw' hi
  have hr : {mod}.AAt (fun j => absorbNode (nodeWords input (m + j.val))) {K} ⟨{j}, by decide⟩ =
      Spec.rounds 24 (absorbNode (nodeWords input (m + {j}))) := {mod}.aat_{j} _
  rw [hw w hw', hr, absorbNode_keccak, squeezeByte_eq]
  have e1 : (8 * w + i) / 8 = w := by omega
  have e2 : (8 * w + i) % 8 = i := by omega
  rw [e1, e2]
  simp only [Spec.keccakF, Fin.val_mk]

'''


def entry_struct():
    return '''/-- The state with the flags of the closed control state `sc` (the flags a segment was recorded with). -/
@[reducible] def norm (S sc : State (BitVec 64)) : State (BitVec 64) := S.withFlags sc.zf sc.cf sc.nf sc.vf

/-- The entry state of a call (AAPCS64, any flags): `Arm.Entry`. -/
abbrev Entry := Arm.Entry

theorem wf_num (c : Int) (h0 : 0 ≤ c) (h1 : c ≤ 18014398509481984) : (⟨0, c⟩ : Addr).wf := by
  show 0 ≤ c ∧ c < 2 ^ 55
  rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega

'''
