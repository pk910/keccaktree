import Keccaktree.Kernels.X86X1.GenSE1.Seg
import Keccaktree.Kernels.X86X1.GenSE3.Seg
import Keccaktree.Kernels.X86X1.GenSB.Seg
import Keccaktree.Kernels.X86X1.GenSX.Seg
import Keccaktree.Asm.KernelGlue
import Keccaktree.Asm.Library
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_x86_x1` on any number of nodes

The kernel is a frame (pushes, `test rdx, rdx`, spills of the pointers and the
count), a loop whose body hashes one node and advances both pointers, a
`dec qword [rsp+424]; jne` back edge, and the epilogue.  Four generated
segments (`GenSE1` entry, `GenSE3` spills, `GenSB` body, `GenSX` epilogue) are
each proved once, symbolically, at every relocated position; the count steps
are the concrete lemmas of `X86Steps`; the loop is an induction over the
iterations, iteration `k` running the body relocated by `k` nodes.

**Result** (`x86_x1_all`): for every count `c` and node offset `off` with
`64·(off+c) ≤ 2^54`, from an entry state (`Entry`), `21 + 4269·c` steps halt
without a model fault and without a tail call, keep the output words before
node `off`, and leave in output words `4(off+n)+w` the keccak256 digest of input
node `off+n`, for every `n < c`.
-/
namespace Keccaktree.Kernels.X86X1.All
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak
open Keccaktree.Kernels.X86X1 (prog rodata)

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

/-! ## The calling convention and the digests -/

/-- The entry state of a call `keccaktree_keccak256_x86_x1(out, in, count)` at node offset `off`:
the control part of a fresh call, `rdx = count`, `rsp` at the top of the stack region, `rsi`/`rdi`
at node `off` of the input/output regions, the input region holding the message.  The vector
registers, the other general registers and every other memory word are arbitrary. -/
structure Entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.vl = 0 ∧ S.pc = 0 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  rdx : S.getGD 2 = gprWord ⟨0, count⟩
  rsp : S.getGD 4 = gprWord ⟨rStack, 1048576⟩
  rsi : S.getGD 6 = gprWord ⟨rInput, 64 * off⟩
  rdi : S.getGD 7 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

/-- The words of node `n` of the message. -/
def nodeWords (input : Int → BitVec 64) (n : Nat) (w : Nat) : BitVec 64 := input (Int.ofNat (8 * n + w))

/-- Output words `4n..4n+3` hold the keccak256 digest of input node `n` (byte `8w+i` of the digest
is byte `i` of word `4n+w`). -/
def Digest (input : Int → BitVec 64) (S : State (BitVec 64)) (n : Nat) : Prop :=
  ∀ w i : Nat, w < 4 → i < 8 →
    (S.mem rOutput (Int.ofNat (4 * n + w))).extractLsb' (8 * i) 8 = Spec.keccak256 64 (nodeBytes (nodeWords input n)) (8 * w + i)

theorem digest_congr (input : Int → BitVec 64) (S T : State (BitVec 64)) (n : Nat)
    (h : ∀ w : Nat, w < 4 → T.mem rOutput (Int.ofNat (4 * n + w)) = S.mem rOutput (Int.ofNat (4 * n + w)))
    (hd : Digest input S n) : Digest input T n := by
  intro w i hw hi
  rw [h w hw]
  exact hd w i hw hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The body's input invariant at node `m`, from the message. -/
theorem body_inv0 (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat) (hin : ∀ q, S.mem rInput q = input q) :
    GenSB.Inv0 (fun i => envOf S ((rho m).var i)) (fun _ => absorbNode (nodeWords input m)) := by
  have key : ∀ q : Int, envOf S ((rho m).var (memVar rInput q)) = input (q + 8 * (m : Int)) := by
    intro q; rw [rho_var_in, envOf_mem, hin]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, absorbNode_lane8 _, absorbNode_lane9 _, absorbNode_lane10 _,
    absorbNode_lane11 _, absorbNode_lane12 _, absorbNode_lane13 _, absorbNode_lane14 _, absorbNode_lane15 _,
    absorbNode_lane16 _, absorbNode_lane17 _, absorbNode_lane18 _, absorbNode_lane19 _, absorbNode_lane20 _,
    absorbNode_lane21 _, absorbNode_lane22 _, absorbNode_lane23 _, absorbNode_lane24 _⟩
  all_goals
    show envOf S ((rho m).var (memVar rInput _)) = _
    rw [key]
    simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, absorbNode_lane0, absorbNode_lane1, absorbNode_lane2,
      absorbNode_lane3, absorbNode_lane4, absorbNode_lane5, absorbNode_lane6, absorbNode_lane7, nodeWords, rotl0]
    congr 1
    simp only [Int.ofNat_eq_coe]
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The body's output invariant at node `m` is the digest of node `m`. -/
theorem body_digest (input : Int → BitVec 64) (S : State (BitVec 64)) (m : Nat)
    (h : GenSB.Inv25 (fun i => envOf S ((rho m).var i)) (GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25)) :
    Digest input S m := by
  have key : ∀ w : Nat, envOf S ((rho m).var (memVar rOutput (Int.ofNat (4 * 0 + w)))) = S.mem rOutput (Int.ofNat (4 * m + w)) := by
    intro w; rw [rho_var_out, envOf_mem]; congr 1; simp only [Int.ofNat_eq_coe]; omega
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hw : ∀ w : Nat, w < 4 → S.mem rOutput (Int.ofNat (4 * m + w)) =
      L (GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25 ⟨0, by decide⟩) w := by
    intro w hw
    rw [← key w]
    rcases w with _ | _ | _ | _ | w
    · have := h0; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h1; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h2; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · have := h3; simp only [specQuantity, specQuantity0, specQuantityCol, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, rotl0] at this; exact this
    · omega
  intro w i hw' hi
  have hr : GenSB.AAt (fun _ => absorbNode (nodeWords input m)) 25 ⟨0, by decide⟩ =
      Spec.rounds 24 (absorbNode (nodeWords input m)) := GenSB.aat_0 _
  rw [hw w hw', hr, absorbNode_keccak, squeezeByte_eq]
  have e1 : (8 * w + i) / 8 = w := by omega
  have e2 : (8 * w + i) % 8 = i := by omega
  rw [e1, e2]
  simp only [Spec.keccakF, Fin.val_mk]

/-! ## The loop -/

/-- The state at the loop head before iteration `k` (of a call on `c` nodes at offset `off` from
`S0`): the body's start cut relocated by `off + k` nodes, the count word `c - k`, the message,
the earlier output words, and the digests of the nodes done. -/
@[reducible] def Head (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (k : Nat) (S : State (BitVec 64)) : Prop :=
  relocState (rho (off + k)) (cutOf GenSB.ctl0 GenSB.sc0) = cutOf GenSB.ctl0 S ∧ SliceCert.Ok S ∧
  S.mem rStack 131064 = gprWord ⟨0, (c : Int) - k⟩ ∧ (∀ q, S.mem rInput q = input q) ∧
  (∀ q : Int, q < 4 * (off : Int) → S.mem rOutput q = S0.mem rOutput q) ∧
  (∀ n, n < k → Digest input S (off + n))

/-- The state at the epilogue: its start cut (relocated by `m` nodes; only the stack pointer is a
control word), the earlier output words, and every digest. -/
@[reducible] def ExitAt (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (S : State (BitVec 64)) : Prop :=
  relocState (rho m) (cutOf GenSX.ctl0 GenSX.sc0) = cutOf GenSX.ctl0 S ∧ SliceCert.Ok S ∧
  (∀ q : Int, q < 4 * (off : Int) → S.mem rOutput q = S0.mem rOutput q) ∧
  (∀ n, n < c → Digest input S (off + n))

/-- The control fields of a state after concrete steps that changed only flags and `pc`. -/
theorem ctrl_after (U T sc sc' : State (BitVec 64))
    (hT : T.g = sc.g ∧ T.k = sc.k ∧ T.zf = sc.zf ∧ T.cf = sc.cf ∧ T.nf = sc.nf ∧ T.vf = sc.vf ∧ T.vl = sc.vl ∧
      T.pc = sc.pc ∧ T.depth = sc.depth)
    (hU : U.g = T.g ∧ U.k = T.k ∧ U.nf = T.nf ∧ U.vf = T.vf ∧ U.vl = T.vl ∧ U.depth = T.depth)
    (hcl : sc.g = sc'.g ∧ sc.k = sc'.k ∧ sc.nf = sc'.nf ∧ sc.vf = sc'.vf ∧ sc.vl = sc'.vl ∧ sc.depth = sc'.depth)
    (hzf : U.zf = sc'.zf) (hcf : U.cf = sc'.cf) (hpc : U.pc = sc'.pc) :
    U.g = sc'.g ∧ U.k = sc'.k ∧ U.zf = sc'.zf ∧ U.cf = sc'.cf ∧ U.nf = sc'.nf ∧ U.vf = sc'.vf ∧
      U.vl = sc'.vl ∧ U.pc = sc'.pc ∧ U.depth = sc'.depth := by
  obtain ⟨g1, k1, _, _, n1, v1, l1, _, d1⟩ := hT
  obtain ⟨g2, k2, n2, v2, l2, d2⟩ := hU
  obtain ⟨g3, k3, n3, v3, l3, d3⟩ := hcl
  exact ⟨g2.trans (g1.trans g3), k2.trans (k1.trans k3), hzf, hcf, n2.trans (n1.trans n3), v2.trans (v1.trans v3),
    l2.trans (l1.trans l3), hpc, d2.trans (d1.trans d3)⟩

theorem body_len : GenSB.segLen = 4267 := by decide +kernel
theorem prog_600 : prog.getD 600 .nop = .decm (.base 4 424) := by decide +kernel
theorem prog_601 : prog.getD 601 .nop = .jcc .ne 13 := by decide +kernel

/-- The body's write condition is false outside the node's own output words and the stack. -/
theorem wok_out (q : Int) (h : q < 0 ∨ 4 ≤ q) :
    ((rOutput == 3 && q != 131064) || (rOutput == 2 && decide (0 ≤ q) && decide (q < 4))) = false := by
  rcases h with h | h
  · rw [show decide (0 ≤ q) = false from decide_eq_false (by omega)]; rfl
  · rw [show decide (q < 4) = false from decide_eq_false (by omega)]
    cases decide (0 ≤ q) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One iteration of the loop.** From the loop head before iteration `k < c`, `4269` steps
(body, `dec`, `jne`) reach the loop head before iteration `k + 1`, or the epilogue after the last. -/
theorem iter (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (k : Nat) (S : State (BitVec 64)) (hk : k < c) (hH : Head off c input S0 k S) :
    (k + 1 < c → Head off c input S0 (k + 1) (X86.isa.run rodata prog 4269 S)) ∧
    (k + 1 = c → ExitAt off c input S0 (off + k) (X86.isa.run rodata prog 4269 S)) := by
  obtain ⟨hcut, hok, hcnt, hin, hpre, hdig⟩ := hH
  have hρ := rho_ok (off + k)
  have hw : (rho (off + k)).within GenSB.B := rho_within (off + k) (by omega)
  have sr := GenSB.seg_run (rho (off + k)) hρ hw S hcut hok
  have fr := GenSB.seg_frame (rho (off + k)) hρ hw S hcut hok
  have dat := GenSB.seg_data (rho (off + k)) hρ hw S hcut hok _ (body_inv0 input S (off + k) hin)
  generalize hSb : GenSB.segAt25 S = Sb at sr fr dat
  obtain ⟨hrun, hokb, hcutb⟩ := sr
  have fb := cut_fields _ _ _ _ hcutb
  -- the stack pointer at the end of the body
  have hsp : Sb.getGD 4 = gprWord ⟨rStack, 1048088⟩ := by
    have e1 := cut_word (rho (off + k)) hρ GenSB.ctl25 GenSB.sc25 Sb hcutb 260 (Or.inl (by decide))
    rw [show cutVar GenSB.ctl25 GenSB.sc25 260 = .ptr ⟨rStack, 1048088⟩ by decide +kernel, reloc_ptr_stack] at e1
    rw [← envOf_gdVar Sb 4 (by decide)]
    exact cut_ptr GenSB.ctl25 Sb 260 (by decide) _ e1
  have hgx : gx Sb 4 = some ⟨rStack, 1048088⟩ := gx_of_word Sb 4 _ hsp (by decide)
  -- the count word survives the body
  have hcntb : Sb.mem rStack 131064 = gprWord ⟨0, (c : Int) - k⟩ := by
    rw [fr rStack 131064 (by rw [rho_wshift_stack]; decide), hcnt]
  have hpcb : Sb.pc = 600 := fb.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hhb : Sb.halted = false := hokb.2.1
  -- dec qword [rsp+424]
  have hb' : 64 * (off + c) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hdec : X86.exec rodata (.decm (.base 4 424)) Sb =
      next { Sb with mem := memStore Sb.mem rStack 131064 (gprWord ⟨0, (c : Int) - k - 1⟩), zf := decide ((c : Int) - k - 1 = 0) } :=
    exec_decm_num rodata Sb 4 424 ⟨rStack, 1048088⟩ ((c : Int) - k) hhb hgx (by decide) (by decide)
      hcntb (by
        show 0 ≤ (c : Int) - k ∧ (c : Int) - k < 2 ^ 55
        rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega)
  generalize hV : next { Sb with mem := memStore Sb.mem rStack 131064 (gprWord ⟨0, (c : Int) - k - 1⟩), zf := decide ((c : Int) - k - 1 = 0) } = V at hdec
  have hrunV : X86.isa.run rodata prog 1 Sb = V := by
    rw [X86.run_one rodata prog Sb hhb, show prog.getD Sb.pc .nop = .decm (.base 4 424) by rw [hpcb]; exact prog_600, hdec]
  have hpcV : V.pc = 601 := by rw [← hV]; show Sb.pc + 1 = 601; rw [hpcb]
  have hhV : V.halted = false := by rw [← hV]; exact hhb
  -- jne loop
  have hrunU : X86.isa.run rodata prog 1 V = { V with pc := if condHolds V .ne then 13 else V.pc + 1 } := by
    rw [X86.run_one rodata prog V hhV, show prog.getD V.pc .nop = .jcc .ne 13 by rw [hpcV]; exact prog_601]
    exact exec_jcc_eq rodata V .ne 13 hhV
  generalize hU : { V with pc := if condHolds V .ne then 13 else V.pc + 1 } = U at hrunU
  have hrun4269 : X86.isa.run rodata prog 4269 S = U := by
    rw [show 4269 = GenSB.segLen + 1 + 1 by rw [body_len], Isa.run_add, Isa.run_add, hrun, hrunV, hrunU]
  rw [hrun4269]
  -- the fields of U
  have hUmem : U.mem = memStore Sb.mem rStack 131064 (gprWord ⟨0, (c : Int) - k - 1⟩) := by subst hU hV; rfl
  have hUzf : U.zf = decide ((c : Int) - k - 1 = 0) := by subst hU hV; rfl
  have hUpc : U.pc = if decide ((c : Int) - k - 1 = 0) then 602 else 13 := by
    rw [← hU]; show (if condHolds V .ne then 13 else V.pc + 1) = _
    rw [hpcV, show condHolds V .ne = !V.zf from rfl, show V.zf = decide ((c : Int) - k - 1 = 0) by subst hV; rfl]
    cases decide ((c : Int) - k - 1 = 0) <;> rfl
  have hUc : U.g = Sb.g ∧ U.k = Sb.k ∧ U.nf = Sb.nf ∧ U.vf = Sb.vf ∧ U.vl = Sb.vl ∧ U.depth = Sb.depth := by
    rw [← hU, ← hV]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hUcf : U.cf = Sb.cf := by subst hU hV; rfl
  have hUok : SliceCert.Ok U := by rw [← hU, ← hV]; exact hokb
  have hUenv : ∀ i, i ≠ memVar rStack 131064 → envOf U i = envOf Sb i := by
    intro i hi
    rw [← envOf_memStore_other Sb rStack 131064 (gprWord ⟨0, (c : Int) - k - 1⟩) i hi, ← hU, ← hV]; rfl
  have hUo : ∀ q, U.mem rOutput q = Sb.mem rOutput q := by
    intro q; rw [hUmem]; exact memStore_other _ _ _ _ _ _ (Or.inl (by decide))
  have hUi : ∀ q, U.mem rInput q = Sb.mem rInput q := by
    intro q; rw [hUmem]; exact memStore_other _ _ _ _ _ _ (Or.inl (by decide))
  -- frames of the body
  have hbi : ∀ q, Sb.mem rInput q = S.mem rInput q := fun q => fr rInput q rfl
  have hbo : ∀ q : Int, q - 4 * ((off + k : Nat) : Int) < 0 → Sb.mem rOutput q = S.mem rOutput q := by
    intro q hq
    apply fr rOutput q
    rw [rho_wshift_out]
    exact wok_out _ (Or.inl hq)
  have hpre' : ∀ q : Int, q < 4 * (off : Int) → U.mem rOutput q = S0.mem rOutput q := by
    intro q hq; rw [hUo, hbo q (by omega)]; exact hpre q hq
  have hdig' : ∀ n, n < k + 1 → Digest input U (off + n) := by
    intro n hn
    by_cases hnk : n < k
    · apply digest_congr input S U (off + n) _ (hdig n hnk)
      intro w hw; rw [hUo]; exact hbo _ (by simp only [Int.ofNat_eq_coe]; omega)
    · have hnk' : n = k := by omega
      rw [hnk']
      apply digest_congr input Sb U (off + k) (fun w _ => hUo _)
      exact body_digest input Sb (off + k) dat
  have hL : ∀ L' : List Nat, (L'.all fun i => GenSB.ctl25.contains i && (decide (i < 288) || memVarRegion i == rStack)) = true →
      ∀ i ∈ L', envOf U i = envOf Sb i := by
    intro L' hL' i hi
    apply hUenv
    have := (hL_dec GenSB.ctl25 L' hL' i hi).1
    intro he; rw [he] at this; revert this; decide +kernel
  refine ⟨fun hk1 => ?_, fun hk1 => ?_⟩
  · -- back to the loop head, one node further
    have hz : decide ((c : Int) - k - 1 = 0) = false := decide_eq_false (by omega)
    refine ⟨?_, hUok, ?_, fun q => (hUi q).trans ((hbi q).trans (hin q)), hpre', hdig'⟩
    · rw [show off + (k + 1) = (off + k) + 1 by omega, ← rho_add]
      apply cut_transfer (rho (off + k)) _ hρ (Reloc.add_ok _ _ hρ (rho_ok 1)) GenSB.ctl25 GenSB.ctl0 GenSB.sc25 GenSB.sc0 Sb U hcutb
        (hL_dec _ _ (by decide +kernel)) (hL _ (by decide +kernel))
        (hval_succ _ _ hρ (rho_ok 1) _ _ _ _ (by decide +kernel))
      exact ctrl_after U Sb GenSB.sc25 GenSB.sc0 fb hUc (by decide +kernel)
        (by rw [hUzf, hz]; decide +kernel) (by rw [hUcf, fb.2.2.2.1]; decide +kernel)
        (by rw [hUpc, hz]; decide +kernel)
    · -- (`congr 2` here closed `⟨0, ↑c - ↑k - 1⟩ = ⟨0, ↑c - ↑(k + 1)⟩` by `rfl` at default transparency,
      -- unfolding the Int arithmetic for > 40 min; `omega` on the offset is immediate)
      rw [hUmem, memStore_same]
      exact congrArg (fun z : Int => gprWord ⟨0, z⟩) (by omega)
  · -- the last iteration: on to the epilogue
    have hz : decide ((c : Int) - k - 1 = 0) = true := decide_eq_true (by omega)
    refine ⟨?_, hUok, hpre', ?_⟩
    · apply cut_transfer (rho (off + k)) _ hρ hρ GenSB.ctl25 GenSX.ctl0 GenSB.sc25 GenSX.sc0 Sb U hcutb
        (hL_dec _ _ (by decide +kernel)) (hL _ (by decide +kernel))
        (hval_same _ _ _ _ _ (by decide +kernel))
      exact ctrl_after U Sb GenSB.sc25 GenSX.sc0 fb hUc (by decide +kernel)
        (by rw [hUzf, hz]; decide +kernel) (by rw [hUcf, fb.2.2.2.1]; decide +kernel)
        (by rw [hUpc, hz]; decide +kernel)
    · intro n hn; exact hdig' n (by omega)

/-- **The loop**: from the loop head before iteration `k`, the remaining `d + 1 = c - k` iterations
reach the epilogue with every digest written. -/
theorem loop (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ d k (S : State (BitVec 64)), k + d + 1 = c → Head off c input S0 k S →
      ExitAt off c input S0 (off + c - 1) (X86.isa.run rodata prog (4269 * (d + 1)) S) := by
  intro d
  induction d with
  | zero =>
    intro k S hk hH
    have := (iter off c input S0 hb k S (by omega) hH).2 (by omega)
    rw [show off + c - 1 = off + k by omega, show 4269 * (0 + 1) = 4269 from rfl]
    exact this
  | succ d ih =>
    intro k S hk hH
    have h1 := (iter off c input S0 hb k S (by omega) hH).1 (by omega)
    rw [show 4269 * (d + 1 + 1) = 4269 + 4269 * (d + 1) by omega, Isa.run_add]
    exact ih (k + 1) _ (by omega) h1

theorem exit_len : GenSX.segLen = 7 := rfl
theorem prog_609 : prog.getD 609 .nop = .ret := by decide +kernel

theorem exec_ret0 (S : State (BitVec 64)) (hh : S.halted = false) (hd : S.depth = 0) :
    X86.exec rodata .ret S = { S with halted := true } := by
  simp only [X86.exec, hh, Bool.false_eq_true, ↓reduceIte, hd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The epilogue**: `add rsp; pop ×6; ret` halts with the memory unchanged. -/
theorem epilogue (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (hm : 64 * m ≤ 2 ^ 54)
    (U : State (BitVec 64)) (hX : ExitAt off c input S0 m U) :
    (X86.isa.run rodata prog 8 U).halted = true ∧ (X86.isa.run rodata prog 8 U).err = false ∧
    (X86.isa.run rodata prog 8 U).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (X86.isa.run rodata prog 8 U).mem rOutput q = S0.mem rOutput q) ∧
    ∀ n, n < c → Digest input (X86.isa.run rodata prog 8 U) (off + n) := by
  obtain ⟨hcut, hok, hpre, hdig⟩ := hX
  have hρ := rho_ok m
  have hw : (rho m).within GenSX.B := rho_within m hm
  have sr := GenSX.seg_run (rho m) hρ hw U hcut hok
  have fr := GenSX.seg_frame (rho m) hρ hw U hcut hok
  generalize hSx : GenSX.segAt1 U = Sx at sr fr
  obtain ⟨hrun, hokx, hcutx⟩ := sr
  have fx := cut_fields _ _ _ _ hcutx
  have hpc : Sx.pc = 609 := fx.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hd : Sx.depth = 0 := fx.2.2.2.2.2.2.2.2.trans (by decide +kernel)
  have hr : X86.isa.run rodata prog 8 U = { Sx with halted := true } := by
    rw [show 8 = GenSX.segLen + 1 by rw [exit_len], Isa.run_add, hrun, X86.run_one rodata prog Sx hokx.2.1,
      show prog.getD Sx.pc .nop = .ret by rw [hpc]; exact prog_609, exec_ret0 Sx hokx.2.1 hd]
  have hmem : ∀ r q, Sx.mem r q = U.mem r q := fun r q => fr r q rfl
  rw [hr]
  refine ⟨rfl, hokx.1, hokx.2.2, fun q hq => (hmem _ _).trans (hpre q hq), fun n hn => ?_⟩
  exact digest_congr input U _ _ (fun w _ => hmem _ _) (hdig n hn)

/-! ## The whole call -/

theorem e1_len : GenSE1.segLen = 7 := rfl
theorem e3_len : GenSE3.segLen = 4 := rfl
theorem prog_7 : prog.getD 7 .nop = .test 2 2 := by decide +kernel
theorem prog_8 : prog.getD 8 .nop = .jcc .e 602 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`keccaktree_keccak256_x86_x1` on any number of nodes.**  For every count `c` and node offset
`off` with `64·(off + c) ≤ 2^54`, from an entry state, `21 + 4269·c` steps of the fetch-execute loop
halt without a model fault and without a tail call, keep the output words before node `off`, and
leave the keccak256 digest of input node `off + n` in output words `4(off+n) .. 4(off+n)+3`, for
every `n < c`. -/
theorem x86_x1_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    (X86.isa.run rodata prog (21 + 4269 * c) S).halted = true ∧
    (X86.isa.run rodata prog (21 + 4269 * c) S).err = false ∧
    (X86.isa.run rodata prog (21 + 4269 * c) S).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (X86.isa.run rodata prog (21 + 4269 * c) S).mem rOutput q = S.mem rOutput q) ∧
    ∀ n, n < c → Digest input (X86.isa.run rodata prog (21 + 4269 * c) S) (off + n) := by
  have hρ := rho_ok off
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hwf_in : (⟨rInput, 64 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 64 * (off : Int) ∧ 64 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hwf_out : (⟨rOutput, 32 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 32 * (off : Int) ∧ 32 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  -- the entry cut, at node offset `off`
  have hc0 : relocState (rho off) (cutOf GenSE1.ctl0 GenSE1.sc0) = cutOf GenSE1.ctl0 S := by
    apply relocState_cutOf (rho off) GenSE1.ctl0 GenSE1.sc0 S
    · intro i hi
      simp only [GenSE1.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · rw [cutVar_ptr_of GenSE1.ctl0 S 260 ⟨rStack, 1048576⟩ (by decide) ((envOf_gdVar S 4 (by decide)).trans hE.rsp) (by decide) (by decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 260 = .ptr ⟨rStack, 1048576⟩ by decide +kernel, reloc_ptr_stack]
      · rw [cutVar_ptr_of GenSE1.ctl0 S 262 ⟨rInput, 64 * (off : Int)⟩ (by decide) ((envOf_gdVar S 6 (by decide)).trans hE.rsi) hwf_in (by show rInput ≠ 0; decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 262 = .ptr ⟨rInput, 0⟩ by decide +kernel, reloc_ptr_in, Int.zero_add]
      · rw [cutVar_ptr_of GenSE1.ctl0 S 263 ⟨rOutput, 32 * (off : Int)⟩ (by decide) ((envOf_gdVar S 7 (by decide)).trans hE.rdi) hwf_out (by show rOutput ≠ 0; decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 263 = .ptr ⟨rOutput, 0⟩ by decide +kernel, reloc_ptr_out, Int.zero_add]
    · intro i hi h; simp only [GenSE1.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
    · obtain ⟨g, k, z, cf, n, v, l, p, d⟩ := hE.ctrl
      rw [g, k, z, cf, n, v, l, p, d]
      decide +kernel
  -- E1: pushes, frame
  have hw0 : (rho off).within (2 ^ 54) := rho_within off (by omega)
  have s1 := GenSE1.seg_run (rho off) hρ hw0 S hc0 hE.ok
  have f1 := GenSE1.seg_frame (rho off) hρ hw0 S hc0 hE.ok
  have m1 := GenSE1.seg_moves (rho off) hρ hw0 S hc0 hE.ok 258 258 (by simp)
  generalize hT1 : GenSE1.segAt1 S = T1 at s1 f1 m1
  obtain ⟨hrun1, hok1, hcut1⟩ := s1
  have ft1 := cut_fields _ _ _ _ hcut1
  have hrdx1 : T1.getGD 2 = gprWord ⟨0, c⟩ := by
    rw [Reloc.var_lt (rho off) 258 (by decide)] at m1
    rw [← envOf_gdVar T1 2 (by decide)]
    exact m1.trans ((envOf_gdVar S 2 (by decide)).trans hE.rdx)
  have hpc1 : T1.pc = 7 := ft1.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hh1 : T1.halted = false := hok1.2.1
  -- test rdx, rdx ; je
  have ht := exec_test_num rodata T1 2 c hh1 hrdx1 (by
    show 0 ≤ (c : Int) ∧ (c : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega)
  have hrunT2 : X86.isa.run rodata prog 1 T1 = next { T1 with zf := decide ((c : Int) = 0), cf := false } := by
    rw [X86.run_one rodata prog T1 hh1, show prog.getD T1.pc .nop = .test 2 2 by rw [hpc1]; exact prog_7, ht]
  generalize hT2 : next { T1 with zf := decide ((c : Int) = 0), cf := false } = T2 at hrunT2
  have hpc2 : T2.pc = 8 := by rw [← hT2]; show T1.pc + 1 = 8; rw [hpc1]
  have hh2 : T2.halted = false := by rw [← hT2]; exact hh1
  have hrunT3 : X86.isa.run rodata prog 1 T2 = { T2 with pc := if condHolds T2 .e then 602 else T2.pc + 1 } := by
    rw [X86.run_one rodata prog T2 hh2, show prog.getD T2.pc .nop = .jcc .e 602 by rw [hpc2]; exact prog_8]
    exact exec_jcc_eq rodata T2 .e 602 hh2
  generalize hT3 : { T2 with pc := if condHolds T2 .e then 602 else T2.pc + 1 } = T3 at hrunT3
  have hT3zf : T3.zf = decide ((c : Int) = 0) := by subst hT3 hT2; rfl
  have hT3cf : T3.cf = false := by subst hT3 hT2; rfl
  have hT3pc : T3.pc = if decide ((c : Int) = 0) then 602 else 9 := by
    rw [← hT3]; show (if T2.zf then 602 else T2.pc + 1) = _
    rw [hpc2, show T2.zf = decide ((c : Int) = 0) by subst hT2; rfl]
  have hT3c : T3.g = T1.g ∧ T3.k = T1.k ∧ T3.nf = T1.nf ∧ T3.vf = T1.vf ∧ T3.vl = T1.vl ∧ T3.depth = T1.depth := by
    rw [← hT3, ← hT2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hT3env : ∀ i, envOf T3 i = envOf T1 i := by intro i; rw [← hT3, ← hT2]; rfl
  have hT3mem : T3.mem = T1.mem := by subst hT3 hT2; rfl
  have hT3ok : SliceCert.Ok T3 := by rw [← hT3, ← hT2]; exact hok1
  have h9 : X86.isa.run rodata prog 9 S = T3 := by
    rw [show 9 = GenSE1.segLen + 1 + 1 by rw [e1_len], Isa.run_add, Isa.run_add, hrun1, hrunT2, hrunT3]
  have hpre3 : ∀ q : Int, T3.mem rOutput q = S.mem rOutput q := by
    intro q; rw [hT3mem]; exact f1 rOutput q rfl
  have hin3 : ∀ q : Int, T3.mem rInput q = input q := by
    intro q; rw [hT3mem, f1 rInput q rfl]; exact hE.inp q
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- no node: straight to the epilogue
    subst hc
    have hz : decide (((0 : Nat) : Int) = 0) = true := rfl
    have hX : ExitAt off 0 input S off T3 := by
      refine ⟨?_, hT3ok, fun q _ => hpre3 q, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      apply cut_transfer (rho off) (rho off) hρ hρ GenSE1.ctl1 GenSX.ctl0 GenSE1.sc1 GenSX.sc0 T1 T3 hcut1
        (hL_dec _ _ (by decide +kernel)) (fun i _ => hT3env i) (hval_same _ _ _ _ _ (by decide +kernel))
      exact ctrl_after T3 T1 GenSE1.sc1 GenSX.sc0 ft1 hT3c (by decide +kernel)
        (by rw [hT3zf, hz]; decide +kernel) (by rw [hT3cf]; decide +kernel) (by rw [hT3pc, hz]; decide +kernel)
    have he := epilogue off 0 input S off (by omega) T3 hX
    rw [show 21 + 4269 * 0 = 9 + 8 + 4 by rfl, Isa.run_add, Isa.run_add, h9]
    rw [Isa.run_halted _ _ _ _ _ he.1]
    exact he
  · -- E3: spills; then the loop and the epilogue
    have hz : decide ((c : Int) = 0) = false := decide_eq_false (by omega)
    have hc3 : relocState (rho off) (cutOf GenSE3.ctl0 GenSE3.sc0) = cutOf GenSE3.ctl0 T3 := by
      apply cut_transfer (rho off) (rho off) hρ hρ GenSE1.ctl1 GenSE3.ctl0 GenSE1.sc1 GenSE3.sc0 T1 T3 hcut1
        (hL_dec _ _ (by decide +kernel)) (fun i _ => hT3env i) (hval_same _ _ _ _ _ (by decide +kernel))
      exact ctrl_after T3 T1 GenSE1.sc1 GenSE3.sc0 ft1 hT3c (by decide +kernel)
        (by rw [hT3zf, hz]; decide +kernel) (by rw [hT3cf]; decide +kernel) (by rw [hT3pc, hz]; decide +kernel)
    have s3 := GenSE3.seg_run (rho off) hρ hw0 T3 hc3 hT3ok
    have f3 := GenSE3.seg_frame (rho off) hρ hw0 T3 hc3 hT3ok
    have m3 := GenSE3.seg_moves (rho off) hρ hw0 T3 hc3 hT3ok 2097315 258 (by simp)
    generalize hT5 : GenSE3.segAt1 T3 = T5 at s3 f3 m3
    obtain ⟨hrun3, hok3, hcut3⟩ := s3
    have ft3 := cut_fields _ _ _ _ hcut3
    have hH : Head off c input S 0 T5 := by
      refine ⟨?_, hok3, ?_, fun q => (f3 rInput q rfl).trans (hin3 q), fun q _ => (f3 rOutput q rfl).trans (hpre3 q),
        fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      · apply cut_transfer (rho off) (rho (off + 0)) hρ hρ GenSE3.ctl1 GenSB.ctl0 GenSE3.sc1 GenSB.sc0 T5 T5 hcut3
          (hL_dec _ _ (by decide +kernel)) (fun i _ => rfl) (hval_same _ _ _ _ _ (by decide +kernel))
        exact ctrl_after T5 T5 GenSE3.sc1 GenSB.sc0 ft3 ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (by decide +kernel)
          (ft3.2.2.1.trans (by decide +kernel)) (ft3.2.2.2.1.trans (by decide +kernel))
          (ft3.2.2.2.2.2.2.2.1.trans (by decide +kernel))
      · rw [rho_var_stack off 2097315 (by decide) (by decide +kernel), Reloc.var_lt (rho off) 258 (by decide)] at m3
        rw [show (2097315 : Nat) = memVar rStack 131064 by decide +kernel, envOf_mem] at m3
        rw [m3, hT3env, (envOf_gdVar T1 2 (by decide) : envOf T1 258 = T1.getGD 2), hrdx1]
        simp
    have hl := loop off c input S hb (c - 1) 0 T5 (by omega) hH
    rw [show c - 1 + 1 = c by omega] at hl
    have he := epilogue off c input S (off + c - 1) (by omega) _ hl
    have hrun3' : X86.isa.run rodata prog 4 T3 = T5 := by rw [← e3_len]; exact hrun3
    rw [show 21 + 4269 * c = 9 + 4 + 4269 * c + 8 by omega, Isa.run_add, Isa.run_add, Isa.run_add, h9, hrun3']
    exact he

/-! ## In the library -/

/-- The x86 calling convention of the library at node offset `off` (within the address bound). -/
def EntryX86 (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  Entry off count input { S with pc := 0 } ∧ 64 * (off + count) ≤ 2 ^ 54

/-- `keccaktree_keccak256_x86_x1` as a kernel of the library (rank 0: it hands nothing over). -/
def kernel : Library.KernelThm X86.isa EntryX86 Digest where
  name := "x86_x1"
  rank := 0
  rodata := rodata
  prog := prog
  entry := 0
  steps := fun _ c => 21 + 4269 * c
  thm := fun off count input S h => by
    obtain ⟨hh, he, ht, hp, hd⟩ := x86_x1_all off count input _ h.1 h.2
    exact ⟨hh, he, hp, Or.inl ⟨ht, hd⟩⟩

theorem digest_local : Library.DigestLocal Digest := by
  intro input S S' n h hd w i hw hi
  rw [h (Int.ofNat (4 * n + w)) (by simp only [Int.ofNat_eq_coe]; omega) (by simp only [Int.ofNat_eq_coe]; omega)]
  exact hd w i hw hi

theorem ranks_ok : Library.RanksOk [kernel] := by
  intro K hK off count input S hS next done htail _
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
  subst hK
  have ht : (X86.isa.run rodata prog (21 + 4269 * count) { S with pc := 0 }).tail = none :=
    (x86_x1_all off count input _ hS.1 hS.2).2.2.1
  have h := ht.symm.trans htail
  cases h

/-- **The library theorem on the table `[x86_x1]`**: from the library's x86 entry state, the run
halts without a model fault with every node's digest in place. -/
theorem lib_x86_x1 (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hS : EntryX86 "x86_x1" off count input S) : Library.LibOk [kernel] kernel off count input S :=
  Library.lib_correct [kernel] 0 (by simp [kernel]) ranks_ok digest_local _ kernel (by simp) off count input S
    (Nat.le_refl _) hS

end Keccaktree.Kernels.X86X1.All
