import Keccaktree.Kernels.RiscvCommon
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Bytes: misaligned buffers of the RISC-V kernels

The kernels hash nodes at any byte offset of their buffers.  A buffer at machine address `≡ m (mod 8)`
is the region pointer `⟨r, m + …⟩`; its message bytes are bytes of the region's words (`byteAt`,
little endian).  This file gives

* the byte view of a region (`byteAt`, `wordAt`: the 8 bytes at a byte address as a word), the node
  words of a message at a byte offset (`nodeWordsB`) and the digest predicate at a byte offset
  (`DigestB`; `DigestB 0 0 = Digest`);
* concrete steps of `lbu`/`sb` (`exec_lbu_eq`, `exec_sb_eq`) and of the scalar instructions on a
  state with the scalar kernels' control part (`Ctl0`);
* **the byte-copy loop** `COPY_BYTES` (`lbu; sb; addi; addi; addi -1; bnez`) for any count, any
  source/destination regions and byte offsets (`copy_loop`): `6 n` steps copy `n` bytes and change no
  other byte.
-/
namespace Keccaktree.Kernels.RiscvBytes
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak Keccaktree.Kernels.RiscvCommon
open Keccaktree.Asm.Riscv (setR getR insByte wordOf byteOf run_one exec_opi_eq exec_br_num getR_pos getR_zero
  setR_getGD_same setR_getGD_other setR_mem' setR_pc setR_halted setR_err setR_tail setR_k setR_g setR_zf setR_cf
  setR_nf setR_vf setR_vl setR_depth next_halted next_err next_tail next_g next_k next_zf
  next_cf next_nf next_vf next_vl next_depth gx_word)
open Keccaktree.Asm.Arm (gx addr withAddr)

/-! ## The byte view of a region -/

/-- Byte `b` of a region with words `W` (little endian). -/
def byteAt (W : Int → BitVec 64) (b : Int) : BitVec 8 := (W (b / 8)).extractLsb' (8 * (b % 8).toNat) 8

/-- The 8 bytes at byte address `b` of a region, as a word. -/
def wordAt (W : Int → BitVec 64) (b : Int) : BitVec 64 :=
  if b % 8 = 0 then W (b / 8)
  else (W (b / 8) >>> (8 * (b % 8).toNat)) ||| (W (b / 8 + 1) <<< (64 - 8 * (b % 8).toNat))

/-- Word `w` of node `n` of the message at byte offset `m` of the input region. -/
def nodeWordsB (input : Int → BitVec 64) (m n w : Nat) : BitVec 64 := wordAt input (m + 64 * n + 8 * w)

/-- Bytes `mo + 32n .. mo + 32n + 31` of the output region hold the keccak256 digest of node `n` of
the message at byte offset `mi` of the input region. -/
def DigestB (mi mo : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) (n : Nat) : Prop :=
  ∀ j : Nat, j < 32 → byteAt (S.mem rOutput) (mo + 32 * n + j) = Spec.keccak256 64 (nodeBytes (nodeWordsB input mi n)) j

theorem byteAt_word (W : Int → BitVec 64) (q : Int) (j : Nat) (hj : j < 8) :
    byteAt W (8 * q + j) = (W q).extractLsb' (8 * j) 8 := by
  unfold byteAt
  have e1 : (8 * q + j) / 8 = q := by omega
  have e2 : ((8 * q + j) % 8).toNat = j := by omega
  rw [e1, e2]

theorem wordAt_aligned (W : Int → BitVec 64) (q : Int) : wordAt W (8 * q) = W q := by
  unfold wordAt
  rw [if_pos (by omega : (8 * q) % 8 = 0)]
  exact congrArg W (by omega)

theorem nodeWordsB_zero (input : Int → BitVec 64) (n w : Nat) :
    nodeWordsB input 0 n w = nodeWords input n w := by
  have h : ∀ x : Int, x = 8 * ((8 * n + w : Nat) : Int) → wordAt input x = nodeWords input n w := by
    intro x hx; rw [hx, wordAt_aligned]; rfl
  exact h _ (by push_cast; omega)

/-- At byte offsets 0 the byte digest is the word digest of the library. -/
theorem digestB_zero (input : Int → BitVec 64) (S : State (BitVec 64)) (n : Nat) :
    DigestB 0 0 input S n ↔ Digest input S n := by
  have hw : nodeWordsB input 0 n = nodeWords input n := funext fun w => nodeWordsB_zero input n w
  have hb : ∀ w i : Nat, i < 8 → byteAt (S.mem rOutput) (((0 : Nat) : Int) + 32 * (n : Int) + ((8 * w + i : Nat) : Int)) =
      (S.mem rOutput (Int.ofNat (4 * n + w))).extractLsb' (8 * i) 8 := by
    intro w i hi
    have : ((0 : Nat) : Int) + 32 * (n : Int) + ((8 * w + i : Nat) : Int) = 8 * ((4 * n + w : Nat) : Int) + (i : Int) := by
      push_cast; omega
    rw [this, byteAt_word _ _ _ hi]; rfl
  unfold DigestB Digest
  rw [hw]
  constructor
  · intro h w i hw' hi
    rw [← hb w i hi]; exact h (8 * w + i) (by omega)
  · intro h j hj
    have e : j = 8 * (j / 8) + j % 8 := by omega
    have := h (j / 8) (j % 8) (by omega) (Nat.mod_lt _ (by decide))
    rw [← hb _ _ (Nat.mod_lt _ (by decide)), ← e] at this
    exact this

/-! ## Bit-vector facts (by cases on the byte positions) -/

theorem cases8 (k : Nat) (h : k < 8) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega

theorem insByte_bv (w x : BitVec 64) (k : Nat) :
    (insByte w x k : BitVec 64) = (w &&& ~~~(0xff#64 <<< (8 * k))) ||| ((x &&& 0xff#64) <<< (8 * k)) := rfl

/-- A byte of `insByte`. -/
theorem insByte_byte (w x : BitVec 64) (k j : Nat) (hk : k < 8) (hj : j < 8) :
    (insByte w x k : BitVec 64).extractLsb' (8 * j) 8 = if j = k then x.extractLsb' 0 8 else w.extractLsb' (8 * j) 8 := by
  rw [insByte_bv]
  rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cases8 j hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> bv_decide

/-- The loaded byte (`lbu`) is the byte. -/
theorem lbu_byte (w : BitVec 64) (k : Nat) (hk : k < 8) :
    ((w >>> (8 * k)) &&& 0xff#64).extractLsb' 0 8 = w.extractLsb' (8 * k) 8 := by
  rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_decide

/-- A byte of the word at a byte address. -/
theorem wordAt_byte (W : Int → BitVec 64) (b : Int) (j : Nat) (hj : j < 8) :
    (wordAt W b).extractLsb' (8 * j) 8 = byteAt W (b + j) := by
  obtain ⟨k, hk8, hk⟩ : ∃ k : Nat, k < 8 ∧ b % 8 = k := ⟨(b % 8).toNat, by omega, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q : Int, b = 8 * q + k := ⟨b / 8, by omega⟩
  subst hq
  unfold wordAt byteAt
  have c1 : ((8 * q + (k : Int)) % 8 = 0) ↔ k = 0 := by omega
  have c2 : ((8 * q + (k : Int)) % 8).toNat = k := by omega
  have c3 : (8 * q + (k : Int)) / 8 = q := by omega
  have c4 : (8 * q + (k : Int) + (j : Int)) / 8 = q + ((k + j) / 8 : Nat) := by omega
  have c5 : ((8 * q + (k : Int) + (j : Int)) % 8).toNat = (k + j) % 8 := by omega
  rw [c2, c3, c4, c5]
  simp only [c1]
  rcases cases8 k hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cases8 j hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp <;> bv_decide

/-- Two words with the same 8 bytes are equal. -/
theorem word_ext (x y : BitVec 64) (h : ∀ j, j < 8 → x.extractLsb' (8 * j) 8 = y.extractLsb' (8 * j) 8) : x = y := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  have h4 := h 4 (by decide); have h5 := h 5 (by decide); have h6 := h 6 (by decide); have h7 := h 7 (by decide)
  simp only [Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  bv_decide

/-- A word of a region whose bytes are those of the word at a byte address. -/
theorem word_of_bytes (W V : Int → BitVec 64) (q b : Int) (h : ∀ j : Nat, j < 8 → byteAt W (8 * q + j) = byteAt V (b + j)) :
    W q = wordAt V b := by
  apply word_ext
  intro j hj
  rw [← byteAt_word W q j hj, wordAt_byte V b j hj]
  exact h j hj

/-! ## Byte stores -/

/-- Store the low byte of `x` at byte `b` of region `r` (`sb`). -/
def storeByte (M : Region → Int → BitVec 64) (r : Region) (b : Int) (x : BitVec 64) : Region → Int → BitVec 64 :=
  memStore M r (b / 8) (insByte (M r (b / 8)) x (b % 8).toNat)

theorem byteAt_storeByte (M : Region → Int → BitVec 64) (r : Region) (b : Int) (x : BitVec 64) (r' : Region) (b' : Int) :
    byteAt (storeByte M r b x r') b' = if r' = r ∧ b' = b then x.extractLsb' 0 8 else byteAt (M r') b' := by
  unfold storeByte byteAt
  by_cases hr : r' = r
  · subst hr
    by_cases hq : b' / 8 = b / 8
    · rw [hq, memStore_same, insByte_byte _ _ _ _ (by omega) (by omega)]
      by_cases hb : b' = b
      · subst hb; simp
      · have : ¬ ((b' % 8).toNat = (b % 8).toNat) := by omega
        simp only [this, ↓reduceIte, hb, and_false]
    · rw [memStore_other _ _ _ _ _ _ (Or.inr hq)]
      have : ¬ b' = b := fun h => hq (by rw [h])
      simp [this]
  · rw [memStore_other _ _ _ _ _ _ (Or.inl hr)]
    simp [hr]

/-- A word none of whose bytes is the stored one is kept. -/
theorem storeByte_word (M : Region → Int → BitVec 64) (r : Region) (b : Int) (x : BitVec 64) (r' : Region) (q : Int)
    (h : r' ≠ r ∨ q ≠ b / 8) : storeByte M r b x r' q = M r' q := by
  unfold storeByte
  exact memStore_other _ _ _ _ _ _ h

/-! ## Concrete steps -/

/-- The control part of the scalar kernels' states (entry: library-normalised; never changed). -/
def Ctl0 (T : State (BitVec 64)) : Prop :=
  T.g = Vector.replicate 32 ⟨0, 0⟩ ∧ T.k = Vector.replicate 8 0 ∧ T.zf = false ∧ T.cf = false ∧ T.nf = false ∧
    T.vf = false ∧ T.vl = 0 ∧ T.depth = 0 ∧ T.err = false ∧ T.halted = false ∧ T.tail = none

theorem replicate_set (n : Nat) : (Vector.replicate 32 (⟨0, 0⟩ : Addr)).setIfInBounds n ⟨0, 0⟩ = Vector.replicate 32 ⟨0, 0⟩ := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_setIfInBounds, Vector.getElem_replicate]
  split <;> rfl

theorem Ctl0.setR {T : State (BitVec 64)} (h : Ctl0 T) (n : Nat) (x : BitVec 64) : Ctl0 (setR T n x) := by
  obtain ⟨g, k, z, c, nf, v, l, d, e, hh, t⟩ := h
  by_cases hn : n = 0
  · subst hn; exact ⟨g, k, z, c, nf, v, l, d, e, hh, t⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [setR_g _ _ hn, g, replicate_set]
    all_goals simp only [setR_k, setR_zf, setR_cf, setR_nf, setR_vf, setR_vl, setR_depth, setR_err, setR_halted, setR_tail, *]

theorem Ctl0.next {T : State (BitVec 64)} (h : Ctl0 T) : Ctl0 (Riscv.next T) := h
theorem Ctl0.withMem {T : State (BitVec 64)} (h : Ctl0 T) (m : Region → Int → BitVec 64) : Ctl0 { T with mem := m } := h
theorem Ctl0.withPc {T : State (BitVec 64)} (h : Ctl0 T) (p : Nat) : Ctl0 { T with pc := p } := h

theorem Ctl0.ok {T : State (BitVec 64)} (h : Ctl0 T) : SliceCert.Ok T := ⟨h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩
theorem Ctl0.halted {T : State (BitVec 64)} (h : Ctl0 T) : T.halted = false := h.2.2.2.2.2.2.2.2.2.1

/-- A general register after `setR` (registers `< 32`). -/
theorem getGD_setR (S : State (BitVec 64)) (n m : Nat) (hn : n < 32) (x : BitVec 64) :
    (setR S n x).getGD m = if m = n ∧ n ≠ 0 then x else S.getGD m := by
  by_cases hm : m = n
  · subst hm
    by_cases h0 : m = 0
    · subst h0; simp [setR]
    · rw [if_pos ⟨rfl, h0⟩]
      exact setR_getGD_same S m hn h0 x
  · simp only [hm, false_and, ↓reduceIte]
    exact setR_getGD_other S n m hm x

theorem addr_zero (S : State (BitVec 64)) (b : Nat) (a : Addr) (hb : S.getGD b = gprWord a) (hwf : a.wf) :
    addr S b 0 = some a := by
  show (Arm.gx S b).map (fun a => (⟨a.region, a.off + 0⟩ : Addr)) = some a
  rw [gx_word S b a hb hwf]
  rcases a with ⟨r, o⟩
  simp

theorem loadWords_wordOf (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (a : Addr) (hr : a.region ≠ rRodata) :
    S.loadWords rodata (wordOf a) 1 = some [S.mem a.region (a.off / 8)] := by
  have h1 : (wordOf a).off % 8 = 0 := by simp only [wordOf]; omega
  rw [State.loadWords, if_pos h1]
  simp only [List.range_one, List.map_cons, List.map_nil]
  rw [show (wordOf a).off / 8 + Int.ofNat 0 = a.off / 8 by simp only [wordOf, Int.ofNat_eq_natCast, Int.natCast_zero]; omega]
  show some [S.read rodata a.region (a.off / 8)] = _
  simp only [State.read, if_neg hr]

theorem storeWords_wordOf (S : State (BitVec 64)) (a : Addr) (hr : a.region ≠ rRodata) (v : BitVec 64) :
    S.storeWords (wordOf a) [v] = some { S with mem := memStore S.mem a.region (a.off / 8) v } := by
  have h1 : (wordOf a).off % 8 = 0 ∧ (wordOf a).region ≠ rRodata := ⟨by simp only [wordOf]; omega, hr⟩
  rw [State.storeWords, if_pos h1]
  simp only [memStoreFrom]
  rw [show (wordOf a).off / 8 = a.off / 8 by simp only [wordOf]; omega]
  rfl

/-- `lbu d, 0(b)`: the byte, zero-extended. -/
theorem exec_lbu_eq (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d b : Nat) (a : Addr)
    (hh : S.halted = false) (hb : S.getGD b = gprWord a) (hwf : a.wf) (hr : a.region ≠ rRodata) :
    Riscv.exec vlmax rodata (.lbu d b 0) S =
      Riscv.next (setR S d ((S.mem a.region (a.off / 8) >>> (8 * (a.off % 8).toNat)) &&& 0xff#64)) := by
  simp only [Riscv.exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr, addr_zero S b a hb hwf, loadWords_wordOf rodata S a hr]
  rfl

/-- `sb s, 0(b)`: one byte of the word. -/
theorem exec_sb_eq (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (src b : Nat) (a : Addr)
    (hh : S.halted = false) (hb : S.getGD b = gprWord a) (hwf : a.wf) (hr : a.region ≠ rRodata) :
    Riscv.exec vlmax rodata (.sb src b 0) S =
      Riscv.next { S with mem := storeByte S.mem a.region a.off (getR S src) } := by
  simp only [Riscv.exec, hh, Bool.false_eq_true, ↓reduceIte, withAddr, addr_zero S b a hb hwf, loadWords_wordOf rodata S a hr,
    storeWords_wordOf S a hr]
  rfl

/-- `addi d, s, k` on a pointer or a number. -/
theorem exec_addi_ptr (vlmax : Nat) (rodata : Array (BitVec 64)) (S : State (BitVec 64)) (d s : Nat) (k : BitVec 64)
    (a : Addr) (o : Int) (hh : S.halted = false) (hs0 : s ≠ 0) (hs : S.getGD s = gprWord a) (ho : a.off + k.toInt = o) :
    Riscv.exec vlmax rodata (.opi d s .addi k) S = Riscv.next (setR S d (gprWord ⟨a.region, o⟩)) := by
  rw [exec_opi_eq vlmax rodata S d s .addi k hh, getR_pos S s hs0, hs, ← ho]
  show Riscv.next (setR S d (gprWord a + k)) = _
  rw [gprWord_add_const]


/-! ## Straight-line concrete steps

`St T p R M`: the state `T` has the scalar kernels' control part, `pc = p`, general registers `R` and
memory `M`.  One lemma per instruction form moves it one step. -/

/-- `R` with register `d` set to `v`. -/
def upd (R : Nat → BitVec 64) (d : Nat) (v : BitVec 64) : Nat → BitVec 64 := fun r => if r = d then v else R r

structure St (T : State (BitVec 64)) (p : Nat) (R : Nat → BitVec 64) (M : Region → Int → BitVec 64) : Prop where
  ctl : Ctl0 T
  pc : T.pc = p
  regs : ∀ r, r < 32 → T.getGD r = R r
  mem : T.mem = M

theorem St.of {T : State (BitVec 64)} (h : Ctl0 T) : St T T.pc (fun r => T.getGD r) T.mem := ⟨h, rfl, fun _ _ => rfl, rfl⟩

section steps
variable {vlmax : Nat} {rodata : Array (BitVec 64)} {prog : Array Riscv.Instr} {S : State (BitVec 64)} {n p : Nat}
  {R : Nat → BitVec 64} {M : Region → Int → BitVec 64}

theorem St.next_setR {T : State (BitVec 64)} (h : St T p R M) (d : Nat) (hd : d < 32) (hd0 : d ≠ 0) (v : BitVec 64) :
    St (Riscv.next (setR T d v)) (p + 1) (upd R d v) M := by
  refine ⟨(h.ctl.setR _ _).next, by rw [Riscv.next_pc, setR_pc, h.pc], fun r hr => ?_, by rw [Riscv.next_mem, setR_mem', h.mem]⟩
  rw [Riscv.next_getGD, getGD_setR _ _ _ hd]
  unfold upd
  by_cases e : r = d
  · subst e; simp [hd0]
  · simp only [e, false_and, ↓reduceIte]; exact h.regs r hr

theorem St.step {T : State (BitVec 64)} (i : Riscv.Instr) (h : St T p R M) (hi : prog.getD p .nop = i) :
    (Riscv.isa vlmax).run rodata prog 1 T = Riscv.exec vlmax rodata i T := by
  rw [run_one vlmax rodata prog T h.ctl.halted, h.pc, hi]

/-- `ld d, off(b)` of the word `q` holding `v`. -/
theorem St.ld (h : St ((Riscv.isa vlmax).run rodata prog n S) p R M) (d b : Nat) (off : Int) (a : Addr) (q : Int)
    (v : BitVec 64) (hi : prog.getD p .nop = .ld d b off) (hd : d < 32) (hd0 : d ≠ 0) (hb : b < 32) (hR : R b = gprWord a)
    (hwf : a.wf) (hal : (a.off + off) % 8 = 0) (hr : a.region ≠ rRodata) (hq : (a.off + off) / 8 = q)
    (hv : M a.region q = v) :
    St ((Riscv.isa vlmax).run rodata prog (n + 1) S) (p + 1) (upd R d v) M := by
  rw [Isa.run_add, St.step _ h hi, Riscv.exec_ld_word vlmax rodata _ d b off a h.ctl.halted ((h.regs b hb).trans hR) hwf hal hr,
    h.mem, hq, hv]
  exact h.next_setR d hd hd0 _

/-- `sd s, off(b)` of the value `v` into word `q`. -/
theorem St.sd (h : St ((Riscv.isa vlmax).run rodata prog n S) p R M) (src b : Nat) (off : Int) (a : Addr) (q : Int)
    (v : BitVec 64) (hi : prog.getD p .nop = .sd src b off) (hs : src < 32) (hs0 : src ≠ 0) (hb : b < 32)
    (hR : R b = gprWord a) (hwf : a.wf) (hal : (a.off + off) % 8 = 0) (hr : a.region ≠ rRodata) (hq : (a.off + off) / 8 = q)
    (hv : R src = v) :
    St ((Riscv.isa vlmax).run rodata prog (n + 1) S) (p + 1) R (memStore M a.region q v) := by
  rw [Isa.run_add, St.step _ h hi, Riscv.exec_sd_word vlmax rodata _ src b off a h.ctl.halted ((h.regs b hb).trans hR) hwf hal hr,
    getR_pos _ src hs0, h.regs src hs, h.mem, hq, hv]
  exact ⟨(h.ctl.withMem _).next, by rw [Riscv.next_pc]; exact congrArg (· + 1) h.pc, fun r hr => by
    rw [Riscv.next_getGD]; exact h.regs r hr, by rw [Riscv.next_mem]⟩

/-- `addi d, s, k` on a pointer or number. -/
theorem St.addi (h : St ((Riscv.isa vlmax).run rodata prog n S) p R M) (d s : Nat) (k : BitVec 64) (a : Addr) (o : Int)
    (hi : prog.getD p .nop = .opi d s .addi k) (hd : d < 32) (hd0 : d ≠ 0) (hs : s < 32) (hs0 : s ≠ 0) (hR : R s = gprWord a)
    (ho : a.off + k.toInt = o) :
    St ((Riscv.isa vlmax).run rodata prog (n + 1) S) (p + 1) (upd R d (gprWord ⟨a.region, o⟩)) M := by
  rw [Isa.run_add, St.step _ h hi, exec_addi_ptr vlmax rodata _ d s k a o h.ctl.halted hs0 ((h.regs s hs).trans hR) ho]
  exact h.next_setR d hd hd0 _

theorem andi7_gprWord (a : Addr) : gprWord a &&& 7#64 = gprWord ⟨0, a.off % 8⟩ := by
  rw [gprWord_low3]
  show BitVec.ofInt 64 a.off &&& 7#64 = BitVec.ofInt 64 (a.off % 8)
  obtain ⟨k, hk8, hk⟩ : ∃ k : Nat, k < 8 ∧ a.off % 8 = k := ⟨(a.off % 8).toNat, by omega, by omega⟩
  have e : a.off = 8 * (a.off / 8) + (k : Int) := by omega
  rw [hk, e, BitVec.ofInt_add, BitVec.ofInt_mul]
  generalize BitVec.ofInt 64 (a.off / 8) = x
  have h8 : BitVec.ofInt 64 8 = 8#64 := rfl
  rw [h8]
  rcases cases8 k hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> bv_decide

/-- `andi d, s, 7` (the alignment test). -/
theorem St.andi7 (h : St ((Riscv.isa vlmax).run rodata prog n S) p R M) (d s : Nat) (a : Addr)
    (hi : prog.getD p .nop = .opi d s .andi 7#64) (hd : d < 32) (hd0 : d ≠ 0) (hs : s < 32) (hs0 : s ≠ 0) (hR : R s = gprWord a) :
    St ((Riscv.isa vlmax).run rodata prog (n + 1) S) (p + 1) (upd R d (gprWord ⟨0, a.off % 8⟩)) M := by
  rw [Isa.run_add, St.step _ h hi, exec_opi_eq vlmax rodata _ d s .andi 7#64 h.ctl.halted, getR_pos _ s hs0,
    h.regs s hs, hR]
  show St (Riscv.next (setR _ d (gprWord a &&& 7#64))) _ _ _
  rw [andi7_gprWord]
  exact h.next_setR d hd hd0 _

/-- `mv d, s`. -/
theorem St.mv (h : St ((Riscv.isa vlmax).run rodata prog n S) p R M) (d s : Nat)
    (hi : prog.getD p .nop = .mv d s) (hd : d < 32) (hd0 : d ≠ 0) (hs : s < 32) (hs0 : s ≠ 0) :
    St ((Riscv.isa vlmax).run rodata prog (n + 1) S) (p + 1) (upd R d (R s)) M := by
  rw [Isa.run_add, St.step _ h hi, Riscv.exec_mv_eq vlmax rodata _ d s h.ctl.halted, getR_pos _ s hs0, h.regs s hs]
  exact h.next_setR d hd hd0 _

/-- `li d, imm`. -/
theorem St.li (h : St ((Riscv.isa vlmax).run rodata prog n S) p R M) (d : Nat) (imm : BitVec 64)
    (hi : prog.getD p .nop = .li d imm) (hd : d < 32) (hd0 : d ≠ 0) :
    St ((Riscv.isa vlmax).run rodata prog (n + 1) S) (p + 1) (upd R d imm) M := by
  rw [Isa.run_add, St.step _ h hi, Riscv.exec_li_eq vlmax rodata _ d imm h.ctl.halted]
  exact h.next_setR d hd hd0 _

/-- A branch on a number register against `zero`. -/
theorem St.brz (h : St ((Riscv.isa vlmax).run rodata prog n S) p R M) (c : Riscv.BCond) (a t : Nat) (x : Int)
    (hi : prog.getD p .nop = .br c a 0 t) (ha : a < 32) (ha0 : a ≠ 0) (hR : R a = gprWord ⟨0, x⟩) (hx : (⟨0, x⟩ : Addr).wf) :
    St ((Riscv.isa vlmax).run rodata prog (n + 1) S) (if Riscv.brHolds c x 0 then t else p + 1) R M := by
  rw [Isa.run_add, St.step _ h hi, exec_br_num vlmax rodata _ c a 0 t x 0 h.ctl.halted
    ((getR_pos _ a ha0).trans ((h.regs a ha).trans hR)) (getR_zero _) hx ⟨by decide, by decide⟩, h.pc]
  exact ⟨h.ctl.withPc _, rfl, h.regs, h.mem⟩

/-- `j t`. -/
theorem St.j (h : St ((Riscv.isa vlmax).run rodata prog n S) p R M) (t : Nat) (hi : prog.getD p .nop = .j t) :
    St ((Riscv.isa vlmax).run rodata prog (n + 1) S) t R M := by
  rw [Isa.run_add, St.step _ h hi, Riscv.exec_j_eq vlmax rodata _ t h.ctl.halted]
  exact ⟨h.ctl.withPc _, rfl, h.regs, h.mem⟩

end steps

/-! ## The byte-copy loop -/

/-- The state of the copy loop after `i` of its `n` iterations (from `S`). -/
structure CopyAt (S : State (BitVec 64)) (src dst tmp cnt : Nat) (rs rd : Region) (os od : Int) (n i : Nat)
    (T : State (BitVec 64)) : Prop where
  ctl : Ctl0 T
  rsrc : T.getGD src = gprWord ⟨rs, os + i⟩
  rdst : T.getGD dst = gprWord ⟨rd, od + i⟩
  rcnt : T.getGD cnt = gprWord ⟨0, (n : Int) - i⟩
  regs : ∀ r, r ≠ src → r ≠ dst → r ≠ tmp → r ≠ cnt → T.getGD r = S.getGD r
  bytes : ∀ r b, byteAt (T.mem r) b = if r = rd ∧ od ≤ b ∧ b < od + i then byteAt (S.mem rs) (os + (b - od)) else byteAt (S.mem r) b

/-- The instructions of the loop at `L`. -/
def CopyCode (prog : Array Riscv.Instr) (L src dst tmp cnt : Nat) : Prop :=
  prog.getD L .nop = .lbu tmp src 0 ∧ prog.getD (L + 1) .nop = .sb tmp dst 0 ∧
  prog.getD (L + 2) .nop = .opi src src .addi 1#64 ∧ prog.getD (L + 3) .nop = .opi dst dst .addi 1#64 ∧
  prog.getD (L + 4) .nop = .opi cnt cnt .addi 0xffffffffffffffff#64 ∧ prog.getD (L + 5) .nop = .br .ne cnt 0 L

/-- The registers of the loop: distinct, non-zero. -/
def CopyRegs (src dst tmp cnt : Nat) : Prop :=
  src < 32 ∧ dst < 32 ∧ tmp < 32 ∧ cnt < 32 ∧ src ≠ 0 ∧ dst ≠ 0 ∧ tmp ≠ 0 ∧ cnt ≠ 0 ∧
  src ≠ dst ∧ src ≠ tmp ∧ src ≠ cnt ∧ dst ≠ tmp ∧ dst ≠ cnt ∧ tmp ≠ cnt

set_option maxHeartbeats 4000000 in
/-- **One iteration of the copy loop.** -/
theorem copy_step (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (L src dst tmp cnt : Nat)
    (hcode : CopyCode prog L src dst tmp cnt) (hregs : CopyRegs src dst tmp cnt)
    (rs rd : Region) (os od : Int) (hrsd : rs ≠ rd) (hrs : rs ≠ rRodata) (hrd : rd ≠ rRodata) (hrs0 : rs ≠ 0) (hrd0 : rd ≠ 0)
    (n : Nat) (hos : 0 ≤ os) (hod : 0 ≤ od) (hosn : os + n < 2 ^ 55) (hodn : od + n < 2 ^ 55) (hn : n < 2 ^ 55)
    (S : State (BitVec 64)) (i : Nat) (hi : i < n) (T : State (BitVec 64)) (hT : CopyAt S src dst tmp cnt rs rd os od n i T)
    (hpc : T.pc = L) :
    CopyAt S src dst tmp cnt rs rd os od n (i + 1) ((Riscv.isa vlmax).run rodata prog 6 T) ∧
      ((Riscv.isa vlmax).run rodata prog 6 T).pc = if i + 1 < n then L else L + 6 := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hcode
  obtain ⟨s32, d32, t32, n32, s0, d0, t0, n0, sd, st, sn, dt, dn, tn⟩ := hregs
  have hh := hT.ctl.halted
  have wsrc : (⟨rs, os + i⟩ : Addr).wf := ⟨show 0 ≤ os + (i : Int) by omega, show os + (i : Int) < 2 ^ 55 by omega⟩
  have wdst : (⟨rd, od + i⟩ : Addr).wf := ⟨show 0 ≤ od + (i : Int) by omega, show od + (i : Int) < 2 ^ 55 by omega⟩
  -- lbu
  generalize hx : (T.mem rs ((os + i) / 8) >>> (8 * ((os + i) % 8).toNat)) &&& 0xff#64 = x
  have e1 : (Riscv.isa vlmax).run rodata prog 1 T = Riscv.next (setR T tmp x) := by
    rw [run_one vlmax rodata prog T hh, show prog.getD T.pc .nop = .lbu tmp src 0 by rw [hpc]; exact c0, exec_lbu_eq vlmax rodata T tmp src ⟨rs, os + i⟩ hh hT.rsrc wsrc hrs, hx]
  generalize hT1 : Riscv.next (setR T tmp x) = T1 at e1
  have k1 : Ctl0 T1 := by rw [← hT1]; exact (hT.ctl.setR _ _).next
  have p1 : T1.pc = L + 1 := by rw [← hT1, Riscv.next_pc, setR_pc, hpc]
  have g1 : ∀ r, T1.getGD r = if r = tmp then x else T.getGD r := by
    intro r; rw [← hT1, Riscv.next_getGD, getGD_setR _ _ _ t32]; simp [t0]
  have m1 : T1.mem = T.mem := by rw [← hT1, Riscv.next_mem, setR_mem']
  -- sb
  have e2 : (Riscv.isa vlmax).run rodata prog 1 T1 = Riscv.next { T1 with mem := storeByte T1.mem rd (od + i) x } := by
    have hd : T1.getGD dst = gprWord ⟨rd, od + i⟩ := by rw [g1, if_neg dt]; exact hT.rdst
    rw [run_one vlmax rodata prog T1 k1.halted, show prog.getD T1.pc .nop = .sb tmp dst 0 by rw [p1]; exact c1, exec_sb_eq vlmax rodata T1 tmp dst ⟨rd, od + i⟩ k1.halted hd wdst hrd,
      getR_pos T1 tmp t0, g1, if_pos rfl]
  generalize hT2 : Riscv.next { T1 with mem := storeByte T1.mem rd (od + i) x } = T2 at e2
  have k2 : Ctl0 T2 := by rw [← hT2]; exact (k1.withMem _).next
  have p2 : T2.pc = L + 2 := by rw [← hT2, Riscv.next_pc]; show T1.pc + 1 = _; rw [p1]
  have g2 : ∀ r, T2.getGD r = T1.getGD r := by intro r; rw [← hT2, Riscv.next_getGD]; rfl
  have m2 : T2.mem = storeByte T.mem rd (od + i) x := by rw [← hT2, Riscv.next_mem, m1]
  -- addi src
  have e3 : (Riscv.isa vlmax).run rodata prog 1 T2 = Riscv.next (setR T2 src (gprWord ⟨rs, os + (i + 1 : Nat)⟩)) := by
    have hs : T2.getGD src = gprWord ⟨rs, os + i⟩ := by rw [g2, g1, if_neg st]; exact hT.rsrc
    rw [run_one vlmax rodata prog T2 k2.halted, show prog.getD T2.pc .nop = .opi src src .addi 1#64 by rw [p2]; exact c2, exec_addi_ptr vlmax rodata T2 src src 1#64 ⟨rs, os + i⟩ (os + ((i + 1 : Nat) : Int)) k2.halted s0 hs
      (by rw [show (1#64).toInt = 1 by decide]; push_cast; omega)]
  generalize hT3 : Riscv.next (setR T2 src (gprWord ⟨rs, os + (i + 1 : Nat)⟩)) = T3 at e3
  have k3 : Ctl0 T3 := by rw [← hT3]; exact (k2.setR _ _).next
  have p3 : T3.pc = L + 3 := by rw [← hT3, Riscv.next_pc, setR_pc, p2]
  have g3 : ∀ r, T3.getGD r = if r = src then gprWord ⟨rs, os + (i + 1 : Nat)⟩ else T2.getGD r := by
    intro r; rw [← hT3, Riscv.next_getGD, getGD_setR _ _ _ s32]; simp [s0]
  have m3 : T3.mem = T2.mem := by rw [← hT3, Riscv.next_mem, setR_mem']
  -- addi dst
  have e4 : (Riscv.isa vlmax).run rodata prog 1 T3 = Riscv.next (setR T3 dst (gprWord ⟨rd, od + (i + 1 : Nat)⟩)) := by
    have hs : T3.getGD dst = gprWord ⟨rd, od + i⟩ := by
      rw [g3, if_neg (Ne.symm sd), g2, g1, if_neg dt]; exact hT.rdst
    rw [run_one vlmax rodata prog T3 k3.halted, show prog.getD T3.pc .nop = .opi dst dst .addi 1#64 by rw [p3]; exact c3, exec_addi_ptr vlmax rodata T3 dst dst 1#64 ⟨rd, od + i⟩ (od + ((i + 1 : Nat) : Int)) k3.halted d0 hs
      (by rw [show (1#64).toInt = 1 by decide]; push_cast; omega)]
  generalize hT4 : Riscv.next (setR T3 dst (gprWord ⟨rd, od + (i + 1 : Nat)⟩)) = T4 at e4
  have k4 : Ctl0 T4 := by rw [← hT4]; exact (k3.setR _ _).next
  have p4 : T4.pc = L + 4 := by rw [← hT4, Riscv.next_pc, setR_pc, p3]
  have g4 : ∀ r, T4.getGD r = if r = dst then gprWord ⟨rd, od + (i + 1 : Nat)⟩ else T3.getGD r := by
    intro r; rw [← hT4, Riscv.next_getGD, getGD_setR _ _ _ d32]; simp [d0]
  have m4 : T4.mem = T3.mem := by rw [← hT4, Riscv.next_mem, setR_mem']
  -- addi cnt, -1
  have e5 : (Riscv.isa vlmax).run rodata prog 1 T4 = Riscv.next (setR T4 cnt (gprWord ⟨0, (n : Int) - (i + 1 : Nat)⟩)) := by
    have hs : T4.getGD cnt = gprWord ⟨0, (n : Int) - i⟩ := by
      rw [g4, if_neg (Ne.symm dn), g3, if_neg (Ne.symm sn), g2, g1, if_neg (Ne.symm tn)]; exact hT.rcnt
    rw [run_one vlmax rodata prog T4 k4.halted, show prog.getD T4.pc .nop = .opi cnt cnt .addi 0xffffffffffffffff#64 by rw [p4]; exact c4, exec_addi_ptr vlmax rodata T4 cnt cnt 0xffffffffffffffff#64 ⟨0, (n : Int) - i⟩ ((n : Int) - ((i + 1 : Nat) : Int)) k4.halted n0 hs
      (by rw [show (0xffffffffffffffff#64).toInt = -1 by decide]; push_cast; omega)]
  generalize hT5 : Riscv.next (setR T4 cnt (gprWord ⟨0, (n : Int) - (i + 1 : Nat)⟩)) = T5 at e5
  have k5 : Ctl0 T5 := by rw [← hT5]; exact (k4.setR _ _).next
  have p5 : T5.pc = L + 5 := by rw [← hT5, Riscv.next_pc, setR_pc, p4]
  have g5 : ∀ r, T5.getGD r = if r = cnt then gprWord ⟨0, (n : Int) - (i + 1 : Nat)⟩ else T4.getGD r := by
    intro r; rw [← hT5, Riscv.next_getGD, getGD_setR _ _ _ n32]; simp [n0]
  have m5 : T5.mem = T4.mem := by rw [← hT5, Riscv.next_mem, setR_mem']
  -- bne cnt, zero, L
  have e6 : (Riscv.isa vlmax).run rodata prog 1 T5 =
      { T5 with pc := if Riscv.brHolds .ne ((n : Int) - (i + 1 : Nat)) 0 then L else T5.pc + 1 } := by
    have hc : getR T5 cnt = gprWord ⟨0, (n : Int) - (i + 1 : Nat)⟩ := by rw [getR_pos T5 cnt n0, g5, if_pos rfl]
    rw [run_one vlmax rodata prog T5 k5.halted, show prog.getD T5.pc .nop = .br .ne cnt 0 L by rw [p5]; exact c5,
      exec_br_num vlmax rodata T5 .ne cnt 0 L _ 0 k5.halted hc (getR_zero T5)
        ⟨show (0 : Int) ≤ (n : Int) - ((i + 1 : Nat) : Int) by omega, show (n : Int) - ((i + 1 : Nat) : Int) < 2 ^ 55 by omega⟩
        ⟨show (0 : Int) ≤ 0 by decide, show (0 : Int) < 2 ^ 55 by decide⟩]
  have hrun : (Riscv.isa vlmax).run rodata prog 6 T =
      { T5 with pc := if Riscv.brHolds .ne ((n : Int) - (i + 1 : Nat)) 0 then L else L + 5 + 1 } := by
    rw [show 6 = 1 + 1 + 1 + 1 + 1 + 1 from rfl, Isa.run_add, Isa.run_add, Isa.run_add, Isa.run_add, Isa.run_add,
      e1, e2, e3, e4, e5, e6, p5]
  rw [hrun]
  have hcnd : (if Riscv.brHolds .ne ((n : Int) - ((i + 1 : Nat) : Int)) 0 then L else L + 5 + 1) =
      if i + 1 < n then L else L + 6 := by
    by_cases h : i + 1 < n
    · have hb : Riscv.brHolds .ne ((n : Int) - ((i + 1 : Nat) : Int)) 0 = true := by
        simp only [Riscv.brHolds, bne_iff_ne, ne_eq]; omega
      rw [hb, if_pos rfl, if_pos h]
    · have hb : Riscv.brHolds .ne ((n : Int) - ((i + 1 : Nat) : Int)) 0 = false := by
        simp only [Riscv.brHolds, bne_eq_false_iff_eq]; omega
      rw [hb, if_neg (by decide), if_neg h]
  refine ⟨⟨k5.withPc _, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show T5.getGD src = _
    rw [g5, if_neg sn, g4, if_neg sd, g3, if_pos rfl]
  · show T5.getGD dst = _
    rw [g5, if_neg dn, g4, if_pos rfl]
  · show T5.getGD cnt = _
    rw [g5, if_pos rfl]
  · intro r h1 h2 h3 h4
    show T5.getGD r = _
    rw [g5, if_neg h4, g4, if_neg h2, g3, if_neg h1, g2, g1, if_neg h3]
    exact hT.regs r h1 h2 h3 h4
  · intro r b
    show byteAt (T5.mem r) b = _
    rw [m5, m4, m3, m2, byteAt_storeByte]
    -- the loaded byte
    have hxb : x.extractLsb' 0 8 = byteAt (S.mem rs) (os + i) := by
      rw [← hx, lbu_byte _ _ (by omega)]
      have := hT.bytes rs (os + i)
      simp only [show ¬ (rs = rd) from hrsd, false_and, ↓reduceIte] at this
      exact this
    by_cases hb : r = rd ∧ b = od + i
    · obtain ⟨rfl, rfl⟩ := hb
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, by omega, by push_cast; omega⟩, hxb]
      exact congrArg _ (by omega)
    · rw [if_neg hb, hT.bytes r b]
      by_cases hr : r = rd
      · subst hr
        have e : (od ≤ b ∧ b < od + (i : Int)) ↔ (od ≤ b ∧ b < od + ((i + 1 : Nat) : Int)) := by
          have : b ≠ od + i := fun h => hb ⟨rfl, h⟩
          push_cast; omega
        by_cases h1 : od ≤ b ∧ b < od + (i : Int)
        · rw [if_pos ⟨rfl, h1⟩, if_pos ⟨rfl, e.mp h1⟩]
        · rw [if_neg (fun h => h1 h.2), if_neg (fun h => h1 (e.mpr h.2))]
      · rw [if_neg (fun h => hr h.1), if_neg (fun h => hr h.1)]
  · show (if Riscv.brHolds .ne ((n : Int) - ((i + 1 : Nat) : Int)) 0 then L else L + 5 + 1) = _
    exact hcnd

theorem CopyAt.word_other {S T : State (BitVec 64)} {src dst tmp cnt : Nat} {rs rd : Region} {os od : Int} {n i : Nat}
    (hT : CopyAt S src dst tmp cnt rs rd os od n i T) (r : Region) (q : Int)
    (h : r ≠ rd ∨ 8 * q + 8 ≤ od ∨ od + i ≤ 8 * q) : T.mem r q = S.mem r q := by
  apply word_ext
  intro j hj
  rw [← byteAt_word _ q j hj, ← byteAt_word _ q j hj, hT.bytes, if_neg]
  rintro ⟨h1, h2, h3⟩
  rcases h with h | h | h
  · exact h h1
  · omega
  · omega

theorem CopyAt.word_copy {S T : State (BitVec 64)} {src dst tmp cnt : Nat} {rs rd : Region} {os od : Int} {n i : Nat}
    (hT : CopyAt S src dst tmp cnt rs rd os od n i T) (q : Int) (h1 : od ≤ 8 * q) (h2 : 8 * q + 8 ≤ od + i) :
    T.mem rd q = wordAt (S.mem rs) (os + (8 * q - od)) := by
  apply word_of_bytes
  intro j hj
  rw [hT.bytes, if_pos ⟨rfl, by omega, by omega⟩]
  exact congrArg _ (by omega)

/-- The copy as straight-line steps: the state after the loop. -/
theorem CopyAt.st {S T : State (BitVec 64)} {src dst tmp cnt : Nat} {rs rd : Region} {os od : Int} {n i : Nat}
    (hT : CopyAt S src dst tmp cnt rs rd os od n i T) (p : Nat) (hp : T.pc = p) :
    St T p (fun r => T.getGD r) T.mem := ⟨hT.ctl, hp, fun _ _ => rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **The byte-copy loop**: from the loop head with the source at byte `os` of region `rs`, the
destination at byte `od` of region `rd` and the count `n ≥ 1`, `6 n` steps copy the `n` bytes and
leave the loop; every other byte and register is kept. -/
theorem copy_loop (vlmax : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (L src dst tmp cnt : Nat)
    (hcode : CopyCode prog L src dst tmp cnt) (hregs : CopyRegs src dst tmp cnt)
    (rs rd : Region) (os od : Int) (hrsd : rs ≠ rd) (hrs : rs ≠ rRodata) (hrd : rd ≠ rRodata) (hrs0 : rs ≠ 0) (hrd0 : rd ≠ 0)
    (n : Nat) (hn1 : 1 ≤ n) (hos : 0 ≤ os) (hod : 0 ≤ od) (hosn : os + n < 2 ^ 55) (hodn : od + n < 2 ^ 55) (hn : n < 2 ^ 55)
    (S : State (BitVec 64)) (hc : Ctl0 S) (hpc : S.pc = L) (hsrc : S.getGD src = gprWord ⟨rs, os⟩)
    (hdst : S.getGD dst = gprWord ⟨rd, od⟩) (hcnt : S.getGD cnt = gprWord ⟨0, n⟩) :
    CopyAt S src dst tmp cnt rs rd os od n n ((Riscv.isa vlmax).run rodata prog (6 * n) S) ∧
      ((Riscv.isa vlmax).run rodata prog (6 * n) S).pc = L + 6 := by
  have h0 : CopyAt S src dst tmp cnt rs rd os od n 0 S := by
    refine ⟨hc, by simpa using hsrc, by simpa using hdst, by simpa using hcnt, fun r _ _ _ _ => rfl, ?_⟩
    intro r b
    have : ¬ (r = rd ∧ od ≤ b ∧ b < od + ((0 : Nat) : Int)) := by intro h; push_cast at h; omega
    rw [if_neg this]
  have key : ∀ i, i < n → CopyAt S src dst tmp cnt rs rd os od n (i + 1) ((Riscv.isa vlmax).run rodata prog (6 * (i + 1)) S) ∧
      ((Riscv.isa vlmax).run rodata prog (6 * (i + 1)) S).pc = if i + 1 < n then L else L + 6 := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [show 6 * (0 + 1) = 6 from rfl]
      exact copy_step vlmax rodata prog L src dst tmp cnt hcode hregs rs rd os od hrsd hrs hrd hrs0 hrd0 n hos hod hosn hodn hn
        S 0 hi S h0 hpc
    | succ i ih =>
      intro hi
      obtain ⟨hT, hp⟩ := ih (by omega)
      rw [if_pos (by omega)] at hp
      have := copy_step vlmax rodata prog L src dst tmp cnt hcode hregs rs rd os od hrsd hrs hrd hrs0 hrd0 n hos hod hosn hodn hn
        S (i + 1) hi _ hT hp
      rw [show 6 * (i + 1 + 1) = 6 * (i + 1) + 6 by omega, Isa.run_add]
      exact this
  obtain ⟨hT, hp⟩ := key (n - 1) (by omega)
  have e : n - 1 + 1 = n := by omega
  rw [e] at hT hp
  rw [if_neg (Nat.lt_irrefl n)] at hp
  exact ⟨hT, hp⟩

end Keccaktree.Kernels.RiscvBytes
