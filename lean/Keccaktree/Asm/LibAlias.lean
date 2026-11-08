import Keccaktree.Asm.LibX86
import Keccaktree.Asm.Alias
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# In-place hashing for an x86 kernel (`out == in`)

`inplace_lift` turns a kernel's all-count theorem for separate input and output buffers
(`LibX86.NormThm`) into the same statement for the aliased machine (`X86.runAl`: one storage, the
output pointer addressing it at the same offsets as the input pointer), under one condition on the
separate-region run: `AccessRun` — every input word it loads is at or above the current bound `B`
(above every output word stored so far), and it stores no input word.  The aliased run starts from
`T`; the separate-region run starts from `dupState T` (its output region a copy of the storage), so
`Entry` for `dupState T` is the calling convention of `keccaktree_hash(buf, buf, count)`.

The digests end up in the storage (`DigestAl`); the earlier storage words are kept; a tail call hands
the remaining nodes over in place, the storage above the final bound `Bf` still holding the message.
-/
namespace Keccaktree.Asm.LibAlias
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86

/-- What an in-place kernel call achieves (digests in the buffer, read through either view). -/
def OutcomeAl (targets : List String) (Bf : Int) (off count : Nat) (input : Int → BitVec 64) (T Tf : State (BitVec 64)) : Prop :=
  Tf.halted = true ∧ Tf.err = false ∧ Mirror Tf ∧
  (∀ q : Int, q < 4 * off → Tf.mem rOutput q = T.mem rOutput q) ∧
  (∀ q : Int, Bf ≤ q → Tf.mem rInput q = T.mem rInput q) ∧
  ((Tf.tail = none ∧ ∀ n, n < count → Digest input Tf (off + n)) ∨
   ∃ (next : String) (done : Nat), Tf.tail = some next ∧ next ∈ targets ∧ done ≤ count ∧
     (∀ n, n < done → Digest input Tf (off + n)) ∧
     EntryX86 next (off + done) (count - done) (fun q => Tf.mem rInput q)
       (dupState { Tf with halted := false, tail := none }))

theorem entry_transfer (off count : Nat) (input input' : Int → BitVec 64) (S S' : State (BitVec 64))
    (hE : Entry off count input S) (hS' : S' = { S with mem := S'.mem }) (hin : ∀ q, S'.mem rInput q = input' q) :
    Entry off count input' S' := by
  rw [hS']
  exact ⟨hE.ctrl, hE.ok, hE.rdx, hE.rsp, hE.rsi, hE.rdi, hin⟩

/-- **The in-place lifting.** -/
theorem inplace_lift (rodata : Array (BitVec 64)) (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (targets : List String) (h : NormThm rodata prog entry steps targets)
    (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64)) (hm : Mirror T)
    (hE : Entry off count input (dupState T)) (hb : 64 * (off + count) ≤ 2 ^ 54) (hpc : T.pc = entry)
    (B0 Bf : Int) (hacc : AccessRun rodata prog (steps off count) B0 Bf (dupState T)) :
    OutcomeAl targets Bf off count input T (runAl rodata prog (steps off count) T) := by
  have hO := h off count input (dupState T) hE hb hpc
  obtain ⟨hS, hC, hIn⟩ := sim_run rodata prog _ B0 Bf (dupState T) T hacc (sim_dup T hm) (clean_dup T B0)
  generalize hSf : X86.isa.run rodata prog (steps off count) (dupState T) = Sf at hO hS hC hIn
  generalize hTf : runAl rodata prog (steps off count) T = Tf at hS
  obtain ⟨hh, he, hpre, hout⟩ := hO
  have hmIn : ∀ q, Tf.mem rInput q = Sf.mem rOutput q := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmOut : ∀ q, Tf.mem rOutput q = Sf.mem rOutput q := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdig : ∀ n, Digest input Sf n → Digest input Tf n := by
    intro n hd w i hw hi
    rw [hmOut]; exact hd w i hw hi
  refine ⟨hS.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hh, hS.2.2.2.2.2.2.2.2.2.2.2.1.trans he,
    fun q => (hmOut q).trans (hmIn q).symm, ?_, ?_, ?_⟩
  · intro q hq
    rw [hmOut, hpre q hq]; simp only [dupState, ↓reduceIte]; exact (hm q).symm
  · intro q hq
    rw [hmIn, hC q hq, hIn q]; simp [dupState, show rInput ≠ rOutput by decide]
  · rcases hout with ⟨ht, hd⟩ | ⟨next, done, ht, hmem, hdone, hd, hnext⟩
    · exact Or.inl ⟨hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans ht, fun n hn => hdig _ (hd n hn)⟩
    · refine Or.inr ⟨next, done, hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans ht, hmem, hdone, fun n hn => hdig _ (hd n hn), ?_⟩
      obtain ⟨hEn, hbn⟩ := hnext
      refine ⟨entry_transfer _ _ input _ _ _ hEn ?_ (fun q => ?_), hbn⟩
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -⟩ := hS
        cases Tf; cases Sf
        simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
        subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
        rfl
      · simp only [normCtl, ovr, dupState, show rInput ≠ rOutput by decide, ↓reduceIte]

end Keccaktree.Asm.LibAlias
