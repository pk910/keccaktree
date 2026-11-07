import Keccaktree.Asm.Library
import Keccaktree.Asm.EntryCtl
import Keccaktree.Asm.Node
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The x86-64 kernels as a library

The calling convention shared by every x86 kernel (`Entry`: `rdx = count`,
`rsp` at the top of the stack region, `rsi`/`rdi` at node `off` of the input/
output regions, the input region holding the message), the digest predicate,
and `EntryX86`: the entry state *with any flags, mask registers and vector
length* — what a direct call or a tail call from another kernel leaves behind.

`mkKernel` turns a kernel's generated all-count theorem, proved from the
normalised control state (`NormThm`), into a `Library.KernelThm` for
`EntryX86`, given two kernel-checked facts about the program: the entry
prefix writes the flags before reading them (`prefixOk`), and no instruction
reads or writes the mask registers, `nf`/`vf` or `vl` (`static`).  (Kernels
with AVX-512 masks use `run_ovr_path` on their segment paths instead.)
-/
namespace Keccaktree.Asm.LibX86
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Proof Keccak

/-- The entry state of a call `keccaktree_keccak256_<kernel>(out, in, count)` at node offset `off`,
with the control part of a fresh call (no constraint on `pc`: the library sets it to the kernel's
entry).  The vector registers, the other general registers and every other memory word are
arbitrary. -/
structure Entry (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.vl = 0 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  rdx : S.getGD 2 = gprWord ⟨0, count⟩
  rsp : S.getGD 4 = gprWord ⟨rStack, 1048576⟩
  rsi : S.getGD 6 = gprWord ⟨rInput, 64 * off⟩
  rdi : S.getGD 7 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

theorem Entry.with_pc {off count : Nat} {input : Int → BitVec 64} {S : State (BitVec 64)} (h : Entry off count input S)
    (p : Nat) : Entry off count input { S with pc := p } :=
  ⟨h.ctrl, h.ok, h.rdx, h.rsp, h.rsi, h.rdi, h.inp⟩

/-- The words of node `n` of the message. -/
def nodeWords (input : Int → BitVec 64) (n : Nat) (w : Nat) : BitVec 64 := input (Int.ofNat (8 * n + w))

/-- Output words `4n..4n+3` hold the keccak256 digest of input node `n`. -/
def Digest (input : Int → BitVec 64) (S : State (BitVec 64)) (n : Nat) : Prop :=
  ∀ w i : Nat, w < 4 → i < 8 →
    (S.mem rOutput (Int.ofNat (4 * n + w))).extractLsb' (8 * i) 8 = Spec.keccak256 64 (nodeBytes (nodeWords input n)) (8 * w + i)

theorem digest_local : Library.DigestLocal Digest := by
  intro input S S' n h hd w i hw hi
  rw [h (Int.ofNat (4 * n + w)) (by simp only [Int.ofNat_eq_coe]; omega) (by simp only [Int.ofNat_eq_coe]; omega)]
  exact hd w i hw hi

/-- **The x86 calling convention of the library**: the entry state at node offset `off` (within the
address bound), with any flags, mask registers and vector length. -/
def EntryX86 (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  Entry off count input (normCtl S) ∧ 64 * (off + count) ≤ 2 ^ 54

theorem normCtl_ovr_upd (D : Dom) (c : Ctl) (X : State (BitVec 64)) :
    normCtl { ovr D c X with halted := false, tail := none } = normCtl { X with halted := false, tail := none } := by
  simp only [normCtl, ovr, Dom.all, Bool.cond_true, State.mk.injEq, and_true, true_and]
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  have : [0, 1, 2, 3, 4, 5, 6, 7].contains i = true := by
    simp only [List.contains_iff_mem]; simp; omega
  rw [this]; rfl

/-- The outcome is insensitive to leftover control components of the final state. -/
theorem outcome_ovr (targets : List String) (off count : Nat) (input : Int → BitVec 64) (S S' X : State (BitVec 64))
    (D : Dom) (c : Ctl) (hmem : S'.mem = S.mem)
    (h : Library.Outcome EntryX86 Digest targets off count input S X) :
    Library.Outcome EntryX86 Digest targets off count input S' (ovr D c X) := by
  obtain ⟨hh, he, hp, hout⟩ := h
  refine ⟨hh, he, fun q hq => (hp q hq).trans (by rw [hmem]), ?_⟩
  rcases hout with ⟨ht, hd⟩ | ⟨next, done, ht, hmemb, hdone, hd, hnext⟩
  · exact Or.inl ⟨ht, hd⟩
  · refine Or.inr ⟨next, done, ht, hmemb, hdone, hd, ?_⟩
    unfold EntryX86 at hnext ⊢
    rw [normCtl_ovr_upd]; exact hnext

/-- What a kernel's generated all-count proof provides: from a normalised entry state at the
kernel's entry instruction, `steps off count` steps reach the `Outcome`. -/
def NormThm (rodata : Array (BitVec 64)) (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (targets : List String) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    Entry off count input S → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    Library.Outcome EntryX86 Digest targets off count input S (X86.isa.run rodata prog (steps off count) S)

/-- The dirty set after the entry prefix: everything but the flags. -/
abbrev Dom1 : Dom := { Dom.all with zf := false, cf := false }

/-- **An x86 kernel of the library** from its normalised all-count theorem: the entry prefix of `m`
instructions writes the flags before any read (`hpre`), and no instruction touches the other
control components (`hstatic`); both are decided by the kernel on the program. -/
def mkKernel (name : String) (rank : Nat) (targets : List String) (rodata : Array (BitVec 64))
    (prog : Array Instr) (entry : Nat) (steps : Nat → Nat → Nat) (m : Nat)
    (hpre : prefixOk prog entry 1048576 m = true)
    (hstatic : (prog.all fun i => ctlOk Dom1 i && ctlAfter Dom1 i == Dom1) = true)
    (hm : ∀ off count, m ≤ steps off count)
    (h : NormThm rodata prog entry steps targets) : Library.KernelThm X86.isa EntryX86 Digest where
  name := name
  rank := rank
  targets := targets
  rodata := rodata
  prog := prog
  entry := entry
  steps := steps
  thm := fun off count input S hS => by
    obtain ⟨hE, hb⟩ := hS
    have h0 := h off count input { normCtl S with pc := entry } (hE.with_pc entry) hb rfl
    have hrun := run_normCtl rodata prog m 1048576 (steps off count) { S with pc := entry } hpre hstatic
      (hm off count) hE.ok.2.1 hE.rsp (by decide) h0.2.1
    rw [hrun]
    exact outcome_ovr targets off count input _ _ _ _ _ rfl h0

end Keccaktree.Asm.LibX86
