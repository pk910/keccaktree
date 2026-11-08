import Keccaktree.Asm.RiscvChoice
import Keccaktree.Kernels.RiscvBytes
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The RISC-V library with misaligned buffers

The library layer of `LibRv` / `LibTable` (`EntryR`, `EntryRv`, `NormThmRv`, `mkKernelRv`, `lib_rv`) for
buffers at any byte offset: the input buffer at byte `mi + 64·off` and the output buffer at byte
`mo + 32·off` of their regions (`mi, mo < 8`: the machine address of the buffer modulo 8), the digest
at a byte offset (`RiscvBytes.DigestB mi mo`).  New definitions only; with `mi = mo = 0` they are the
aligned ones (`RiscvBytes.digestB_zero`).

The RISC-V kernels hand nothing over (`rvShape`: no tail calls), so the library theorem for a table
of this shape follows from each kernel's theorem directly (`libOk_of_stop`; no locality of the digest
predicate is needed — a misaligned digest spans 5 output words).
-/
namespace Keccaktree.Kernels.LibRvU
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Keccaktree.Asm.LibTable Keccaktree.Kernels.RiscvBytes

/-- The RISC-V entry state with misaligned buffers (`EntryR` with `a1 = mi + 64·off`, `a0 = mo + 32·off`). -/
structure EntryRU (mi mo off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.vl = 0 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  a2 : S.getGD 12 = gprWord ⟨0, count⟩
  sp : S.getGD 2 = gprWord ⟨rStack, 1048576⟩
  a1 : S.getGD 11 = gprWord ⟨rInput, mi + 64 * off⟩
  a0 : S.getGD 10 = gprWord ⟨rOutput, mo + 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

theorem EntryRU.with_pc {mi mo off count : Nat} {input : Int → BitVec 64} {S : State (BitVec 64)}
    (h : EntryRU mi mo off count input S) (p : Nat) : EntryRU mi mo off count input { S with pc := p } :=
  ⟨h.ctrl, h.ok, h.a2, h.sp, h.a1, h.a0, h.inp⟩

/-- The calling convention of the misaligned library: any vector length at entry. -/
def EntryRvU (mi mo : Nat) (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  EntryRU mi mo off count input (normCtl S) ∧ 64 * (off + count) ≤ 2 ^ 54

/-- What a RISC-V kernel's all-count proof at byte offsets `mi`, `mo` provides, from a normalised entry. -/
def NormThmRvU (vlmax mi mo : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (entry : Nat)
    (steps : Nat → Nat → Nat) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryRU mi mo off count input S → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    Library.Outcome (EntryRvU mi mo) (DigestB mi mo) [] off count input S
      ((Riscv.isa vlmax).run rodata prog (steps off count) S)

/-- The same under the vector-length choice `ch`. -/
def NormThmRvUCh (vlmax mi mo : Nat) (ch : Nat → Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr)
    (entry : Nat) (steps : Nat → Nat → Nat) : Prop :=
  ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
    EntryRU mi mo off count input S → 64 * (off + count) ≤ 2 ^ 54 → S.pc = entry →
    Library.Outcome (EntryRvU mi mo) (DigestB mi mo) [] off count input S
      ((Riscv.isaCh vlmax ch).run rodata prog (steps off count) S)

theorem outcome_ovr_u (mi mo off count : Nat) (input : Int → BitVec 64) (S S' X : State (BitVec 64)) (D : Dom) (c : Ctl)
    (hmem : S'.mem = S.mem) (h : Library.Outcome (EntryRvU mi mo) (DigestB mi mo) [] off count input S X) :
    Library.Outcome (EntryRvU mi mo) (DigestB mi mo) [] off count input S' (ovr D c X) := by
  obtain ⟨hh, he, hp, hout⟩ := h
  refine ⟨hh, he, fun q hq => (hp q hq).trans (by rw [hmem]), ?_⟩
  rcases hout with ⟨ht, hd⟩ | ⟨next, done, ht, hmemb, _⟩
  · exact Or.inl ⟨ht, hd⟩
  · exact absurd hmemb (List.not_mem_nil)

/-- **A RISC-V kernel of the misaligned library** (any `vl` at entry). -/
def mkKernelRvU (vlmax mi mo : Nat) (name : String) (rank : Nat) (rodata : Array (BitVec 64))
    (prog : Array Riscv.Instr) (entry : Nat) (steps : Nat → Nat → Nat) (ann : Nat → Dom)
    (hann : Riscv.AnnOk prog ann) (hentry : ann entry = Dom.all)
    (h : NormThmRvU vlmax mi mo rodata prog entry steps) :
    Library.KernelThm (Riscv.isa vlmax) (EntryRvU mi mo) (DigestB mi mo) where
  name := name
  rank := rank
  targets := []
  rodata := rodata
  prog := prog
  entry := entry
  steps := steps
  thm := fun off count input S hS => by
    obtain ⟨hE, hb⟩ := hS
    have h0 := h off count input { normCtl S with pc := entry } (hE.with_pc entry) hb rfl
    obtain ⟨c', hc'⟩ := Riscv.run_ovr_ann vlmax rodata prog ann hann (steps off count) { normCtl S with pc := entry }
      (Ctl.of { S with pc := entry }) h0.2.1
    have hS1 : ovr (ann ({ normCtl S with pc := entry } : State (BitVec 64)).pc) (Ctl.of { S with pc := entry })
        { normCtl S with pc := entry } = { S with pc := entry } := by
      show ovr (ann entry) _ (normCtl { S with pc := entry }) = _
      rw [hentry, ovr_normCtl]
    rw [hS1] at hc'
    rw [hc']
    exact outcome_ovr_u mi mo off count input _ _ _ _ _ rfl h0

/-- **A RISC-V kernel of the misaligned library under the vector-length choice `ch`.** -/
def mkKernelRvUCh (vlmax mi mo : Nat) (ch : Nat → Nat) (name : String) (rank : Nat) (rodata : Array (BitVec 64))
    (prog : Array Riscv.Instr) (entry : Nat) (steps : Nat → Nat → Nat) (ann : Nat → Dom)
    (hann : Riscv.AnnOk prog ann) (hentry : ann entry = Dom.all)
    (h : NormThmRvUCh vlmax mi mo ch rodata prog entry steps) :
    Library.KernelThm (Riscv.isaCh vlmax ch) (EntryRvU mi mo) (DigestB mi mo) where
  name := name
  rank := rank
  targets := []
  rodata := rodata
  prog := prog
  entry := entry
  steps := steps
  thm := fun off count input S hS => by
    obtain ⟨hE, hb⟩ := hS
    have h0 := h off count input { normCtl S with pc := entry } (hE.with_pc entry) hb rfl
    obtain ⟨c', hc'⟩ := Riscv.run_ovr_ann_ch vlmax ch rodata prog ann hann (steps off count) { normCtl S with pc := entry }
      (Ctl.of { S with pc := entry }) h0.2.1
    have hS1 : ovr (ann ({ normCtl S with pc := entry } : State (BitVec 64)).pc) (Ctl.of { S with pc := entry })
        { normCtl S with pc := entry } = { S with pc := entry } := by
      show ovr (ann entry) _ (normCtl { S with pc := entry }) = _
      rw [hentry, ovr_normCtl]
    rw [hS1] at hc'
    rw [hc']
    exact outcome_ovr_u mi mo off count input _ _ _ _ _ rfl h0

/-- A kernel that hands nothing over: the library run is the kernel's run. -/
theorem libOk_of_stop {isa : Isa} {EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop}
    {Digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop} (T : Library.Table isa EntryAt Digest)
    (K : Library.KernelThm isa EntryAt Digest) (hK : K ∈ T) (htg : K.targets = []) (off count : Nat)
    (input : Int → BitVec 64) (S : State (BitVec 64)) (hS : EntryAt K.name off count input S) :
    Library.LibOk T K off count input S := by
  obtain ⟨hh, he, hpres, hout⟩ := K.thm off count input S hS
  rcases hout with ⟨hnone, hd⟩ | ⟨next, done, _, hmem, _⟩
  · exact ⟨_, Library.LibRun.stop K hK off count S hnone, hh, he, hpres, hd⟩
  · rw [htg] at hmem; exact absurd hmem List.not_mem_nil

theorem targets_nil {isa : Isa} {EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop}
    {Digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop} (T : Library.Table isa EntryAt Digest)
    (hT : T.shape = rvShape) (K : Library.KernelThm isa EntryAt Digest) (hK : K ∈ T) : K.targets = [] := by
  have : (K.name, K.rank, K.targets) ∈ rvShape := by rw [← hT]; exact List.mem_map.mpr ⟨K, hK, rfl⟩
  simp only [rvShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at this
  rcases this with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> exact h

/-- A table shape without tail calls. -/
def noTail (sh : List (String × Nat × List String)) : Bool := sh.all fun e => e.2.2.isEmpty

theorem targets_nil_of {isa : Isa} {EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop}
    {Digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop} (T : Library.Table isa EntryAt Digest)
    (sh : List (String × Nat × List String)) (hT : T.shape = sh) (hsh : noTail sh = true)
    (K : Library.KernelThm isa EntryAt Digest) (hK : K ∈ T) : K.targets = [] := by
  have hm : (K.name, K.rank, K.targets) ∈ sh := by rw [← hT]; exact List.mem_map.mpr ⟨K, hK, rfl⟩
  have := List.all_eq_true.mp hsh _ hm
  simpa using this

/-- **A library without tail calls** (e.g. the scalar RISC-V kernels alone): every kernel of the
table, called at its calling convention, finishes every node. -/
theorem lib_noTail {isa : Isa} {EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop}
    {Digest : (Int → BitVec 64) → State (BitVec 64) → Nat → Prop} (T : Library.Table isa EntryAt Digest)
    (sh : List (String × Nat × List String)) (hT : T.shape = sh) (hsh : noTail sh = true) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryAt K.name off count input S → Library.LibOk T K off count input S :=
  fun K hK off count input S hS => libOk_of_stop T K hK (targets_nil_of T sh hT hsh K hK) off count input S hS

/-- **The misaligned RISC-V library**: for buffers at byte offsets `mi`, `mo`, every kernel of a table
of the library's shape, called with any `vl`, finishes every node. -/
theorem lib_rvU (vlmax mi mo : Nat) (T : Library.Table (Riscv.isa vlmax) (EntryRvU mi mo) (DigestB mi mo))
    (hT : T.shape = rvShape) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryRvU mi mo K.name off count input S → Library.LibOk T K off count input S :=
  fun K hK off count input S hS => libOk_of_stop T K hK (targets_nil T hT K hK) off count input S hS

/-- **The misaligned RISC-V library under any vector-length choice.** -/
theorem lib_rvU_ch (vlmax mi mo : Nat) (ch : Nat → Nat)
    (T : Library.Table (Riscv.isaCh vlmax ch) (EntryRvU mi mo) (DigestB mi mo)) (hT : T.shape = rvShape) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryRvU mi mo K.name off count input S → Library.LibOk T K off count input S :=
  fun K hK off count input S hS => libOk_of_stop T K hK (targets_nil T hT K hK) off count input S hS

/-- Byte-level preservation of the output before byte `mo + 32·off` gives the library's word-level one. -/
theorem words_of_bytes (mo off : Nat) (S S' : State (BitVec 64))
    (h : ∀ b : Int, b < mo + 32 * off → byteAt (S'.mem rOutput) b = byteAt (S.mem rOutput) b) :
    ∀ q : Int, q < 4 * off → S'.mem rOutput q = S.mem rOutput q := by
  intro q hq
  apply word_ext
  intro t ht
  rw [← byteAt_word _ q t ht, ← byteAt_word _ q t ht]
  exact h _ (by push_cast; omega)

/-- An aligned all-count theorem (`LibRv.NormThmRv`, no tail calls) is the misaligned one at byte offsets 0. -/
theorem normU_zero (V : Nat) (rodata : Array (BitVec 64)) (prog : Array Riscv.Instr) (entry : Nat) (steps : Nat → Nat → Nat)
    (h : LibRv.NormThmRv V rodata prog entry steps []) : NormThmRvU V 0 0 rodata prog entry steps := by
  intro off count input S hE hb hpc
  have hE' : EntryR off count input S := ⟨hE.ctrl, hE.ok, hE.a2, hE.sp,
    hE.a1.trans (congrArg (fun o => gprWord ⟨rInput, o⟩) (by push_cast; omega)),
    hE.a0.trans (congrArg (fun o => gprWord ⟨rOutput, o⟩) (by push_cast; omega)), hE.inp⟩
  obtain ⟨hh, he, hp, hout⟩ := h off count input S hE' hb hpc
  refine ⟨hh, he, hp, ?_⟩
  rcases hout with ⟨ht, hd⟩ | ⟨_, _, _, hm, _⟩
  · exact Or.inl ⟨ht, fun n hn => (digestB_zero input _ (off + n)).mpr (hd n hn)⟩
  · exact absurd hm List.not_mem_nil

end Keccaktree.Kernels.LibRvU
