import Keccaktree.Asm.LibX86
import Keccaktree.Asm.ArmHom
import Keccaktree.Asm.RiscvHom
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The whole library: the kernel tables of the three instruction sets

A kernel tail-calls only kernels of its own instruction set, so the library is
three tables (x86-64, AArch64, and RISC-V for each vector length).  The shape of
each table (symbol, rank, tail-call targets; the targets are those of the
programs' `tailcall`/`jcct` instructions, `notes/paths.md` finding 6) is fixed
here; the rank is the depth in the acyclic tail-call graph, so every target has
a lower rank (`shapeOk`, decided).

`lib_of_shape`: a table with that shape — the kernels' all-count theorems,
plugged in by the kernel agents in the order of the shape — gives the library
theorem for every kernel entry, every count and every node.
-/
namespace Keccaktree.Asm.LibTable
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.LibX86 Library

def sym (k : String) : String := "keccaktree_keccak256_" ++ k

/-- The x86-64 kernels: symbol, rank, tail-call targets. -/
def x86Shape : List (String × Nat × List String) := [
  (sym "x86_x1", 0, []),
  (sym "avx2_x2", 1, [sym "x86_x1"]),
  (sym "avx2_x4", 2, [sym "avx2_x2", sym "x86_x1"]),
  (sym "avx2_x5", 3, [sym "avx2_x4", sym "x86_x1"]),
  (sym "avx2_x6", 4, [sym "avx2_x4", sym "avx2_x5", sym "x86_x1"]),
  (sym "avx2_x8", 4, [sym "avx2_x4", sym "avx2_x5", sym "x86_x1"]),
  (sym "avx2_x9", 5, [sym "avx2_x4", sym "avx2_x5", sym "avx2_x8", sym "x86_x1"]),
  (sym "avx2_x10", 5, [sym "avx2_x4", sym "avx2_x5", sym "avx2_x8", sym "x86_x1"]),
  (sym "avx512vl_x4", 1, [sym "x86_x1"]),
  (sym "avx512vl_x4d", 1, [sym "x86_x1"]),
  (sym "avx512_x8", 2, [sym "avx512vl_x4", sym "x86_x1"]),
  (sym "avx512_x8d", 2, [sym "avx512vl_x4d", sym "x86_x1"]),
  (sym "avx512_x9", 3, [sym "avx512_x8", sym "avx512vl_x4", sym "x86_x1"]),
  (sym "avx512_x9d", 3, [sym "avx512_x8d", sym "avx512vl_x4d", sym "x86_x1"])]

/-- The AArch64 kernels. -/
def armShape : List (String × Nat × List String) := [
  (sym "scalar_x1", 0, []),
  (sym "sha3_x2", 0, []),
  (sym "neon_x2", 0, []),
  (sym "sha3_x3", 1, [sym "scalar_x1"]),
  (sym "sha3_x3r", 1, [sym "sha3_x2"]),
  (sym "neon_x3", 1, [sym "scalar_x1"])]

/-- The RISC-V kernels (one table per vector length). -/
def rvShape : List (String × Nat × List String) := [
  (sym "rv64_x1", 0, []),
  (sym "zbb_x1", 0, []),
  (sym "rvv", 0, []),
  (sym "rvv_zvkb", 0, [])]

theorem x86Shape_ok : shapeOk x86Shape = true := by decide
theorem armShape_ok : shapeOk armShape = true := by decide
theorem rvShape_ok : shapeOk rvShape = true := by decide

/-- The largest rank of a shape. -/
def maxRank (sh : List (String × Nat × List String)) : Nat := sh.foldl (fun m e => max m e.2.1) 0

theorem rank_le_maxRank (sh : List (String × Nat × List String)) (e : String × Nat × List String) (he : e ∈ sh) :
    e.2.1 ≤ maxRank sh := by
  unfold maxRank
  suffices ∀ (l : List (String × Nat × List String)) (m : Nat), e ∈ l ∨ e.2.1 ≤ m → e.2.1 ≤ l.foldl (fun m e => max m e.2.1) m from
    this sh 0 (Or.inl he)
  intro l
  induction l with
  | nil => intro m h; simpa using h
  | cons x l ih =>
    intro m h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · rcases List.mem_cons.mp h with h | h
      · subst h; right; exact Nat.le_max_right _ _
      · left; exact h
    · right; exact Nat.le_trans h (Nat.le_max_left _ _)

/-- **The library theorem for a table of a given shape**: every kernel of the table, called at
its entry with the instruction set's calling convention, on any count, finishes every node
(through the tail calls), without a model fault. -/
theorem lib_of_shape {isa : Isa} {EntryAt : String → Nat → Nat → (Int → BitVec 64) → State (BitVec 64) → Prop}
    (T : Table isa EntryAt Digest) (sh : List (String × Nat × List String)) (hT : T.shape = sh)
    (hok : shapeOk sh = true) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryAt K.name off count input S → LibOk T K off count input S := by
  intro K hK off count input S hS
  have hrank : ∀ K ∈ T, K.rank ≤ maxRank sh := by
    intro K hK
    have : (K.name, K.rank, K.targets) ∈ sh := by
      rw [← hT]; exact List.mem_map.mpr ⟨K, hK, rfl⟩
    exact rank_le_maxRank sh _ this
  exact lib_correct T (maxRank sh) hrank (ranksOk_of_shape T (by rw [hT]; exact hok)) digest_local _ K hK off
    count input S (Nat.le_refl _) hS

/-- **The x86-64 library**, for every runtime configuration `cfg` of the calibrated thresholds
(`.Lsmall_tail_max`, `.Lmid_tail_max`): the table may depend on the configuration (the two
kernels' constant images), with the fixed shape. -/
theorem lib_x86 {Cfg : Type} (T : Cfg → Table X86.isa EntryX86 Digest) (hT : ∀ cfg, (T cfg).shape = x86Shape)
    (cfg : Cfg) : ∀ K ∈ T cfg, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryX86 K.name off count input S → LibOk (T cfg) K off count input S :=
  lib_of_shape (T cfg) x86Shape (hT cfg) x86Shape_ok

/-! ## AArch64 and RISC-V calling conventions -/

/-- The AArch64 entry state (AAPCS64: `x0` output, `x1` input, `x2` count, `sp`), control part of a
fresh call. -/
structure EntryA (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.vl = 0 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  x2 : S.getGD 2 = gprWord ⟨0, count⟩
  sp : S.getGD 31 = gprWord ⟨rStack, 1048576⟩
  x1 : S.getGD 1 = gprWord ⟨rInput, 64 * off⟩
  x0 : S.getGD 0 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

/-- The AArch64 calling convention of the library: any NZCV flags (a tail call leaves them). -/
def EntryArm (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  EntryA off count input (normCtl S) ∧ 64 * (off + count) ≤ 2 ^ 54

/-- The RISC-V entry state (`a0` output, `a1` input, `a2` count, `sp = x2`), control part of a fresh
call. -/
structure EntryR (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop where
  ctrl : S.g = Vector.replicate 32 ⟨0, 0⟩ ∧ S.k = Vector.replicate 8 0 ∧ S.zf = false ∧ S.cf = false ∧
    S.nf = false ∧ S.vf = false ∧ S.vl = 0 ∧ S.depth = 0
  ok : S.err = false ∧ S.halted = false ∧ S.tail = none
  a2 : S.getGD 12 = gprWord ⟨0, count⟩
  sp : S.getGD 2 = gprWord ⟨rStack, 1048576⟩
  a1 : S.getGD 11 = gprWord ⟨rInput, 64 * off⟩
  a0 : S.getGD 10 = gprWord ⟨rOutput, 32 * off⟩
  inp : ∀ q, S.mem rInput q = input q

/-- The RISC-V calling convention of the library: any vector length at entry (unspecified by the
ABI). -/
def EntryRv (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  EntryR off count input (normCtl S) ∧ 64 * (off + count) ≤ 2 ^ 54

/-- **The AArch64 library.** -/
theorem lib_arm (T : Table Arm.isa EntryArm Digest) (hT : T.shape = armShape) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryArm K.name off count input S → LibOk T K off count input S :=
  lib_of_shape T armShape hT armShape_ok

/-- **The RISC-V library**, for every vector length `vlmax` (lanes per register: VLEN / 64). -/
theorem lib_rv (vlmax : Nat) (T : Table (Riscv.isa vlmax) EntryRv Digest) (hT : T.shape = rvShape) :
    ∀ K ∈ T, ∀ (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)),
      EntryRv K.name off count input S → LibOk T K off count input S :=
  lib_of_shape T rvShape hT rvShape_ok

end Keccaktree.Asm.LibTable
