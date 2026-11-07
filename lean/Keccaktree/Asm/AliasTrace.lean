import Keccaktree.Asm.Alias
import Keccaktree.Asm.Iter
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Footprints of relocated runs (x86)

The access condition of `Alias.lean` is about the cells each concrete step reads and writes.  On a
segment proved symbolically, the concrete state is the evaluation of the relocated symbolic state;
its footprints are the base symbolic footprints shifted by the relocation (`cells_map`,
`cells_reloc`), so the condition becomes a check on the base trace.
-/
namespace Keccaktree.Asm
open X86

namespace X86
variable {α β : Type} [LaneOps α] [LaneOps β]

def srcMems : Src → List MemOp
  | .mem m | .bcst m => [m]
  | .reg _ => []

def gsrcMems : GSrc → List MemOp
  | .mem m => [m]
  | _ => []

/-- The memory operands whose addresses the footprints use. -/
def fpMems : Instr → List MemOp
  | .vmov _ _ src _ => srcMems src
  | .vpxor _ _ _ b | .vpand _ _ _ b | .vpandn _ _ _ b | .vpor _ _ _ b | .vpaddq _ _ _ b
  | .vpsllvq _ _ _ b | .vpsrlvq _ _ _ b | .vpternlogq _ _ _ b _ | .vpshufb _ _ _ b
  | .vpblendd _ _ _ b _ | .vpalignr _ _ _ b _ | .vpunpcklqdq _ _ _ b | .vpunpckhqdq _ _ _ b
  | .vshufi64x2 _ _ _ b _ | .vpermt2q _ _ _ b | .vperm2i128 _ _ b _ | .vinserti128 _ _ b _ => srcMems b
  | .vstore _ m _ | .vextracti128 m _ _ | .kmovw _ m | .cmpm m _ | .cmprm _ m | .xorm m _ | .storeqi m _
  | .addm m _ | .decm m | .storeq m _ | .loadq _ m => [m]
  | .alu _ _ b | .andn _ _ b | .rorx _ b _ => gsrcMems b
  | _ => []

/-- The registers whose decoding the footprints use. -/
def fpRegs (s : State α) : Instr → List Nat
  | .ret => if s.depth = 0 then [] else [4]
  | .pop _ | .call _ | .push _ => [4]
  | .repmovsb => [1, 6, 7]
  | _ => []

/-- The decodings the footprints use succeed (and the `rep movsb` count is a number). -/
def DecOk (s : State α) (i : Instr) : Prop :=
  (∀ m ∈ fpMems i, ∃ a, memAddr? s m = some a) ∧ (∀ n ∈ fpRegs s i, ∃ a, gx s n = some a) ∧
  (i = .repmovsb → ∀ n, gx s 1 = some n → n.region = 0)

theorem withMem_some (s : State α) (m : MemOp) (k : Addr → State α) (h : (withMem s m k).err = false) :
    ∃ a, memAddr? s m = some a := by
  simp only [withMem] at h; split at h
  · rename_i a ha; exact ⟨a, ha⟩
  · simp [State.fail] at h

theorem withX_some (s : State α) (n : Nat) (k : Addr → State α) (h : (withX s n k).err = false) :
    ∃ a, gx s n = some a := by
  simp only [withX] at h; split at h
  · rename_i a ha; exact ⟨a, ha⟩
  · simp [State.fail] at h

theorem withSrc_some (rodata : Array (BitVec 64)) (s : State α) (lanes : Nat) (b : Src) (k : List α → State α)
    (h : (withSrc rodata s lanes b k).err = false) : ∀ m ∈ srcMems b, ∃ a, memAddr? s m = some a := by
  simp only [withSrc] at h
  split at h
  · rename_i bs hb
    intro m hm
    cases b with
    | reg _ => simp [srcMems] at hm
    | mem m' =>
      simp only [srcMems, List.mem_singleton] at hm; subst hm
      simp only [readSrc] at hb
      rcases ha : memAddr? s m with _ | a
      · simp [ha] at hb
      · exact ⟨a, rfl⟩
    | bcst m' =>
      simp only [srcMems, List.mem_singleton] at hm; subst hm
      simp only [readSrc] at hb
      rcases ha : memAddr? s m with _ | a
      · simp [ha] at hb
      · exact ⟨a, rfl⟩
  · simp [State.fail] at h

theorem readG_some (rodata : Array (BitVec 64)) (s : State α) (b : GSrc) (k : α → State α)
    (h : (readG rodata s b k).err = false) : ∀ m ∈ gsrcMems b, ∃ a, memAddr? s m = some a := by
  intro m hm
  cases b with
  | mem m' =>
    simp only [gsrcMems, List.mem_singleton] at hm; subst hm
    exact withMem_some s m _ h
  | _ => simp [gsrcMems] at hm

theorem binop_some (rodata : Array (BitVec 64)) (s : State α) (lanes d a : Nat) (b : Src) (f : α → α → α)
    (h : (binop rodata s lanes d a b f).err = false) : ∀ m ∈ srcMems b, ∃ a, memAddr? s m = some a :=
  withSrc_some rodata s lanes b _ h

set_option maxHeartbeats 4000000 in
/-- A non-failing step decodes what its footprints use. -/
theorem decOk_of_exec (rodata : Array (BitVec 64)) (i : Instr) (s : State α) (hh : s.halted = false)
    (hne : (exec rodata i s).err = false) : DecOk s i := by
  have hT : (s.halted = true) = False := by simp [hh]
  cases i with
  | vmov lanes dst src mask =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vstore lanes m src =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | vpxor lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨binop_some rodata s _ _ _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpand lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨binop_some rodata s _ _ _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpandn lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨binop_some rodata s _ _ _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpor lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨binop_some rodata s _ _ _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpaddq lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨binop_some rodata s _ _ _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpsllq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpsrlq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vprolq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpsllvq lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpsrlvq lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpternlogq lanes d a b imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpshufb lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpshufd lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpblendd lanes d a b imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpalignr lanes d a b imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpunpcklqdq lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpunpckhqdq lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vperm2i128 d a b imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vinserti128 d a b imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vextracti128 m a imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | vshufi64x2 lanes d a b imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | vpermt2q lanes d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨withSrc_some rodata s _ _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | kmovw k m =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | vzeroupper =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | mov d src =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | xchg a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | movi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | lea d m =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | add d imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | sub d imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | andi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | shl d imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | dec d =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | xorz d =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | cmpi a imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | cmpr a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | cmpm m b =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | cmprm a m =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | test a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | bt a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | btc a imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | alu op d b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨readG_some rodata s _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | andn d a b =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨readG_some rodata s _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | rorx d b imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨readG_some rodata s _ _ hne, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | xorm m src =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | storeqi m imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | addm m imm =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | decm m =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | jcc c t =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | jmp t =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | jcct c name =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | call t =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m hm => by simp [fpMems] at hm, fun n hn => ?_, fun h => by cases h⟩
    simp only [fpRegs, List.mem_singleton] at hn; subst hn; exact withX_some s _ _ hne
  | ret =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m hm => by simp [fpMems] at hm, fun n hn => ?_, fun h => by cases h⟩
    by_cases hd : s.depth = 0
    · simp [fpRegs, hd] at hn
    · simp only [fpRegs, hd, ↓reduceIte, List.mem_singleton] at hn; subst hn
      simp only [hd, ↓reduceIte] at hne; exact withX_some s _ _ hne
  | push src =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m hm => by simp [fpMems] at hm, fun n hn => ?_, fun h => by cases h⟩
    simp only [fpRegs, List.mem_singleton] at hn; subst hn; exact withX_some s _ _ hne
  | pop d =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m hm => by simp [fpMems] at hm, fun n hn => ?_, fun h => by cases h⟩
    simp only [fpRegs, List.mem_singleton] at hn; subst hn; exact withX_some s _ _ hne
  | storeq m src =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | loadq d m =>
    simp only [exec, hT, ↓reduceIte] at hne
    refine ⟨fun m' hm => ?_, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
    simp only [fpMems, List.mem_singleton] at hm; subst hm; exact withMem_some s _ _ hne
  | repmovsb =>
    simp only [exec, hT, ↓reduceIte] at hne
    obtain ⟨n1, h1⟩ := withX_some s _ _ hne
    simp only [withX, h1] at hne
    obtain ⟨n6, h6⟩ := withX_some s _ _ hne
    simp only [withX, h6] at hne
    obtain ⟨n7, h7⟩ := withX_some s _ _ hne
    simp only [withX, h7] at hne
    refine ⟨fun m hm => by simp [fpMems] at hm, fun n hn => ?_, fun _ n hn => ?_⟩
    · simp only [fpRegs, List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl
      · exact ⟨_, h1⟩
      · exact ⟨_, h6⟩
      · exact ⟨_, h7⟩
    · rw [h1] at hn; cases hn
      simp only [repBody] at hne
      by_cases hr : n1.region = 0
      · exact hr
      · simp [hr, State.fail] at hne
  | tailcall name =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩
  | nop =>
    simp only [exec, hT, ↓reduceIte] at hne
    exact ⟨fun m hm => by simp [fpMems] at hm, fun n hn => by simp [fpRegs] at hn, fun h => by cases h⟩

section transfer
variable {f : α → β} (hf : IsHom f)
include hf

set_option maxHeartbeats 4000000 in
/-- **Footprints under evaluation**: an instruction's read and write cells in an evaluated state are those
of the symbolic state (when the decodings succeed there). -/
theorem cells_map (i : Instr) (X : State α) (hd : DecOk X i) :
    reads (mapState f X) i = reads X i ∧ writes (mapState f X) i = writes X i := by
  cases i with
  | vmov lanes dst src mask =>
    obtain ⟨hm, -, -⟩ := hd
    cases src with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vstore lanes m src =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpxor lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpand lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpandn lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpor lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpaddq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpsllq lanes d a imm =>
    simp [reads, writes]
  | vpsrlq lanes d a imm =>
    simp [reads, writes]
  | vprolq lanes d a imm =>
    simp [reads, writes]
  | vpsllvq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpsrlvq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpternlogq lanes d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpshufb lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpshufd lanes d a imm =>
    simp [reads, writes]
  | vpblendd lanes d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpalignr lanes d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpunpcklqdq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpunpckhqdq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vperm2i128 d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vinserti128 d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vextracti128 m a imm =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vshufi64x2 lanes d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vpermt2q lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | kmovw k m =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | vzeroupper =>
    simp [reads, writes]
  | mov d src =>
    simp [reads, writes]
  | xchg a b =>
    simp [reads, writes]
  | movi d imm =>
    simp [reads, writes]
  | lea d m =>
    simp [reads, writes]
  | add d imm =>
    simp [reads, writes]
  | sub d imm =>
    simp [reads, writes]
  | andi d imm =>
    simp [reads, writes]
  | shl d imm =>
    simp [reads, writes]
  | dec d =>
    simp [reads, writes]
  | xorz d =>
    simp [reads, writes]
  | cmpi a imm =>
    simp [reads, writes]
  | cmpr a b =>
    simp [reads, writes]
  | cmpm m b =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | cmprm a m =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | test a b =>
    simp [reads, writes]
  | bt a b =>
    simp [reads, writes]
  | btc a imm =>
    simp [reads, writes]
  | alu op d b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, gsrcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | _ => simp [reads, writes, gsrcCells]
  | andn d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, gsrcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | _ => simp [reads, writes, gsrcCells]
  | rorx d b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, gsrcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
    | _ => simp [reads, writes, gsrcCells]
  | xorm m src =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | storeqi m imm =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | addm m imm =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | decm m =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | jcc c t =>
    simp [reads, writes]
  | jmp t =>
    simp [reads, writes]
  | jcct c name =>
    simp [reads, writes]
  | call t =>
    obtain ⟨-, hr, -⟩ := hd
    obtain ⟨a', ha⟩ := hr 4 (by simp [fpRegs]); simp [reads, writes, ha, gx_map_some hf _ _ _ ha]
  | ret =>
    obtain ⟨-, hr, -⟩ := hd
    by_cases hdz : X.depth = 0
    · simp [reads, writes, hdz]
    · obtain ⟨a', ha⟩ := hr 4 (by simp [fpRegs, hdz]); simp [hdz, reads, writes, ha, gx_map_some hf _ _ _ ha]
  | push src =>
    obtain ⟨-, hr, -⟩ := hd
    obtain ⟨a', ha⟩ := hr 4 (by simp [fpRegs]); simp [reads, writes, ha, gx_map_some hf _ _ _ ha]
  | pop d =>
    obtain ⟨-, hr, -⟩ := hd
    obtain ⟨a', ha⟩ := hr 4 (by simp [fpRegs]); simp [reads, writes, ha, gx_map_some hf _ _ _ ha]
  | storeq m src =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | loadq d m =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_map_some hf _ _ _ ha, getV_map hf]
  | repmovsb =>
    obtain ⟨-, hr, hc⟩ := hd
    obtain ⟨n1, h1⟩ := hr 1 (by simp [fpRegs])
    obtain ⟨n6, h6⟩ := hr 6 (by simp [fpRegs])
    obtain ⟨n7, h7⟩ := hr 7 (by simp [fpRegs])
    simp [reads, writes, h1, h6, h7, gx_map_some hf _ _ _ h1, gx_map_some hf _ _ _ h6, gx_map_some hf _ _ _ h7]
  | tailcall name =>
    simp [reads, writes]
  | nop =>
    simp [reads, writes]

end transfer

/-- A relocated cell. -/
def shiftCell (ρ : Reloc) (c : Region × Int) : Region × Int := (c.1, c.2 + ρ.wshift c.1)

theorem storeCells_addr (ρ : Reloc) (hρ : ρ.ok) (a : Addr) (n : Nat) :
    storeCells (ρ.addr a) n = (storeCells a n).map (shiftCell ρ) := by
  simp only [storeCells, List.map_map, Function.comp_def, shiftCell, Reloc.addr_region, Reloc.addr_div8 ρ hρ]
  congr 1; funext i; congr 1; omega

theorem storeCells_addr_sub (ρ : Reloc) (hρ : ρ.ok) (a : Addr) (d : Int) (n : Nat) :
    storeCells { region := a.region, off := (ρ.addr a).off - d } n =
      (storeCells { region := a.region, off := a.off - d } n).map (shiftCell ρ) := by
  rw [← storeCells_addr ρ hρ]
  congr 1
  simp only [Reloc.addr, Addr.mk.injEq, true_and]; omega

set_option maxHeartbeats 4000000 in
/-- **Footprints under relocation**: the relocated state's cells are the shifted cells. -/
theorem cells_reloc (ρ : Reloc) (hρ : ρ.ok) (rodata : Array (BitVec 64)) (i : Instr) (X : State E) (hd : DecOk X i)
    (hok : ∀ e ∈ decodes rodata i X, E.relocOk ρ e) :
    reads (relocState ρ X) i = (reads X i).map (shiftCell ρ) ∧
      writes (relocState ρ X) i = (writes X i).map (shiftCell ρ) := by
  cases i with
  | vmov lanes dst src mask =>
    obtain ⟨hm, -, -⟩ := hd
    cases src with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vstore lanes m src =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpxor lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpand lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpandn lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpor lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpaddq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpsllq lanes d a imm =>
    simp [reads, writes]
  | vpsrlq lanes d a imm =>
    simp [reads, writes]
  | vprolq lanes d a imm =>
    simp [reads, writes]
  | vpsllvq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpsrlvq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpternlogq lanes d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpshufb lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpshufd lanes d a imm =>
    simp [reads, writes]
  | vpblendd lanes d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpalignr lanes d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpunpcklqdq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpunpckhqdq lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vperm2i128 d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vinserti128 d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vextracti128 m a imm =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vshufi64x2 lanes d a b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vpermt2q lanes d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | reg _ => simp [reads, writes, srcCells]
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | bcst m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, srcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | kmovw k m =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | vzeroupper =>
    simp [reads, writes]
  | mov d src =>
    simp [reads, writes]
  | xchg a b =>
    simp [reads, writes]
  | movi d imm =>
    simp [reads, writes]
  | lea d m =>
    simp [reads, writes]
  | add d imm =>
    simp [reads, writes]
  | sub d imm =>
    simp [reads, writes]
  | andi d imm =>
    simp [reads, writes]
  | shl d imm =>
    simp [reads, writes]
  | dec d =>
    simp [reads, writes]
  | xorz d =>
    simp [reads, writes]
  | cmpi a imm =>
    simp [reads, writes]
  | cmpr a b =>
    simp [reads, writes]
  | cmpm m b =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | cmprm a m =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | test a b =>
    simp [reads, writes]
  | bt a b =>
    simp [reads, writes]
  | btc a imm =>
    simp [reads, writes]
  | alu op d b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, gsrcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | _ => simp [reads, writes, gsrcCells]
  | andn d a b =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, gsrcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | _ => simp [reads, writes, gsrcCells]
  | rorx d b imm =>
    obtain ⟨hm, -, -⟩ := hd
    cases b with
    | mem m' => obtain ⟨a', ha⟩ := hm m' (by simp [fpMems, gsrcMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
    | _ => simp [reads, writes, gsrcCells]
  | xorm m src =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | storeqi m imm =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | addm m imm =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | decm m =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | jcc c t =>
    simp [reads, writes]
  | jmp t =>
    simp [reads, writes]
  | jcct c name =>
    simp [reads, writes]
  | call t =>
    obtain ⟨-, hr, -⟩ := hd
    obtain ⟨a', ha⟩ := hr 4 (by simp [fpRegs]); simp [reads, writes, ha, gx_reloc ρ hρ _ _ _ ha (hok _ (by simp [decodes])), storeCells_addr ρ hρ, storeCells_addr_sub ρ hρ]
  | ret =>
    obtain ⟨-, hr, -⟩ := hd
    by_cases hdz : X.depth = 0
    · simp [reads, writes, hdz]
    · obtain ⟨a', ha⟩ := hr 4 (by simp [fpRegs, hdz]); simp [hdz, reads, writes, ha, gx_reloc ρ hρ _ _ _ ha (hok _ (by simp [hdz, decodes])), storeCells_addr ρ hρ]
  | push src =>
    obtain ⟨-, hr, -⟩ := hd
    obtain ⟨a', ha⟩ := hr 4 (by simp [fpRegs]); simp [reads, writes, ha, gx_reloc ρ hρ _ _ _ ha (hok _ (by simp [decodes])), storeCells_addr ρ hρ, storeCells_addr_sub ρ hρ]
  | pop d =>
    obtain ⟨-, hr, -⟩ := hd
    obtain ⟨a', ha⟩ := hr 4 (by simp [fpRegs]); simp [reads, writes, ha, gx_reloc ρ hρ _ _ _ ha (hok _ (by simp [decodes])), storeCells_addr ρ hρ, storeCells_addr_sub ρ hρ]
  | storeq m src =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | loadq d m =>
    obtain ⟨hm, -, -⟩ := hd
    obtain ⟨a', ha⟩ := hm m (by simp [fpMems]); simp [reads, writes, memCells, srcCells, gsrcCells, ha, memAddr?_reloc ρ hρ _ _ _ ha (fun g disp h => hok _ (by simp [decodes, h])), getV_reloc, storeCells_addr ρ hρ]
  | repmovsb =>
    obtain ⟨-, hr, hc⟩ := hd
    obtain ⟨n1, h1⟩ := hr 1 (by simp [fpRegs])
    obtain ⟨n6, h6⟩ := hr 6 (by simp [fpRegs])
    obtain ⟨n7, h7⟩ := hr 7 (by simp [fpRegs])
    have hn1 : ρ.addr n1 = n1 := Reloc.addr_region0 ρ hρ n1 (hc rfl n1 h1)
    simp [reads, writes, h1, h6, h7, gx_reloc ρ hρ _ _ _ h1 (hok _ (by simp [decodes])),
      gx_reloc ρ hρ _ _ _ h6 (hok _ (by simp [decodes])), gx_reloc ρ hρ _ _ _ h7 (hok _ (by simp [decodes])), hn1, storeCells_addr ρ hρ]
  | tailcall name =>
    simp [reads, writes]
  | nop =>
    simp [reads, writes]

end X86
end Keccaktree.Asm

/-! ## The access condition along a relocated symbolic path -/
namespace Keccaktree.Asm
open X86
namespace X86

abbrev Cells := List (Region × Int)

/-- The read and write cells of each step along a path of a symbolic state. -/
def traceCells (rodata : Array (BitVec 64)) (prog : Array Instr) : List Nat → State E → List (Cells × Cells)
  | [], _ => []
  | i :: rest, s => (reads s (prog.getD i .nop), writes s (prog.getD i .nop)) ::
      traceCells rodata prog rest (exec rodata (prog.getD i .nop) s)

/-- The bound after a step's (base) writes, output cells shifted by `δ2`. -/
def bumpC (δ2 b : Int) (w : Cells) : Int := w.foldl (fun b c => if c.1 = rOutput then max b (c.2 + δ2 + 1) else b) b

/-- The access condition on base cells shifted by `δ1` (input) and `δ2` (output). -/
def accessCells (δ1 δ2 : Int) : Int → Int → List (Cells × Cells) → Prop
  | b, bf, [] => b ≤ bf
  | b, bf, (r, w) :: l => (∀ c ∈ r, c.1 = rInput → b ≤ c.2 + δ1) ∧ (∀ c ∈ w, c.1 ≠ rInput) ∧
      accessCells δ1 δ2 (bumpC δ2 b w) bf l

theorem fold_shift (ρ : Reloc) (W : Cells) : ∀ b : Int,
    (W.map (shiftCell ρ)).foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) b =
      bumpC (ρ.wshift rOutput) b W := by
  induction W with
  | nil => intro b; rfl
  | cons c W ih =>
    intro b
    simp only [List.map_cons, List.foldl_cons, bumpC] at ih ⊢
    rw [← ih]
    congr 1
    by_cases h : c.1 = rOutput
    · simp only [shiftCell, h, ↓reduceIte]; (try congr 1); (try omega)
    · simp only [shiftCell, h, ↓reduceIte]

theorem bumpB_eq (ρ : Reloc) (b : Int) (s : State (BitVec 64)) (i : Instr) (W : Cells)
    (hw : writes s i = W.map (shiftCell ρ)) : bumpB b s i = bumpC (ρ.wshift rOutput) b W := by
  unfold bumpB; rw [hw]; exact fold_shift ρ W b

set_option maxHeartbeats 4000000 in
/-- **The access condition along a relocated symbolic path**, from the base cells. -/
theorem path_access (ρ : Reloc) (hρ : ρ.ok) (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (idx : List Nat) (t : State E) (env : Nat → BitVec 64) (b bf : Int),
      X86.isa.pathOk rodata prog idx t = true →
      (∀ e ∈ X86.isaReloc.traceDecodes rodata (idx.map (prog.getD · .nop)) t, E.relocOk ρ e) →
      accessCells (ρ.wshift rInput) (ρ.wshift rOutput) b bf (traceCells rodata prog idx t) →
      AccessRun rodata prog idx.length b bf (mapState (E.eval env) (relocState ρ t)) := by
  intro idx
  induction idx with
  | nil => intro t env b bf _ _ h; exact h
  | cons i rest ih =>
    intro t env b bf hp hdec hacc
    simp only [Isa.pathOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
    obtain ⟨⟨⟨he, hh⟩, hpc⟩, hrest⟩ := hp
    simp only [List.map_cons, Isa.Relocatable.traceDecodes, List.mem_append] at hdec
    simp only [traceCells, accessCells] at hacc
    obtain ⟨hr, hw, hacc⟩ := hacc
    generalize hins : prog.getD i .nop = ins at hdec hr hw hacc hrest
    have hne1 : (exec rodata ins t).err = false := by
      have := X86.isa.pathOk_err rodata prog rest _ hrest; exact this
    have hdec1 : ∀ e ∈ X86.decodes rodata ins t, E.relocOk ρ e := fun e h => hdec e (Or.inl h)
    have hrel : exec rodata ins (relocState ρ t) = relocState ρ (exec rodata ins t) :=
      X86.exec_reloc ρ hρ rodata ins t hne1 hdec1
    have hne2 : (exec rodata ins (relocState ρ t)).err = false := by rw [hrel]; exact hne1
    have hmap : exec rodata ins (mapState (E.eval env) (relocState ρ t)) =
        mapState (E.eval env) (relocState ρ (exec rodata ins t)) := by
      rw [X86.exec_map (E.eval_isHom env) rodata ins _ hne2, hrel]
    have hd1 := decOk_of_exec rodata ins t hh hne1
    have hd2 := decOk_of_exec rodata ins (relocState ρ t) hh hne2
    obtain ⟨hcr, hcw⟩ := cells_reloc ρ hρ rodata ins t hd1 hdec1
    obtain ⟨hmr, hmw⟩ := cells_map (E.eval_isHom env) ins (relocState ρ t) hd2
    simp only [List.length_cons, AccessRun, halted_map, halted_reloc, hh, Bool.false_eq_true, ↓reduceIte,
      pc_map, pc_reloc, hpc, hins]
    refine ⟨?_, ⟨fun c hc hc1 => ?_, fun c hc hc1 => ?_⟩, ?_⟩
    · rw [hmap]; exact hne1
    · rw [hmr, hcr] at hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      simp only [shiftCell] at hc1 ⊢
      have := hr c0 hc0 hc1; rw [hc1]; exact this
    · rw [hmw, hcw] at hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      exact hw c0 hc0 hc1
    · rw [bumpB_eq ρ b _ ins (writes t ins) (hmw.trans hcw), hmap]
      exact ih _ env _ bf hrest (fun e h => hdec e (Or.inr h)) hacc

end X86

/-- **The access condition of a certified slice at a relocated position.** -/
theorem SliceCert.access {rodata : Array (BitVec 64)} {prog : Array X86.Instr} {B : Int}
    (C : SliceCert X86.isa X86.isaReloc rodata prog B) (ρ : Reloc) (hρ : ρ.ok) (hw : ρ.within B)
    (S : State (BitVec 64)) (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S) (hs : SliceCert.Ok S)
    (b bf : Int) (h : X86.accessCells (ρ.wshift rInput) (ρ.wshift rOutput) b bf (X86.traceCells rodata prog C.idx C.cut)) :
    X86.AccessRun rodata prog C.idx.length b bf S := by
  have he : mapState (E.eval (envOf S)) (relocState ρ C.cut) = S := by
    show mapState (E.eval (envOf S)) (relocState ρ (cutOf C.ctl C.sc)) = S
    rw [hc]; exact eval_cutOf C.ctl S hs
  rw [← he]
  exact X86.path_access ρ hρ rodata prog C.idx C.cut _ b bf C.path (C.dec_ok ρ hρ hw) h

end Keccaktree.Asm

/-! ## Summaries of base cells, splitting and composing -/
namespace Keccaktree.Asm
open X86
namespace X86

/-- What the access condition needs from a list of base step cells: the lowest input word read, the
highest output word written, the smallest distance (read index − write index) of an input read after an
output write, and whether an input word is written. -/
structure Summ where
  loR : Option Int
  hiW : Option Int
  gap : Option Int
  inW : Bool
  deriving DecidableEq, Repr

def minO : Option Int → Option Int → Option Int
  | some a, some b => some (min a b) | some a, none => some a | none, b => b
def maxO : Option Int → Option Int → Option Int
  | some a, some b => some (max a b) | some a, none => some a | none, b => b
def subO : Option Int → Option Int → Option Int
  | some a, some b => some (a - b) | _, _ => none

def loIn (r : Cells) : Option Int := r.foldl (fun o c => if c.1 = rInput then minO o (some c.2) else o) none
def hiOut (w : Cells) : Option Int := w.foldl (fun o c => if c.1 = rOutput then maxO o (some c.2) else o) none

def summ : List (Cells × Cells) → Summ
  | [] => ⟨none, none, none, false⟩
  | (r, w) :: l =>
    let t := summ l
    ⟨minO (loIn r) t.loR, maxO (hiOut w) t.hiW, minO t.gap (subO t.loR (hiOut w)),
      w.any (fun c => c.1 = rInput) || t.inW⟩

theorem minO_left (a : Int) (o : Option Int) : ∃ y, minO (some a) o = some y ∧ y ≤ a := by
  cases o <;> simp [minO] <;> omega
theorem minO_right (a : Int) (o : Option Int) : ∃ y, minO o (some a) = some y ∧ y ≤ a := by
  cases o <;> simp [minO] <;> omega
theorem maxO_left (a : Int) (o : Option Int) : ∃ y, maxO (some a) o = some y ∧ a ≤ y := by
  cases o <;> simp [maxO] <;> omega
theorem maxO_right (a : Int) (o : Option Int) : ∃ y, maxO o (some a) = some y ∧ a ≤ y := by
  cases o <;> simp [maxO] <;> omega

theorem foldMin_some (l : Cells) : ∀ (x : Int) (o : Option Int), o = some x →
    ∃ lo, l.foldl (fun o c => if c.1 = rInput then minO o (some c.2) else o) o = some lo ∧ lo ≤ x := by
  induction l with
  | nil => intro x o h; exact ⟨x, h, Int.le_refl _⟩
  | cons e l ih =>
    intro x o h; subst h
    simp only [List.foldl_cons]
    split
    · obtain ⟨y, hy, hle⟩ := minO_right e.2 (some x)
      obtain ⟨lo, h1, h2⟩ := ih y _ hy
      refine ⟨lo, h1, ?_⟩
      simp [minO] at hy; omega
    · exact ih x _ rfl

theorem foldMax_some (l : Cells) : ∀ (x : Int) (o : Option Int), o = some x →
    ∃ hi, l.foldl (fun o c => if c.1 = rOutput then maxO o (some c.2) else o) o = some hi ∧ x ≤ hi := by
  induction l with
  | nil => intro x o h; exact ⟨x, h, Int.le_refl _⟩
  | cons e l ih =>
    intro x o h; subst h
    simp only [List.foldl_cons]
    split
    · obtain ⟨y, hy, hle⟩ := maxO_right e.2 (some x)
      obtain ⟨hi, h1, h2⟩ := ih y _ hy
      refine ⟨hi, h1, ?_⟩
      simp [maxO] at hy; omega
    · exact ih x _ rfl

theorem loIn_le (r : Cells) (c : Region × Int) (hc : c ∈ r) (h1 : c.1 = rInput) :
    ∃ lo, loIn r = some lo ∧ lo ≤ c.2 := by
  suffices ∀ o, ∃ lo, r.foldl (fun o c => if c.1 = rInput then minO o (some c.2) else o) o = some lo ∧ lo ≤ c.2 by
    exact this none
  induction r with
  | nil => simp at hc
  | cons d r ih =>
    intro o
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [if_pos h1]
      obtain ⟨y, hy, hle⟩ := minO_right c.2 o
      obtain ⟨lo, h2, h3⟩ := foldMin_some r y _ hy
      exact ⟨lo, h2, by omega⟩
    · exact ih hc' _

theorem hiOut_ge (w : Cells) (c : Region × Int) (hc : c ∈ w) (h1 : c.1 = rOutput) :
    ∃ hi, hiOut w = some hi ∧ c.2 ≤ hi := by
  suffices ∀ o, ∃ hi, w.foldl (fun o c => if c.1 = rOutput then maxO o (some c.2) else o) o = some hi ∧ c.2 ≤ hi by
    exact this none
  induction w with
  | nil => simp at hc
  | cons d w ih =>
    intro o
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [if_pos h1]
      obtain ⟨y, hy, hle⟩ := maxO_right c.2 o
      obtain ⟨hi, h2, h3⟩ := foldMax_some w y _ hy
      exact ⟨hi, h2, by omega⟩
    · exact ih hc' _

/-- The bound after writes stays below the highest written output word (shifted), or unchanged. -/
theorem bumpC_le (δ2 b bf : Int) (w : Cells) (hb : b ≤ bf) (hw : ∀ hi, hiOut w = some hi → hi + δ2 + 1 ≤ bf) :
    bumpC δ2 b w ≤ bf := by
  unfold bumpC
  suffices ∀ (b' : Int), b' ≤ bf → ∀ (l : Cells), (∀ c ∈ l, c.1 = rOutput → c.2 + δ2 + 1 ≤ bf) →
      l.foldl (fun b c => if c.1 = rOutput then max b (c.2 + δ2 + 1) else b) b' ≤ bf by
    apply this b hb w
    intro c hc h1
    obtain ⟨hi, h2, h3⟩ := hiOut_ge w c hc h1
    have := hw hi h2; omega
  intro b' hb' l
  induction l generalizing b' with
  | nil => intro _; exact hb'
  | cons c l ih =>
    intro hl
    simp only [List.foldl_cons]
    apply ih _ _ (fun d hd => hl d (List.mem_cons_of_mem _ hd))
    split
    · rename_i h; have := hl c (List.mem_cons_self) h; omega
    · exact hb'

/-- **The access condition from a summary** (linear conditions on the shifts and bounds). -/
theorem summ_access (δ1 δ2 : Int) : ∀ (l : List (Cells × Cells)) (b bf : Int),
    (∀ lo, (summ l).loR = some lo → b ≤ lo + δ1) →
    (∀ g, (summ l).gap = some g → δ2 + 1 ≤ g + δ1) →
    b ≤ bf → (∀ hi, (summ l).hiW = some hi → hi + δ2 + 1 ≤ bf) →
    (summ l).inW = false → accessCells δ1 δ2 b bf l := by
  intro l
  induction l with
  | nil => intro b bf _ _ hb _ _; exact hb
  | cons rw l ih =>
    obtain ⟨r, w⟩ := rw
    intro b bf hlo hgap hb hhi hin
    simp only [summ, Bool.or_eq_false_iff, List.any_eq_false] at hlo hgap hhi hin
    refine ⟨fun c hc h1 => ?_, fun c hc h1 => ?_, ?_⟩
    · obtain ⟨lo, h2, h3⟩ := loIn_le r c hc h1
      rw [h2] at hlo
      obtain ⟨y, hy, hle⟩ := minO_left lo (summ l).loR
      have := hlo y hy; omega
    · have := hin.1 c hc; simp [h1] at this
    · apply ih
      · intro lo hlo'
        rw [hlo'] at hlo hgap
        obtain ⟨y, hy, hle⟩ := minO_right lo (loIn r)
        have hb2 : b ≤ lo + δ1 := by have := hlo y hy; omega
        unfold bumpC
        suffices ∀ (b' : Int), b' ≤ lo + δ1 → ∀ (l' : Cells), (∀ c ∈ l', c ∈ w) →
            l'.foldl (fun b c => if c.1 = rOutput then max b (c.2 + δ2 + 1) else b) b' ≤ lo + δ1 by
          exact this b hb2 w (fun c hc => hc)
        intro b' hb' l'
        induction l' generalizing b' with
        | nil => intro _; exact hb'
        | cons c l' ih2 =>
          intro hsub
          simp only [List.foldl_cons]
          apply ih2 _ _ (fun d hd => hsub d (List.mem_cons_of_mem _ hd))
          split
          · rename_i h
            obtain ⟨hi, hhi1, hhi2⟩ := hiOut_ge w c (hsub c List.mem_cons_self) h
            rw [hhi1] at hgap
            obtain ⟨y2, hy2, hle2⟩ := minO_right (lo - hi) (summ l).gap
            have : δ2 + 1 ≤ y2 + δ1 := hgap y2 (by simpa only [subO] using hy2)
            omega
          · exact hb'
      · intro g hg'
        rw [hg'] at hgap
        obtain ⟨y, hy, hle⟩ := minO_left g (subO (summ l).loR (hiOut w))
        have := hgap y hy; omega
      · apply bumpC_le δ2 b bf w hb
        intro hi h
        rw [h] at hhi
        obtain ⟨y, hy, hle⟩ := maxO_left hi (summ l).hiW
        have := hhi y hy; omega
      · intro hi h
        rw [h] at hhi
        obtain ⟨y, hy, hle⟩ := maxO_right hi (hiOut w)
        have := hhi y hy; omega
      · exact hin.2

end X86
end Keccaktree.Asm
