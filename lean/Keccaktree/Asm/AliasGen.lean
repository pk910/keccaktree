import Keccaktree.Asm.AliasBase
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# In-place hashing for any instruction set with footprints

The x86 development of `Alias.lean` only uses, of the instruction set, its step function, the cells a
step reads and writes, that the write cells do not depend on memory, and memory locality
(`exec_local`).  `FootIsa` packages these; the aliased machine, the access condition and the
simulation follow once for every such instruction set (AArch64: `ArmAlias.lean`, RISC-V:
`RiscvAlias.lean`).
-/
namespace Keccaktree.Asm
open X86

/-- An instruction set with memory footprints (concrete states). -/
structure FootIsa where
  Instr : Type
  nop : Instr
  exec : Array (BitVec 64) → Instr → State (BitVec 64) → State (BitVec 64)
  reads : State (BitVec 64) → Instr → List (Region × Int)
  writes : State (BitVec 64) → Instr → List (Region × Int)
  writes_wm : ∀ (s : State (BitVec 64)) (m' : Region → Int → BitVec 64) (i : Instr),
    writes ({ s with mem := m' } : State (BitVec 64)) i = writes s i
  exec_local : ∀ (rodata : Array (BitVec 64)) (m' : Region → Int → BitVec 64) (i : Instr) (s : State (BitVec 64)),
    s.halted = false → (exec rodata i s).err = false → Agree m' (reads s i) s →
      exec rodata i ({ s with mem := m' } : State (BitVec 64)) = rebase (writes s i) m' (exec rodata i s)
  exec_halted : ∀ (rodata : Array (BitVec 64)) (i : Instr) (s : State (BitVec 64)), s.halted = true → exec rodata i s = s

namespace FootIsa
variable (I : FootIsa)

theorem exec_frame (rodata : Array (BitVec 64)) (i : I.Instr) (s : State (BitVec 64)) (hh : s.halted = false)
    (hne : (I.exec rodata i s).err = false) (r : Region) (q : Int) (hw : (r, q) ∉ I.writes s i) :
    (I.exec rodata i s).mem r q = s.mem r q := by
  have h := I.exec_local rodata s.mem i s hh hne (fun _ _ => rfl)
  have h2 : ({ s with mem := s.mem } : State (BitVec 64)) = s := rfl
  rw [h2] at h
  rw [h]; simp only [rebase, hw, ↓reduceIte]

/-- One step of the aliased machine. -/
def execAl (rodata : Array (BitVec 64)) (i : I.Instr) (t : State (BitVec 64)) : State (BitVec 64) :=
  if t.halted then t else
  let s := { t with mem := joinMem t.mem }
  let s' := I.exec rodata i s
  { s' with mem := fun r q => if r = rInput ∨ r = rOutput then
      (if (rOutput, q) ∈ I.writes s i then s'.mem rOutput q else s'.mem rInput q) else s'.mem r q }

/-- The aliased machine's fetch-execute loop. -/
def runAl (rodata : Array (BitVec 64)) (prog : Array I.Instr) : Nat → State (BitVec 64) → State (BitVec 64)
  | 0, t => t
  | n + 1, t => if t.halted then t else runAl rodata prog n (I.execAl rodata (prog.getD t.pc I.nop) t)

/-- The separate-region run. -/
def run (rodata : Array (BitVec 64)) (prog : Array I.Instr) : Nat → State (BitVec 64) → State (BitVec 64)
  | 0, s => s
  | n + 1, s => if s.halted then s else run rodata prog n (I.exec rodata (prog.getD s.pc I.nop) s)

def AccessOk (B : Int) (s : State (BitVec 64)) (i : I.Instr) : Prop :=
  (∀ c ∈ I.reads s i, c.1 = rInput → B ≤ c.2) ∧ (∀ c ∈ I.writes s i, c.1 ≠ rInput)

def bumpB (B : Int) (s : State (BitVec 64)) (i : I.Instr) : Int :=
  (I.writes s i).foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) B

def AccessRun (rodata : Array (BitVec 64)) (prog : Array I.Instr) : Nat → Int → Int → State (BitVec 64) → Prop
  | 0, B, Bf, _ => B ≤ Bf
  | n + 1, B, Bf, s => if s.halted then B ≤ Bf else
      ((I.exec rodata (prog.getD s.pc I.nop) s).err = false ∧ I.AccessOk B s (prog.getD s.pc I.nop) ∧
        AccessRun rodata prog n (I.bumpB B s (prog.getD s.pc I.nop)) Bf (I.exec rodata (prog.getD s.pc I.nop) s))

set_option maxHeartbeats 4000000 in
theorem sim_step (rodata : Array (BitVec 64)) (i : I.Instr) (s t : State (BitVec 64)) (B : Int)
    (hS : Sim s t) (hC : Clean B s) (hA : I.AccessOk B s i) (hh : s.halted = false)
    (hne : (I.exec rodata i s).err = false) :
    Sim (I.exec rodata i s) (I.execAl rodata i t) ∧ Clean (I.bumpB B s i) (I.exec rodata i s) := by
  have hth : t.halted = false := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hh
  have hmIn := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmOt := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hag : Agree (joinMem t.mem) (I.reads s i) s := by
    rintro ⟨r, q⟩ hc
    simp only [joinMem]
    by_cases h2 : r = rOutput
    · subst h2; simp only [↓reduceIte]; exact hmIn q
    · simp only [h2, ↓reduceIte]
      by_cases h1 : r = rInput
      · subst h1; rw [hmIn q]; exact hC q (hA.1 _ hc rfl)
      · exact hmOt r q h1 h2
  have hloc := I.exec_local rodata (joinMem t.mem) i s hh hne hag
  have hfr := I.exec_frame rodata i s hh hne
  have hj : ({ t with mem := joinMem t.mem } : State (BitVec 64)) = { s with mem := joinMem t.mem } := joined_eq s t hS
  have hex : I.execAl rodata i t = { I.exec rodata i ({ s with mem := joinMem t.mem } : State (BitVec 64)) with
      mem := fun r q => if r = rInput ∨ r = rOutput then
        (if (rOutput, q) ∈ I.writes ({ s with mem := joinMem t.mem } : State (BitVec 64)) i
          then (I.exec rodata i ({ s with mem := joinMem t.mem } : State (BitVec 64))).mem rOutput q
          else (I.exec rodata i ({ s with mem := joinMem t.mem } : State (BitVec 64))).mem rInput q)
        else (I.exec rodata i ({ s with mem := joinMem t.mem } : State (BitVec 64))).mem r q } := by
    have hT : (t.halted = true) = False := by simp [hth]
    simp only [execAl, hT, ↓reduceIte]; rw [hj]
  rw [hex, hloc]; simp only [I.writes_wm]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -⟩ := hS
  have hst : ∀ q, (if (rOutput, q) ∈ I.writes s i then (rebase (I.writes s i) (joinMem t.mem) (I.exec rodata i s)).mem rOutput q
      else (rebase (I.writes s i) (joinMem t.mem) (I.exec rodata i s)).mem rInput q) = (I.exec rodata i s).mem rOutput q := by
    intro q
    by_cases hw : (rOutput, q) ∈ I.writes s i
    · simp only [hw, ↓reduceIte, rebase]
    · have hw1 : (rInput, q) ∉ I.writes s i := fun h => hA.2 _ h rfl
      simp only [hw, hw1, ↓reduceIte, rebase, joinMem, show rInput ≠ rOutput by decide]
      rw [hmIn q, hfr rOutput q hw]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_, fun q => ?_, ?_⟩, ?_⟩
  · simp only [true_or, ↓reduceIte]; exact hst q
  · simp only [or_true, ↓reduceIte]; exact hst q
  · intro r q hr1 hr2
    simp only [hr1, hr2, or_self, ↓reduceIte, rebase]
    split
    · rfl
    · rename_i hw; simp only [joinMem, hr2, ↓reduceIte]; rw [hmOt r q hr1 hr2, hfr r q hw]
  · intro q hq
    have hw2 : (rOutput, q) ∉ I.writes s i := fun h => by
      have : q < I.bumpB B s i := X86.foldB_out (I.writes s i) B q h
      omega
    have hw1 : (rInput, q) ∉ I.writes s i := fun h => hA.2 _ h rfl
    rw [hfr _ _ hw2, hfr _ _ hw1]
    exact hC q (Int.le_trans (X86.foldB_ge (I.writes s i) B) hq)

/-- **The simulation along a run** (any instruction set with footprints). -/
theorem sim_run (rodata : Array (BitVec 64)) (prog : Array I.Instr) :
    ∀ (n : Nat) (B Bf : Int) (s t : State (BitVec 64)), I.AccessRun rodata prog n B Bf s → Sim s t → Clean B s →
      Sim (I.run rodata prog n s) (I.runAl rodata prog n t) ∧ Clean Bf (I.run rodata prog n s) ∧
      ∀ q, (I.run rodata prog n s).mem rInput q = s.mem rInput q := by
  intro n
  induction n with
  | zero => intro B Bf s t hA hS hC; exact ⟨hS, clean_mono _ _ _ hA hC, fun _ => rfl⟩
  | succ n ih =>
    intro B Bf s t hA hS hC
    have hth : t.halted = s.halted := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
    have htpc : t.pc = s.pc := hS.2.2.2.2.2.2.2.2.2.1
    cases hh : s.halted
    · simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte] at hA
      obtain ⟨hne, hok, hA⟩ := hA
      have hst := I.sim_step rodata (prog.getD s.pc I.nop) s t B hS hC hok hh hne
      simp only [run, runAl, hth, hh, htpc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ hA hst.1 hst.2
      refine ⟨h1, h2, fun q => (h3 q).trans ?_⟩
      exact I.exec_frame rodata _ s hh hne rInput q (fun hw => hok.2 _ hw rfl)
    · simp only [AccessRun, hh, ↓reduceIte] at hA
      simp only [run, runAl, hth, hh, ↓reduceIte]; exact ⟨hS, clean_mono _ _ _ hA hC, fun _ => by simp⟩

end FootIsa
end Keccaktree.Asm
