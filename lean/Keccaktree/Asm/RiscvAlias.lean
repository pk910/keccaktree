import Keccaktree.Asm.AliasGen
import Keccaktree.Asm.ArmAlias
import Keccaktree.Asm.RiscvFoot
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# RISC-V read footprints and memory locality (in-place hashing)

`Riscv.reads`: the cells a RISC-V step loads (`ld`: one word, `vlseg`: `nf·vl` words; the byte copies
of misaligned buffers: `lbu` and `sb` the word holding the byte (`sb` inserts it), `vle8` the `vl/8` words
(misaligned: the `vl/8 + 1` words it straddles), `vse8` misaligned the `vl/8 + 1` words it rewrites (its
edge words keep their other bytes)); every other instruction loads nothing (each case explicit);
`exec_local` as for x86; `footIsa vlmax`: the instruction set with footprints (`AliasGen.lean`).
-/
namespace Keccaktree.Asm.Riscv
open Keccaktree.Asm
open Keccaktree.Asm.X86 (State rebase Agree rebase_nil)
open Keccaktree.Asm.Arm (gx setX withX addr withAddr)
open LaneOps

variable {α : Type} [LaneOps α]

def reads (s : State α) : Instr → List (Region × Int)
  | .ld _ base off => match addr s base off with
    | some a => storeCells a 1
    | none => []
  | .vlseg _ base nf => match addr s base 0 with
    | some a => storeCells a (nf * s.vl)
    | none => []
  | .lbu _ base off => match addr s base off with
    | some a => storeCells (wordOf a) 1
    | none => []
  | .sb _ base off => match addr s base off with
    | some a => storeCells (wordOf a) 1
    | none => []
  | .vle8 _ base => match addr s base 0 with
    | some a => if byteOf a = 0 then storeCells a (s.vl / 8) else storeCells (wordOf a) (s.vl / 8 + 1)
    | none => []
  | .vse8 _ base => match addr s base 0 with
    | some a => if byteOf a = 0 then [] else storeCells (wordOf a) (s.vl / 8 + 1)
    | none => []
  | .op _ _ _ _ | .opi _ _ _ _ | .li _ _ | .mv _ _ | .not _ _ | .lea _ _ | .sd _ _ _ | .br _ _ _ _ | .j _
  | .ret | .nop | .unsupported _ | .vsetvli _ _ | .vsetvlie8 _ _ _ | .vop _ _ _ _ | .vnot _ _
  | .vshifti _ _ _ _ | .vshiftx _ _ _ _ | .vxorx _ _ _ | .vmvi _ _ | .vmvx _ _ | .vmvv _ _ | .vsseg _ _ _ => []

theorem rebase_agree {m' : Region → Int → α} (W : List (Region × Int)) (X : State α)
    (h : ∀ c ∈ W, m' c.1 c.2 = X.mem c.1 c.2) : rebase W m' X = { X with mem := m' } := by
  simp only [rebase]
  congr 1
  funext r q
  split
  · rename_i hq; exact (h (r, q) hq).symm
  · rfl

theorem agree_sub {m' : Region → Int → α} {L L' : List (Region × Int)} {s : State α} (h : Agree m' L s)
    (hs : ∀ c ∈ L', c ∈ L) : Agree m' L' s := fun c hc => h c (hs c hc)

theorem setGroup_wm (vlmax : Nat) (s : State α) (m' : Region → Int → α) (d : Nat) (ws : List α) (n : Nat) :
    setGroup vlmax ({ s with mem := m' } : State α) d ws n = { setGroup vlmax s d ws n with mem := m' } := by
  unfold setGroup
  generalize List.range ((n + vlmax - 1) / vlmax) = l
  induction l generalizing s with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih (setLanes s (d + x) (min vlmax (n - x * vlmax)) fun l => ws.getD (x * vlmax + l) (const 0))

theorem loadBytes_loc (rodata : Array (BitVec 64)) (m' : Region → Int → α) (s : State α) (a : Addr) (n : Nat)
    (h : Agree m' (if byteOf a = 0 then storeCells a n else storeCells (wordOf a) (n + 1)) s) :
    loadBytes rodata ({ s with mem := m' } : State α) a n = loadBytes rodata s a n := by
  unfold loadBytes
  split
  · rename_i hk; rw [if_pos hk] at h; rw [X86.loadWords_loc rodata m' s a n h]
  · rename_i hk; rw [if_neg hk] at h; rw [X86.loadWords_loc rodata m' s _ _ h]

theorem storeCells_last (a : Addr) (n : Nat) :
    ∀ c ∈ storeCells ⟨a.region, (wordOf a).off + 8 * n⟩ 1, c ∈ storeCells (wordOf a) (n + 1) := by
  intro c hc
  simp only [storeCells, List.mem_map, List.mem_range] at hc ⊢
  obtain ⟨i, hi, rfl⟩ := hc
  refine ⟨n, by omega, ?_⟩
  have : i = 0 := by omega
  subst this
  have : ((wordOf a).off + 8 * (n : Int)) / 8 = (wordOf a).off / 8 + n := by omega
  simp only [Prod.mk.injEq, this]
  exact ⟨rfl, by simp⟩

theorem storeCells_first (a : Addr) (n : Nat) :
    ∀ c ∈ storeCells (wordOf a) 1, c ∈ storeCells (wordOf a) (n + 1) := by
  intro c hc
  simp only [storeCells, List.mem_map, List.mem_range] at hc ⊢
  obtain ⟨i, hi, rfl⟩ := hc
  exact ⟨i, by omega, rfl⟩

theorem storeBytes_loc (rodata : Array (BitVec 64)) (m' : Region → Int → α) (s : State α) (a : Addr)
    (vs : List α) (n : Nat) (hn : vs.length = n)
    (h : byteOf a ≠ 0 → Agree m' (storeCells (wordOf a) (n + 1)) s) :
    storeBytes rodata ({ s with mem := m' } : State α) a vs n =
      (storeBytes rodata s a vs n).map
        (rebase (if byteOf a = 0 then storeCells a n else storeCells (wordOf a) (n + 1)) m') := by
  unfold storeBytes
  split
  · rename_i hk
    try simp only [hk, ↓reduceIte]
    rw [X86.storeWords_loc m' s a vs, hn]
  · rename_i hk
    try simp only [hk, ↓reduceIte]
    have hA := h hk
    rw [X86.loadWords_loc rodata m' s (wordOf a) 1 (agree_sub hA (storeCells_first a n)),
      X86.loadWords_loc rodata m' s _ 1 (agree_sub hA (storeCells_last a n))]
    split
    · rw [X86.storeWords_loc m' s (wordOf a)]
      simp only [splitWords, List.length_map, List.length_range]
    · rfl

@[simp] theorem getR_wm (s : State α) (m' : Region → Int → α) (n : Nat) :
    getR ({ s with mem := m' } : State α) n = getR s n := rfl
@[simp] theorem lane_wm (s : State α) (m' : Region → Int → α) (n l : Nat) :
    lane ({ s with mem := m' } : State α) n l = lane s n l := rfl
@[simp] theorem vl_wm (s : State α) (m' : Region → Int → α) : ({ s with mem := m' } : State α).vl = s.vl := rfl

theorem setActive_wm (s : State α) (m' : Region → Int → α) (d : Nat) (f : Nat → α) :
    setActive ({ s with mem := m' } : State α) d f = { setActive s d f with mem := m' } := rfl

theorem foldl_setActive_wm (l : List Nat) (g : Nat → Nat → α) (d : Nat) (s : State α) (m' : Region → Int → α) :
    l.foldl (fun s' f => setActive s' (d + f) (g f)) ({ s with mem := m' } : State α) =
      { l.foldl (fun s' f => setActive s' (d + f) (g f)) s with mem := m' } := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; rw [setActive_wm, ih]

syntax "wm_close''" : tactic
macro_rules
  | `(tactic| wm_close'') => `(tactic| first
    | rfl
    | (split <;> rename_i h <;> (try simp only [h, ↓reduceIte]) <;> wm_close'')
    | (simp only [getR_wm, lane_wm, vl_wm, X86.getGD_wm, X86.getV_wm, Arm.gx_wm', withX, setR] <;> wm_close''))

set_option maxHeartbeats 8000000 in
/-- **Memory locality of a RISC-V step** (as `X86.exec_local`). -/
theorem exec_local (vlmax : Nat) (rodata : Array (BitVec 64)) (m' : Region → Int → α) (i : Instr) (s : State α)
    (hh : s.halted = false) (hne : (exec vlmax rodata i s).err = false) (hag : Agree m' (reads s i) s) :
    exec vlmax rodata i ({ s with mem := m' } : State α) = rebase (writes s i) m' (exec vlmax rodata i s) := by
  have hT : (s.halted = true) = False := by simp [hh]
  cases i with
  | op d a b k =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | opi d a k imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | li d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | mv d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | not d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | lea d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | ld d base off =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    simp only [withAddr, Arm.addr_wm] at hne ⊢
    rcases ha : addr s base off with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.loadWords_loc rodata m' s a _ (by simpa [reads, ha] using hag), rebase_nil]
      wm_close''
  | sd src base off =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [withAddr, Arm.addr_wm, writes] at hne ⊢
    rcases ha : addr s base off with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.storeWords_loc m' s a]
      rcases hs : s.storeWords a [getR s src] with _ | s'
      · simp [hs, State.fail] at hne
      · simp only [hs, Option.map_some, getR_wm]; rfl
  | br c a b t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | j t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | ret =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | nop =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | unsupported name =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vsetvli d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vop d a b k =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vnot d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vshifti d a k imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vshiftx d a k x =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vxorx d a x =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vmvi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vmvx d x =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vmvv d a =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | vlseg d base nf =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    simp only [withAddr, Arm.addr_wm] at hne ⊢
    rcases ha : addr s base 0 with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.loadWords_loc rodata m' s a _ (by simpa [reads, ha] using hag), rebase_nil]
      rcases hl : s.loadWords rodata a (nf * s.vl) with _ | ws
      · rfl
      · simp only []
        rw [foldl_setActive_wm _ (fun f l => ws.getD (nf * l + f) (LaneOps.const 0))]; rfl
  | vsseg src base nf =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [withAddr, Arm.addr_wm, writes] at hne ⊢
    rcases ha : addr s base 0 with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      simp only [lane_wm, vl_wm]
      rw [X86.storeWords_loc m' s a]
      rcases hs : s.storeWords a ((List.range (nf * s.vl)).map fun q => lane s (src + q % nf) (q / nf)) with _ | s'
      · simp [hs, State.fail] at hne
      · simp only [hs, Option.map_some, List.length_map, List.length_range]; rfl
  | vsetvlie8 d a lmul =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close''
  | lbu d base off =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    simp only [withAddr, Arm.addr_wm] at hne ⊢
    rcases ha : addr s base off with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.loadWords_loc rodata m' s (wordOf a) 1 (by simp only [reads, ha] at hag; exact hag), rebase_nil]
      wm_close''
  | sb src base off =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [withAddr, Arm.addr_wm, writes] at hne ⊢
    rcases ha : addr s base off with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha] at hne ⊢
      rw [X86.loadWords_loc rodata m' s (wordOf a) 1 (by simp only [reads, ha] at hag; exact hag)]
      rcases hl : s.loadWords rodata (wordOf a) 1 with _ | l
      · simp [hl, State.fail] at hne
      · rcases l with _ | ⟨w, _ | ⟨w2, l⟩⟩
        · simp [hl, State.fail] at hne
        · simp only [hl, getR_wm] at hne ⊢
          rw [X86.storeWords_loc m' s (wordOf a)]
          rcases hs : s.storeWords (wordOf a) [insByte w (getR s src) (byteOf a)] with _ | s'
          · simp [hs, State.fail] at hne
          · simp only [hs, Option.map_some]; rfl
        · simp [hl, State.fail] at hne
  | vle8 d base =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    simp only [withAddr, Arm.addr_wm] at hne ⊢
    rcases ha : addr s base 0 with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha, vl_wm] at hne ⊢
      rw [loadBytes_loc rodata m' s a _ (by simp only [reads, ha] at hag; exact hag), rebase_nil]
      split
      · split
        · rw [setGroup_wm]; rfl
        · rfl
      · rfl
  | vse8 src base =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [withAddr, Arm.addr_wm] at hne ⊢
    rcases ha : addr s base 0 with _ | a
    · simp [ha, State.fail] at hne
    · simp only [ha, vl_wm] at hne ⊢
      have hr : byteOf a ≠ 0 → Agree m' (storeCells (wordOf a) (s.vl / 8 + 1)) s := by
        intro hk; simp only [reads, ha, hk, ↓reduceIte] at hag; exact hag
      by_cases hc : s.vl % 8 = 0 ∧ 0 < vlmax
      · simp only [hc, and_self, ↓reduceIte] at hne ⊢
        by_cases h0 : s.vl = 0
        · rw [if_pos h0] at hne; rw [if_pos h0, if_pos h0]
          rw [rebase_agree]
          · rfl
          · intro c hc'
            simp only [writes, ha] at hc'
            by_cases hk : byteOf a = 0
            · simp [hk, h0, storeCells] at hc'
            · simp only [hk, ↓reduceIte] at hc'
              exact hr hk c hc'
        · rw [if_neg h0] at hne; rw [if_neg h0, if_neg h0]
          rw [show (List.range (s.vl / 8)).map (fun j => groupWord vlmax ({ s with mem := m' } : State α) src j) =
              (List.range (s.vl / 8)).map (fun j => groupWord vlmax s src j) from rfl,
            storeBytes_loc rodata m' s a _ _ (by simp) hr]
          rcases hs : storeBytes rodata s a ((List.range (s.vl / 8)).map fun j => groupWord vlmax s src j) (s.vl / 8)
            with _ | s'
          · simp [hs, State.fail] at hne
          · simp only [hs, Option.map_some, writes, ha]; rfl
      · simp only [hc, ↓reduceIte, State.fail] at hne
        simp at hne

theorem writes_wm (s : State (BitVec 64)) (m' : Region → Int → BitVec 64) (i : Instr) :
    writes ({ s with mem := m' } : State (BitVec 64)) i = writes s i := by
  cases i <;> rfl

/-- **The RISC-V instruction set (VLEN = 64·`vlmax`) with footprints.** -/
def footIsa (vlmax : Nat) : FootIsa where
  Instr := Instr
  nop := .nop
  exec := exec vlmax
  reads := reads
  writes := writes
  writes_wm := writes_wm
  exec_local := fun rodata m' i s hh hne hag => exec_local vlmax rodata m' i s hh hne hag
  exec_halted := fun rodata i s h => by simp [exec, h]

end Keccaktree.Asm.Riscv
