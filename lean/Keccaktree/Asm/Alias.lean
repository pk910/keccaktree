import Keccaktree.Asm.AliasBase
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# In-place hashing: aliased input and output (x86)

`exec_local` (all x86 instructions), the x86 aliased machine (`execAl`, `runAl`), the access condition
(`AccessRun`, `accessCheck`) and the simulation (`sim_step`, `sim_run`).  Base definitions: `AliasBase.lean`.
-/
namespace Keccaktree.Asm
open X86

variable {α : Type} [LaneOps α]

namespace X86
section exec_local
variable (rodata : Array (BitVec 64)) (m' : Region → Int → α)

set_option maxHeartbeats 8000000 in
/-- **Memory locality of a step**: run on a state whose memory `m'` agrees with `s` on the cells the
instruction reads, a non-failing step computes the same registers, flags and stored words, and the
cells it does not store to keep `m'`. -/
theorem exec_local (i : Instr) (s : State α) (hh : s.halted = false) (hne : (exec rodata i s).err = false)
    (hag : Agree m' (reads s i) s) :
    exec rodata i ({ s with mem := m' } : State α) = rebase (writes s i) m' (exec rodata i s) := by
  have hT : (s.halted = true) = False := by simp [hh]
  cases i with
  | vmov lanes dst src mask =>
    cases mask <;> (
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes src [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close)
  | vstore lanes m src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withStore_loc m' s ad _ _ _ _ hne2; intro _ _ _
      simp only [List.length_take]; rfl
  | vpxor lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpand lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpandn lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpor lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpaddq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpsllq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | vpsrlq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | vprolq lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | vpsllvq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpsrlvq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpternlogq lanes d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpshufb lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpshufd lanes d a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | vpblendd lanes d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpalignr lanes d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpunpcklqdq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpunpckhqdq lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vperm2i128 d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s 4 b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vinserti128 d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s 2 b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vextracti128 m a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withStore_loc m' s ad _ _ _ _ hne2; intro _ _ _
      simp only [lane128, List.length_cons, List.length_nil]; rfl
  | vshufi64x2 lanes d a b imm =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | vpermt2q lanes d a b =>
    simp only [exec, binop, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withSrc_loc rodata m' s lanes b [] _ _ hag hne; intro _ _ _; rw [rebase_nil]; wm_close
  | kmovw k m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro ad had hne2
    rw [read_loc rodata m' s ad.region (ad.off / 8) (fun _ => by
      have := hag (ad.region, ad.off / 8 + ((0 : Nat) : Int)) (by simp [reads, memCells, had, storeCells])
      simpa using this)]
    rw [rebase_nil]; wm_close
  | vzeroupper =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | mov d src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | xchg a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | movi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | lea d m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | add d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | sub d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | andi d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | shl d imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | dec d =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s d [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | xorz d =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | cmpi a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s a [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | cmpr a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s a [] _ _ hne; intro _ _ hne2
    apply withX_loc m' s b [] _ _ hne2; intro _ _ _; rw [rebase_nil]; wm_close
  | cmpm m b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro ad had hne2
    apply withLoad_loc rodata m' s ad 1 [] _ _ (by simpa [reads, memCells, had] using hag) hne2
    intro ws _ hne3
    split
    · rename_i v hv
      simp only [hv] at hne3
      apply withX_loc m' s b [] _ _ hne3; intro _ _ _; rw [rebase_nil]; wm_close
    · rename_i hv; simp only [hv] at hne3; simp [State.fail] at hne3
  | cmprm a m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro ad had hne2
    apply withLoad_loc rodata m' s ad 1 [] _ _ (by simpa [reads, memCells, had] using hag) hne2
    intro ws _ hne3
    split
    · rename_i v hv
      simp only [hv] at hne3
      apply withX_loc m' s a [] _ _ hne3; intro _ _ _; rw [rebase_nil]; wm_close
    · rename_i hv; simp only [hv] at hne3; simp [State.fail] at hne3
  | test a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s a [] _ _ hne; intro _ _ hne2
    apply withX_loc m' s b [] _ _ hne2; intro _ _ _; rw [rebase_nil]; wm_close
  | bt a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    show (match LaneOps.asConst (s.getGD a) with | some w => withX ({ s with mem := m' } : State α) b _ | none => _) = _
    rcases hc : LaneOps.asConst (s.getGD a) with _ | w
    · simp only [hc] at hne; simp [State.fail] at hne
    · simp only [hc] at hne ⊢
      apply withX_loc m' s b [] _ _ hne; intro _ _ _; rw [rebase_nil]; wm_close
  | btc a imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | alu op d b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply readG_loc rodata m' s b [] _ _ hag hne; intro _ _; rw [rebase_nil]; wm_close
  | andn d a b =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply readG_loc rodata m' s b [] _ _ hag hne; intro _ _; rw [rebase_nil]; wm_close
  | rorx d b imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply readG_loc rodata m' s b [] _ _ hag hne; intro _ _; rw [rebase_nil]; wm_close
  | xorm m src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withLoad_loc rodata m' s ad 1 _ _ _ (by simpa [reads, memCells, hm] using hag) hne2; intro ws _ hne3
      apply withStore_loc m' s ad _ _ _ _ hne3 <;> intro _ _ _ <;> rfl
  | storeqi m imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withStore_loc m' s ad _ _ _ _ hne2 <;> intro _ _ _ <;> rfl
  | addm m imm =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withLoad_loc rodata m' s ad 1 _ _ _ (by simpa [reads, memCells, hm] using hag) hne2; intro ws _ hne3
      apply withStore_loc m' s ad _ _ _ _ hne3 <;> intro _ _ _ <;> rfl
  | decm m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withLoad_loc rodata m' s ad 1 _ _ _ (by simpa [reads, memCells, hm] using hag) hne2; intro ws _ hne3
      split
      · rename_i v hv
        simp only [hv] at hne3
        split
        · rename_i hr; simp only [hr, ↓reduceIte] at hne3 ⊢
          apply withStore_loc m' s ad _ _ _ _ hne3 <;> intro _ _ _ <;> rfl
        · rename_i hr; simp only [hr, ↓reduceIte] at hne3; simp [State.fail] at hne3
      · rename_i hv; simp only [hv] at hne3; simp [State.fail] at hne3
  | jcc c t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | jmp t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | jcct c name =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | call t =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hsp : gx s 4 with _ | sp
    · simp only [withX, gx_loc, hsp, fail_err] at hne; simp [State.fail] at hne
    · simp only [hsp]
      apply withX_loc m' s 4 _ _ _ hne; intro sp' hsp' hne2
      rw [hsp] at hsp'; cases hsp'
      apply withStore_loc m' s _ _ _ _ _ hne2 <;> intro _ _ _ <;> rfl
  | ret =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    by_cases hd : s.depth = 0
    · simp only [hd, ↓reduceIte] at hne ⊢ <;> rw [rebase_nil] <;> rfl
    · simp only [show ({ s with mem := m' } : State α).depth = s.depth from rfl, hd, ↓reduceIte] at hne ⊢
      apply withX_loc m' s 4 [] _ _ hne; intro sp hsp hne2
      apply withLoad_loc rodata m' s sp 1 [] _ _ (by simpa [reads, hd, hsp] using hag) hne2
      intro ws _ hne3; rw [rebase_nil]; wm_close
  | push src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hsp : gx s 4 with _ | sp
    · simp only [withX, gx_loc, hsp, fail_err] at hne; simp [State.fail] at hne
    · simp only [hsp]
      apply withX_loc m' s 4 _ _ _ hne; intro sp' hsp' hne2
      rw [hsp] at hsp'; cases hsp'
      apply withStore_loc m' s _ _ _ _ _ hne2 <;> intro _ _ _ <;> rfl
  | pop d =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withX_loc m' s 4 [] _ _ hne; intro sp hsp hne2
    apply withLoad_loc rodata m' s sp 1 [] _ _ (by simpa [reads, hsp] using hag) hne2
    intro _ _ _; rw [rebase_nil]; wm_close
  | storeq m src =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hm : memAddr? s m with _ | ad
    · simp only [withMem, memAddr?_loc, hm, fail_err] at hne; simp [State.fail] at hne
    · simp only [hm]
      apply withMem_loc m' s m _ _ _ hne; intro ad' had' hne2
      rw [hm] at had'; cases had'
      apply withStore_loc m' s ad _ _ _ _ hne2 <;> intro _ _ _ <;> rfl
  | loadq d m =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢; rw [show writes s _ = [] from rfl]
    apply withMem_loc m' s m [] _ _ hne; intro ad had hne2
    apply withLoad_loc rodata m' s ad 1 [] _ _ (by simpa [reads, memCells, had] using hag) hne2
    intro _ _ _; rw [rebase_nil]; wm_close
  | repmovsb =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢
    simp only [writes]
    rcases hn : gx s 1 with _ | n
    · simp only [withX, gx_loc, hn, fail_err] at hne; simp [State.fail] at hne
    rcases hsrc : gx s 6 with _ | src
    · simp only [withX, gx_loc, hn, hsrc, fail_err] at hne; simp [State.fail] at hne
    rcases hdst : gx s 7 with _ | dst
    · simp only [withX, gx_loc, hn, hsrc, hdst, fail_err] at hne; simp [State.fail] at hne
    simp only [withX, gx_loc, hn, hsrc, hdst] at hne ⊢
    simp only [repBody] at hne ⊢
    split
    · rename_i hc
      simp only [hc, and_self, ↓reduceIte] at hne
      apply withLoad_loc rodata m' s src _ _ _ _ (by simpa [reads, hn, hsrc] using hag) hne; intro vs hvs hne3
      have hlen : vs.length = n.off.toNat / 8 := by
        simp only [State.loadWords] at hvs; split at hvs
        · cases hvs; simp
        · cases hvs
      apply withStore_loc m' s dst vs _ _ _ hne3; intro _ _ _; rw [hlen]; rfl
    · rename_i hc; simp only [hc, ↓reduceIte] at hne; simp [State.fail] at hne
  | tailcall name =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close
  | nop =>
    simp only [exec, hT, ↓reduceIte] at hne ⊢ <;> rw [show writes s _ = [] from rfl, rebase_nil] <;> wm_close

end exec_local

end X86
end Keccaktree.Asm

/-! ## The aliased machine and the simulation -/
namespace Keccaktree.Asm
open X86
namespace X86
variable {α : Type} [LaneOps α]

/-- The storage after a step on the joined view `s` with result `s'`: a word stored through the output
pointer, else the input region's word; mirrored into both regions (they are one buffer). -/
def mirror (s s' : State α) (i : Instr) : Region → Int → α :=
  fun r q => if r = rInput ∨ r = rOutput then
      (if (rOutput, q) ∈ writes s i then s'.mem rOutput q else s'.mem rInput q)
    else s'.mem r q

/-- **One step of the aliased machine** (`keccaktree_hash(buf, buf, n)`): the step runs on the joined
view (loads through either pointer see the storage, region 1), and the words it stores through the
output pointer land in the storage; regions 1 and 2 both show the storage. -/
def execAl (rodata : Array (BitVec 64)) (i : Instr) (t : State α) : State α :=
  if t.halted then t else
  let s := { t with mem := joinMem t.mem }
  let s' := exec rodata i s
  { s' with mem := mirror s s' i }

/-- The aliased machine's fetch-execute loop. -/
def runAl (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → State α → State α
  | 0, t => t
  | n + 1, t => if t.halted then t else runAl rodata prog n (execAl rodata (prog.getD t.pc .nop) t)

/-- What a step of the separate-region run must respect for the aliased run to follow it: it loads
input words only at or above `B` (where the storage still holds the input), and stores no input word. -/
def AccessOk (B : Int) (s : State α) (i : Instr) : Prop :=
  (∀ c ∈ reads s i, c.1 = rInput → B ≤ c.2) ∧ (∀ c ∈ writes s i, c.1 ≠ rInput)

/-- The bound after a step: above every output word stored so far. -/
def bumpB (B : Int) (s : State α) (i : Instr) : Int :=
  (writes s i).foldl (fun b c => if c.1 = rOutput then max b (c.2 + 1) else b) B

theorem bumpB_ge (B : Int) (s : State α) (i : Instr) : B ≤ bumpB B s i := foldB_ge _ _

theorem bumpB_out (B : Int) (s : State α) (i : Instr) (q : Int) (hq : (rOutput, q) ∈ writes s i) : q < bumpB B s i :=
  foldB_out _ _ _ hq

theorem writes_wm (s : State α) (m' : Region → Int → α) (i : Instr) :
    writes ({ s with mem := m' } : State α) i = writes s i := by
  cases i <;> rfl

theorem execAl_eq (rodata : Array (BitVec 64)) (i : Instr) (t : State α) (hth : t.halted = false) :
    execAl rodata i t =
      { exec rodata i ({ t with mem := joinMem t.mem } : State α) with
        mem := mirror ({ t with mem := joinMem t.mem } : State α) (exec rodata i ({ t with mem := joinMem t.mem } : State α)) i } := by
  simp only [execAl, hth, Bool.false_eq_true, ↓reduceIte]

set_option maxHeartbeats 4000000 in
/-- **One step of the simulation**: if the separate-region step loads input words only where the
output region still holds the input, the aliased step follows it. -/
theorem sim_step (rodata : Array (BitVec 64)) (i : Instr) (s t : State α) (B : Int)
    (hS : Sim s t) (hC : Clean B s) (hA : AccessOk B s i) (hh : s.halted = false)
    (hne : (exec rodata i s).err = false) :
    Sim (exec rodata i s) (execAl rodata i t) ∧ Clean (bumpB B s i) (exec rodata i s) := by
  have hth : t.halted = false := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hh
  have hmIn := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmOt := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hag : Agree (joinMem t.mem) (reads s i) s := by
    rintro ⟨r, q⟩ hc
    simp only [joinMem]
    by_cases h2 : r = rOutput
    · subst h2; simp only [↓reduceIte]; exact hmIn q
    · simp only [h2, ↓reduceIte]
      by_cases h1 : r = rInput
      · subst h1; rw [hmIn q]; exact hC q (hA.1 _ hc rfl)
      · exact hmOt r q h1 h2
  have hloc := exec_local rodata (joinMem t.mem) i s hh hne hag
  have hfr := exec_frame rodata i s hne
  rw [execAl_eq rodata i t hth, joined_eq s t hS, hloc]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -⟩ := hS
  have hst : ∀ q, mirror ({ s with mem := joinMem t.mem } : State α) (rebase (writes s i) (joinMem t.mem) (exec rodata i s)) i rInput q =
      (exec rodata i s).mem rOutput q ∧
      mirror ({ s with mem := joinMem t.mem } : State α) (rebase (writes s i) (joinMem t.mem) (exec rodata i s)) i rOutput q =
      (exec rodata i s).mem rOutput q := by
    intro q
    simp only [mirror, writes_wm, true_or, or_true, ↓reduceIte, rebase]
    by_cases hw : (rOutput, q) ∈ writes s i
    · simp only [hw, ↓reduceIte, and_self]
    · have hw1 : (rInput, q) ∉ writes s i := fun h => hA.2 _ h rfl
      simp only [hw, hw1, ↓reduceIte, joinMem, show rInput ≠ rOutput by decide]
      rw [hmIn q, hfr rOutput q hw]; simp
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => (hst q).1, fun q => (hst q).2, ?_⟩, ?_⟩
  · intro r q hr1 hr2
    simp only [mirror, hr1, hr2, or_self, ↓reduceIte, rebase]
    split
    · rfl
    · rename_i hw; simp only [joinMem, hr2, ↓reduceIte]; rw [hmOt r q hr1 hr2, hfr r q hw]
  · intro q hq
    have hw2 : (rOutput, q) ∉ writes s i := fun h => by have := bumpB_out B s i q h; omega
    have hw1 : (rInput, q) ∉ writes s i := fun h => hA.2 _ h rfl
    rw [hfr _ _ hw2, hfr _ _ hw1]
    exact hC q (Int.le_trans (bumpB_ge B s i) hq)

/-- The access condition along a separate-region run of `n` steps from `s`, starting at bound `B`;
when the run stops (halted, or `n` steps done) the bound is at most `Bf`. -/
def AccessRun (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → Int → Int → State α → Prop
  | 0, B, Bf, _ => B ≤ Bf
  | n + 1, B, Bf, s => if s.halted then B ≤ Bf else
      ((exec rodata (prog.getD s.pc .nop) s).err = false ∧ AccessOk B s (prog.getD s.pc .nop) ∧
        AccessRun rodata prog n (bumpB B s (prog.getD s.pc .nop)) Bf (exec rodata (prog.getD s.pc .nop) s))

/-- **The simulation along a run**: the aliased run follows the separate-region run, and at the end
the output region of the latter still holds the input above `Bf`. -/
theorem sim_run (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (B Bf : Int) (s t : State α), AccessRun rodata prog n B Bf s → Sim s t → Clean B s →
      Sim (X86.isa.run rodata prog n s) (runAl rodata prog n t) ∧ Clean Bf (X86.isa.run rodata prog n s) ∧
      ∀ q, (X86.isa.run rodata prog n s).mem rInput q = s.mem rInput q := by
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
      have hst := sim_step rodata (prog.getD s.pc .nop) s t B hS hC hok hh hne
      show Sim (if s.halted then s else X86.isa.run rodata prog n (X86.exec rodata (prog.getD s.pc .nop) s))
        (if t.halted then t else runAl rodata prog n (execAl rodata (prog.getD t.pc .nop) t)) ∧
        Clean Bf (if s.halted then s else X86.isa.run rodata prog n (X86.exec rodata (prog.getD s.pc .nop) s)) ∧
        ∀ q, (if s.halted then s else X86.isa.run rodata prog n (X86.exec rodata (prog.getD s.pc .nop) s)).mem rInput q =
          s.mem rInput q
      rw [hth, hh, htpc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ hA hst.1 hst.2
      refine ⟨h1, h2, fun q => (h3 q).trans ?_⟩
      exact exec_frame rodata _ s hne rInput q (fun hw => hok.2 _ hw rfl)
    · simp only [AccessRun, hh, ↓reduceIte] at hA
      rw [Isa.run_halted _ _ _ _ _ hh]
      simp only [runAl, hth, hh, ↓reduceIte]; exact ⟨hS, clean_mono _ _ _ hA hC, fun _ => trivial⟩

theorem bumpB_mono (B B' : Int) (s : State α) (i : Instr) (h : B' ≤ B) : bumpB B' s i ≤ bumpB B s i := by
  unfold bumpB
  generalize writes s i = l
  induction l generalizing B B' with
  | nil => exact h
  | cons c l ih2 => simp only [List.foldl_cons]; apply ih2; split <;> omega

theorem accessRun_mono (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (B B' Bf : Int) (s : State α), B' ≤ B → AccessRun rodata prog n B Bf s → AccessRun rodata prog n B' Bf s := by
  intro n
  induction n with
  | zero => intro B B' Bf s hB hA; exact Int.le_trans hB hA
  | succ n ih =>
    intro B B' Bf s hB hA
    cases hh : s.halted
    · simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte] at hA ⊢
      obtain ⟨hne, hok, hA⟩ := hA
      exact ⟨hne, ⟨fun c hc hr => Int.le_trans hB (hok.1 c hc hr), hok.2⟩, ih _ _ _ _ (bumpB_mono _ _ _ _ hB) hA⟩
    · simp only [AccessRun, hh, ↓reduceIte] at hA ⊢
      exact Int.le_trans hB hA

end X86
end Keccaktree.Asm

/-! ## A checker for the access condition (concrete runs) -/
namespace Keccaktree.Asm
open X86
namespace X86

/-- `AccessRun` as a Boolean function on concrete states. -/
def accessCheck (rodata : Array (BitVec 64)) (prog : Array Instr) : Nat → Int → Int → State (BitVec 64) → Bool
  | 0, B, Bf, _ => decide (B ≤ Bf)
  | n + 1, B, Bf, s => if s.halted then decide (B ≤ Bf) else
      !(exec rodata (prog.getD s.pc .nop) s).err &&
      (reads s (prog.getD s.pc .nop)).all (fun c => c.1 != rInput || decide (B ≤ c.2)) &&
      (writes s (prog.getD s.pc .nop)).all (fun c => c.1 != rInput) &&
      accessCheck rodata prog n (bumpB B s (prog.getD s.pc .nop)) Bf (exec rodata (prog.getD s.pc .nop) s)

theorem accessCheck_sound (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n : Nat) (B Bf : Int) (s : State (BitVec 64)), accessCheck rodata prog n B Bf s = true →
      AccessRun rodata prog n B Bf s := by
  intro n
  induction n with
  | zero => intro B Bf s h; simp only [accessCheck, decide_eq_true_eq] at h; exact h
  | succ n ih =>
    intro B Bf s h
    cases hh : s.halted
    · simp only [accessCheck, hh, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true',
        List.all_eq_true] at h
      obtain ⟨⟨⟨he, hr⟩, hw⟩, hA⟩ := h
      simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte]
      refine ⟨he, ⟨fun c hc hrc => ?_, fun c hc hrc => ?_⟩, ih _ _ _ hA⟩
      · have := hr c hc; simp only [hrc, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at this; exact this
      · have := hw c hc; simp [hrc] at this
    · simp only [accessCheck, hh, ↓reduceIte, decide_eq_true_eq] at h
      simp only [AccessRun, hh, ↓reduceIte]; exact h

end X86
end Keccaktree.Asm

/-! ## Composing access conditions -/
namespace Keccaktree.Asm
open X86
namespace X86

theorem accessRun_halted (rodata : Array (BitVec 64)) (prog : Array Instr) (m : Nat) (B Bf : Int) (s : State (BitVec 64))
    (hh : s.halted = true) (h : AccessRun rodata prog m B Bf s) : B ≤ Bf := by
  cases m with
  | zero => exact h
  | succ m => simp only [AccessRun, hh, ↓reduceIte] at h; exact h

/-- **Sequencing**: the access condition of `n` steps up to an intermediate bound, then of `m` more. -/
theorem accessRun_add (rodata : Array (BitVec 64)) (prog : Array Instr) :
    ∀ (n m : Nat) (B B' Bf : Int) (s : State (BitVec 64)), AccessRun rodata prog n B B' s →
      AccessRun rodata prog m B' Bf (X86.isa.run rodata prog n s) → AccessRun rodata prog (n + m) B Bf s := by
  intro n
  induction n with
  | zero =>
    intro m B B' Bf s h1 h2
    simp only [Nat.zero_add]
    exact accessRun_mono rodata prog m B' B Bf s h1 h2
  | succ n ih =>
    intro m B B' Bf s h1 h2
    rw [show n + 1 + m = (n + m) + 1 by omega]
    cases hh : s.halted
    · simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
      obtain ⟨hne, hok, h1⟩ := h1
      refine ⟨hne, hok, ih m _ B' Bf _ h1 ?_⟩
      have : X86.isa.run rodata prog (n + 1) s = X86.isa.run rodata prog n (X86.exec rodata (prog.getD s.pc .nop) s) := by
        show (if s.halted then s else _) = _; rw [hh]; rfl
      rw [this] at h2; exact h2
    · simp only [AccessRun, hh, ↓reduceIte] at h1 ⊢
      rw [Isa.run_halted _ _ _ _ _ hh] at h2
      exact Int.le_trans h1 (accessRun_halted rodata prog m B' Bf s hh h2)

/-- One step without input or output cells. -/
theorem accessRun_step (rodata : Array (BitVec 64)) (prog : Array Instr) (m : Nat) (B Bf : Int) (s : State (BitVec 64))
    (hh : s.halted = false) (hne : (exec rodata (prog.getD s.pc .nop) s).err = false)
    (hr : ∀ c ∈ reads s (prog.getD s.pc .nop), c.1 ≠ rInput)
    (hw : ∀ c ∈ writes s (prog.getD s.pc .nop), c.1 ≠ rInput ∧ c.1 ≠ rOutput)
    (h : AccessRun rodata prog m B Bf (exec rodata (prog.getD s.pc .nop) s)) :
    AccessRun rodata prog (m + 1) B Bf s := by
  simp only [AccessRun, hh, Bool.false_eq_true, ↓reduceIte]
  refine ⟨hne, ⟨fun c hc h1 => absurd h1 (hr c hc), fun c hc => (hw c hc).1⟩, ?_⟩
  have : bumpB B s (prog.getD s.pc .nop) = B := by
    clear h hr hne
    unfold bumpB
    generalize writes s (prog.getD s.pc .nop) = l at hw
    induction l generalizing B with
    | nil => rfl
    | cons c l ih =>
      simp only [List.foldl_cons, (hw c List.mem_cons_self).2, ↓reduceIte]
      exact ih B (fun d hd => hw d (List.mem_cons_of_mem _ hd))
  rw [this]; exact h

end X86
end Keccaktree.Asm
