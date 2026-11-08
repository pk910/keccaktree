import Keccaktree.Kernels.X86X1.Lib
import Keccaktree.Asm.LibAlias
import Keccaktree.Asm.AliasTrace
import Keccaktree.Kernels.X86X1.InPlace.GenSE1
import Keccaktree.Kernels.X86X1.InPlace.GenSE3
import Keccaktree.Kernels.X86X1.InPlace.GenSB
import Keccaktree.Kernels.X86X1.InPlace.GenSX
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_x86_x1` in place (`out == in`), for every count

`x86_x1_inplace`: the aliased machine (`X86.runAl`, one buffer) runs the kernel on `c` nodes at node
offset `off` and leaves the digest of node `off + n` in buffer words `4(off+n) .. 4(off+n)+3`.  From
`LibAlias.inplace_lift`: the all-count theorem for separate buffers (`Lib.norm_thm`) and the access
condition along the separate-region run (`access_all`): every input word is loaded at or above the
bound `4·(off + k)` while node `off + k` is hashed (above every digest stored so far).  The access
condition comes from the generated segments: each slice's base footprint summary (`sum*`, decided),
relocated by `rho m` (input words `+8m`, output words `+4m`, `chain_access`), plus the few concrete
steps between the segments.
-/
namespace Keccaktree.Kernels.X86X1.InPlaceAll
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Kernels.X86X1.All Keccaktree.Asm.LibAlias
open Keccaktree.Kernels.X86X1 (prog rodata)

/-! ## The access condition along the run -/

theorem within54 (m : Nat) (h : 64 * m ≤ 2 ^ 54) : (rho m).within GenSB.B := rho_within m h

/-- A segment of one slice without input or output cells keeps any bound. -/
theorem seg1_access {B : Int} (C : SliceCert X86.isa X86.isaReloc rodata prog B) (ρ : Reloc) (hρ : ρ.ok)
    (hw : ρ.within B) (S : State (BitVec 64)) (hc : relocState ρ (cutOf C.ctl C.sc) = cutOf C.ctl S)
    (hs : SliceCert.Ok S) (hsum : summ (traceCells rodata prog C.idx C.cut) = ⟨none, none, none, false⟩) (b : Int) :
    AccessRun rodata prog C.idx.length b b S := by
  have := chain_access ρ hρ hw [C] S b b trivial (by intro D hD; simp at hD; subst hD; exact hc) hs
    (by simp only [List.map_cons, List.map_nil, SummOk, hsum, nextB]; simp)
  simpa using this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One iteration**: the body hashes node `m = off + k` with every input load at or above `4m`
and its digest stored below `4m + 4`. -/
theorem body_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (k : Nat) (S : State (BitVec 64)) (hk : k < c) (hH : Head off c input S0 k S) :
    AccessRun rodata prog 4269 (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S := by
  obtain ⟨hcut, hok, hcnt, hin, hpre, hdig⟩ := hH
  have hρ := rho_ok (off + k)
  have hw : (rho (off + k)).within GenSB.B := rho_within (off + k) (by omega)
  have hseg : AccessRun rodata prog GenSB.segLen (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S := by
    rw [← InPlace.GenSB.len]
    apply chain_access (rho (off + k)) hρ hw InPlace.GenSB.certs S _ _ InPlace.GenSB.chain
      (by intro C hC; simp only [InPlace.GenSB.certs, List.head?_cons, Option.mem_def, Option.some.injEq] at hC; subst hC; exact hcut) hok
    rw [InPlace.GenSB.sums, rho_wshift_in, rho_wshift_out]
    simp only [SummOk, nextB]
    simp [SummOk, nextB] <;> omega
  -- the body run, then `dec qword [rsp+424]` and `jne`
  have sr := GenSB.seg_run (rho (off + k)) hρ hw S hcut hok
  have fr := GenSB.seg_frame (rho (off + k)) hρ hw S hcut hok
  generalize hSb : GenSB.segAt25 S = Sb at sr fr
  obtain ⟨hrun, hokb, hcutb⟩ := sr
  have fb := cut_fields _ _ _ _ hcutb
  have hsp : Sb.getGD 4 = gprWord ⟨rStack, 1048088⟩ := by
    have e1 := cut_word (rho (off + k)) hρ GenSB.ctl25 GenSB.sc25 Sb hcutb 260 (Or.inl (by decide))
    rw [show cutVar GenSB.ctl25 GenSB.sc25 260 = .ptr ⟨rStack, 1048088⟩ by decide +kernel, reloc_ptr_stack] at e1
    rw [← envOf_gdVar Sb 4 (by decide)]
    exact cut_ptr GenSB.ctl25 Sb 260 (by decide) _ e1
  have hgx : gx Sb 4 = some ⟨rStack, 1048088⟩ := gx_of_word Sb 4 _ hsp (by decide)
  have hcntb : Sb.mem rStack 131064 = gprWord ⟨0, (c : Int) - k⟩ := by
    rw [fr rStack 131064 (by rw [rho_wshift_stack]; decide), hcnt]
  have hpcb : Sb.pc = 600 := fb.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hhb : Sb.halted = false := hokb.2.1
  have hb' : 64 * (off + c) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hdec : X86.exec rodata (.decm (.base 4 424)) Sb =
      next { Sb with mem := memStore Sb.mem rStack 131064 (gprWord ⟨0, (c : Int) - k - 1⟩), zf := decide ((c : Int) - k - 1 = 0) } :=
    exec_decm_num rodata Sb 4 424 ⟨rStack, 1048088⟩ ((c : Int) - k) hhb hgx (by decide) (by decide)
      hcntb (by
        show 0 ≤ (c : Int) - k ∧ (c : Int) - k < 2 ^ 55
        rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega)
  have hmemop : memAddr? Sb (.base 4 424) = some ⟨rStack, 1048088 + 424⟩ := by simp [memAddr?, hgx]
  have hsteps : AccessRun rodata prog 2 (4 * ((off + k : Nat) : Int) + 4) (4 * ((off + k : Nat) : Int) + 4) Sb := by
    apply accessRun_step rodata prog 1 _ _ Sb hhb
    · rw [hpcb, prog_600, hdec]; exact hokb.1
    · intro cl hc; rw [hpcb, prog_600] at hc
      simp only [reads, memCells, hmemop, storeCells, List.map_cons, List.map_nil, List.range_one, List.mem_cons,
        List.mem_nil_iff, or_false] at hc
      subst hc; decide
    · intro cl hc; rw [hpcb, prog_600] at hc
      simp only [writes, hmemop, storeCells, List.map_cons, List.map_nil, List.range_one, List.mem_cons,
        List.mem_nil_iff, or_false] at hc
      subst hc; decide
    · rw [hpcb, prog_600, hdec]
      generalize hV : next { Sb with mem := memStore Sb.mem rStack 131064 (gprWord ⟨0, (c : Int) - k - 1⟩), zf := decide ((c : Int) - k - 1 = 0) } = V
      have hpcV : V.pc = 601 := by rw [← hV]; show Sb.pc + 1 = 601; rw [hpcb]
      have hhV : V.halted = false := by rw [← hV]; exact hhb
      apply accessRun_step rodata prog 0 _ _ V hhV
      · rw [hpcV, prog_601, exec_jcc_eq rodata V .ne 13 hhV]; rw [← hV]; exact hokb.1
      · intro cl hc; rw [hpcV, prog_601] at hc; simp [reads] at hc
      · intro cl hc; rw [hpcV, prog_601] at hc; simp [writes] at hc
      · exact Int.le_refl _
  rw [show 4269 = GenSB.segLen + 2 by rw [body_len]]
  apply accessRun_add rodata prog _ _ _ _ _ S hseg
  rw [hrun]; exact hsteps

/-- **The loop**: from the head of iteration `k`, the remaining iterations. -/
theorem loop_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ d k (S : State (BitVec 64)), k + d + 1 = c → Head off c input S0 k S →
      AccessRun rodata prog (4269 * (d + 1)) (4 * ((off + k : Nat) : Int)) (4 * ((off + c : Nat) : Int)) S := by
  intro d
  induction d with
  | zero =>
    intro k S hk hH
    have := body_access off c input S0 hb k S (by omega) hH
    rw [show ((off + c : Nat) : Int) = (off + k : Nat) + 1 by omega, show 4269 * (0 + 1) = 4269 from rfl]
    rw [show 4 * (((off + k : Nat) : Int) + 1) = 4 * ((off + k : Nat) : Int) + 4 by omega]
    exact this
  | succ d ih =>
    intro k S hk hH
    have h1 := (iter off c input S0 hb k S (by omega) hH).1 (by omega)
    rw [show 4269 * (d + 1 + 1) = 4269 + 4269 * (d + 1) by omega]
    apply accessRun_add rodata prog _ _ _ _ _ S (body_access off c input S0 hb k S (by omega) hH)
    have := ih (k + 1) _ (by omega) h1
    rw [show ((off + (k + 1) : Nat) : Int) = (off + k : Nat) + 1 by omega] at this
    rw [show 4 * ((off + k : Nat) : Int) + 4 = 4 * (((off + k : Nat) : Int) + 1) by omega]
    exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The epilogue touches neither input nor output. -/
theorem exit_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (hm : 64 * m ≤ 2 ^ 54)
    (U : State (BitVec 64)) (hX : ExitAt off c input S0 m U) (b : Int) :
    AccessRun rodata prog 8 b b U := by
  obtain ⟨hcut, hok, hpre, hdig⟩ := hX
  have hρ := rho_ok m
  have hw : (rho m).within GenSX.B := rho_within m hm
  have hseg : AccessRun rodata prog GenSX.segLen b b U := by
    have := seg1_access GenSX.cert0 (rho m) hρ hw U hcut hok (by have := InPlace.GenSX.sums; simpa [InPlace.GenSX.certs] using this) b
    exact this
  have sr := GenSX.seg_run (rho m) hρ hw U hcut hok
  generalize hSx : GenSX.segAt1 U = Sx at sr
  obtain ⟨hrun, hokx, hcutx⟩ := sr
  have fx := cut_fields _ _ _ _ hcutx
  have hpc : Sx.pc = 609 := fx.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hd : Sx.depth = 0 := fx.2.2.2.2.2.2.2.2.trans (by decide +kernel)
  rw [show 8 = GenSX.segLen + 1 by rw [exit_len]]
  apply accessRun_add rodata prog _ _ _ _ _ U hseg
  rw [hrun]
  apply accessRun_step rodata prog 0 _ _ Sx hokx.2.1
  · rw [hpc, prog_609, exec_ret0 Sx hokx.2.1 hd]; exact hokx.1
  · intro cl hc; rw [hpc, prog_609] at hc; simp [reads, hd] at hc
  · intro cl hc; rw [hpc, prog_609] at hc; simp [writes] at hc
  · exact Int.le_refl _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The access condition of a whole call** (`c` nodes at node offset `off`): the bound starts at
`4·off` and ends at `4·(off + c)`. -/
theorem access_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    AccessRun rodata prog (21 + 4269 * c) (4 * (off : Int)) (4 * ((off + c : Nat) : Int)) S := by
  have hρ := rho_ok off
  have hwf_in : (⟨rInput, 64 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 64 * (off : Int) ∧ 64 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hwf_out : (⟨rOutput, 32 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 32 * (off : Int) ∧ 32 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
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
  have hw0 : (rho off).within (2 ^ 54) := rho_within off (by omega)
  have a1 : AccessRun rodata prog GenSE1.segLen (4 * (off : Int)) (4 * (off : Int)) S :=
    seg1_access GenSE1.cert0 (rho off) hρ hw0 S hc0 hE.ok (by have := InPlace.GenSE1.sums; simpa [InPlace.GenSE1.certs] using this) (4 * (off : Int))
  have s1 := GenSE1.seg_run (rho off) hρ hw0 S hc0 hE.ok
  have f1 := GenSE1.seg_frame (rho off) hρ hw0 S hc0 hE.ok
  have m1 := GenSE1.seg_moves (rho off) hρ hw0 S hc0 hE.ok 258 258 (by simp)
  generalize hT1 : GenSE1.segAt1 S = T1 at s1 m1 f1
  obtain ⟨hrun1, hok1, hcut1⟩ := s1
  have ft1 := cut_fields _ _ _ _ hcut1
  have hrdx1 : T1.getGD 2 = gprWord ⟨0, c⟩ := by
    rw [Reloc.var_lt (rho off) 258 (by decide)] at m1
    rw [← envOf_gdVar T1 2 (by decide)]
    exact m1.trans ((envOf_gdVar S 2 (by decide)).trans hE.rdx)
  have hpc1 : T1.pc = 7 := ft1.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hh1 : T1.halted = false := hok1.2.1
  have ht := exec_test_num rodata T1 2 c hh1 hrdx1 (by
    show 0 ≤ (c : Int) ∧ (c : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega)
  generalize hT2 : next { T1 with zf := decide ((c : Int) = 0), cf := false } = T2 at ht
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
  -- the 9 entry steps keep the bound
  have a9 : ∀ (m : Nat) (bf : Int), AccessRun rodata prog m (4 * (off : Int)) bf T3 →
      AccessRun rodata prog (9 + m) (4 * (off : Int)) bf S := by
    intro m bf hrest
    rw [show 9 + m = GenSE1.segLen + (2 + m) by rw [e1_len]; omega]
    apply accessRun_add rodata prog _ _ _ _ _ S a1
    rw [hrun1, show 2 + m = (m + 1) + 1 by omega]
    apply accessRun_step rodata prog _ _ _ T1 hh1
    · rw [hpc1, prog_7, ht, ← hT2]; exact hok1.1
    · intro cl hc; rw [hpc1, prog_7] at hc; simp [reads] at hc
    · intro cl hc; rw [hpc1, prog_7] at hc; simp [writes] at hc
    · rw [hpc1, prog_7, ht]
      apply accessRun_step rodata prog _ _ _ T2 hh2
      · rw [hpc2, prog_8, exec_jcc_eq rodata T2 .e 602 hh2, ← hT2]; exact hok1.1
      · intro cl hc; rw [hpc2, prog_8] at hc; simp [reads] at hc
      · intro cl hc; rw [hpc2, prog_8] at hc; simp [writes] at hc
      · rw [hpc2, prog_8, exec_jcc_eq rodata T2 .e 602 hh2, hT3]; exact hrest
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have hz : decide (((0 : Nat) : Int) = 0) = true := rfl
    have hX : ExitAt off 0 input S off T3 := by
      refine ⟨?_, hT3ok, fun q _ => by rw [hT3mem]; exact f1 rOutput q rfl, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      · apply cut_transfer (rho off) (rho off) hρ hρ GenSE1.ctl1 GenSX.ctl0 GenSE1.sc1 GenSX.sc0 T1 T3 hcut1
          (hL_dec _ _ (by decide +kernel)) (fun i _ => hT3env i) (hval_same _ _ _ _ _ (by decide +kernel))
        exact ctrl_after T3 T1 GenSE1.sc1 GenSX.sc0 ft1 hT3c (by decide +kernel)
          (by rw [hT3zf, hz]; decide +kernel) (by rw [hT3cf]; decide +kernel) (by rw [hT3pc, hz]; decide +kernel)
    have he := exit_access off 0 input S off (by omega) T3 hX (4 * (off : Int))
    rw [show 21 + 4269 * 0 = 9 + (8 + 4) by rfl]
    apply a9
    apply accessRun_add rodata prog 8 4 _ (4 * (off : Int)) _ T3 he
    have hhalt := (epilogue off 0 input S off (by omega) T3 hX).1
    rw [show ((off + 0 : Nat) : Int) = (off : Int) by simp]
    -- the remaining steps from a halted state
    cases h4 : (4 : Nat) with
    | zero => exact Int.le_refl _
    | succ n => simp [AccessRun, hhalt]
  · have hz : decide ((c : Int) = 0) = false := decide_eq_false (by omega)
    have hc3 : relocState (rho off) (cutOf GenSE3.ctl0 GenSE3.sc0) = cutOf GenSE3.ctl0 T3 := by
      apply cut_transfer (rho off) (rho off) hρ hρ GenSE1.ctl1 GenSE3.ctl0 GenSE1.sc1 GenSE3.sc0 T1 T3 hcut1
        (hL_dec _ _ (by decide +kernel)) (fun i _ => hT3env i) (hval_same _ _ _ _ _ (by decide +kernel))
      exact ctrl_after T3 T1 GenSE1.sc1 GenSE3.sc0 ft1 hT3c (by decide +kernel)
        (by rw [hT3zf, hz]; decide +kernel) (by rw [hT3cf]; decide +kernel) (by rw [hT3pc, hz]; decide +kernel)
    have a3 : AccessRun rodata prog GenSE3.segLen (4 * (off : Int)) (4 * (off : Int)) T3 := seg1_access GenSE3.cert0 (rho off) hρ hw0 T3 hc3 hT3ok (by have := InPlace.GenSE3.sums; simpa [InPlace.GenSE3.certs] using this) (4 * (off : Int))
    have s3 := GenSE3.seg_run (rho off) hρ hw0 T3 hc3 hT3ok
    have f3 := GenSE3.seg_frame (rho off) hρ hw0 T3 hc3 hT3ok
    have m3 := GenSE3.seg_moves (rho off) hρ hw0 T3 hc3 hT3ok 2097315 258 (by simp)
    generalize hT5 : GenSE3.segAt1 T3 = T5 at s3 f3 m3
    obtain ⟨hrun3, hok3, hcut3⟩ := s3
    have ft3 := cut_fields _ _ _ _ hcut3
    have hpre3 : ∀ q : Int, T3.mem rOutput q = S.mem rOutput q := by
      intro q; rw [hT3mem]; exact f1 rOutput q rfl
    have hin3 : ∀ q : Int, T3.mem rInput q = input q := by
      intro q; rw [hT3mem, f1 rInput q rfl]; exact hE.inp q
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
    have al := loop_access off c input S hb (c - 1) 0 T5 (by omega) hH
    rw [show c - 1 + 1 = c by omega, show ((off + 0 : Nat) : Int) = (off : Int) by simp] at al
    have ae := exit_access off c input S (off + c - 1) (by omega) _ hl (4 * ((off + c : Nat) : Int))
    rw [show 21 + 4269 * c = 9 + (4 + (4269 * c + 8)) by omega]
    apply a9
    apply accessRun_add rodata prog _ _ _ (4 * (off : Int)) _ T3 (by rw [← e3_len]; exact a3)
    rw [show GenSE3.segLen = 4 from rfl] at hrun3
    rw [hrun3]
    exact accessRun_add rodata prog _ _ _ _ _ T5 al ae

/-- **`keccaktree_keccak256_x86_x1` in place, on any number of nodes.**  For every count `c` and node
offset `off` (`64·(off+c) ≤ 2^54`), from an aliased entry state `T` (its separate-region view
`dupState T` is the calling convention: `rdi` the output pointer at `32·off`, `rsi` the input pointer
at `64·off`, both into the one buffer), `21 + 4269·c` steps of the aliased machine halt without a
model fault and without a tail call, keep the buffer words before `4·off` and from `4·(off+c)` on,
and leave the keccak256 digest of input node `off + n` in buffer words `4(off+n) .. 4(off+n)+3`
(read through the output view; both views show the one buffer). -/
theorem x86_x1_inplace (off c : Nat) (input : Int → BitVec 64) (T : State (BitVec 64))
    (hm : Mirror T) (hE : LibX86.Entry off c input (dupState T)) (hb : 64 * (off + c) ≤ 2 ^ 54) (hpc : T.pc = 0) :
    OutcomeAl [] (4 * ((off + c : Nat) : Int)) off c input T (runAl rodata prog (21 + 4269 * c) T) := by
  have hE' : Entry off c input (dupState T) :=
    ⟨⟨hE.ctrl.1, hE.ctrl.2.1, hE.ctrl.2.2.1, hE.ctrl.2.2.2.1, hE.ctrl.2.2.2.2.1, hE.ctrl.2.2.2.2.2.1,
      hE.ctrl.2.2.2.2.2.2.1, hpc, hE.ctrl.2.2.2.2.2.2.2⟩, hE.ok, hE.rdx, hE.rsp, hE.rsi, hE.rdi, hE.inp⟩
  exact inplace_lift rodata prog 0 (fun _ c => 21 + 4269 * c) [] Lib.norm_thm off c input T hm hE hb hpc
    (4 * (off : Int)) (4 * ((off + c : Nat) : Int)) (access_all off c input (dupState T) hE' hb)

/-! ## The in-place library on `[x86_x1]` -/

/-- **The in-place calling convention** `keccaktree_hash(buf + 32·off, buf + 64·off, count)` after
`off` nodes are done: one buffer (both views agree), the separate-region view at its entry (control of
a fresh call), the message from word `8·off` on. -/
def EntryAl (name : String) (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64)) : Prop :=
  Mirror T ∧ LibX86.Entry off count (fun q => T.mem rInput q) (dupState T) ∧
  (∀ q : Int, 8 * (off : Int) ≤ q → T.mem rInput q = input q) ∧ 64 * (off + count) ≤ 2 ^ 54

theorem digest_input (input input' : Int → BitVec 64) (S : State (BitVec 64)) (n : Nat)
    (h : ∀ w : Nat, input' (Int.ofNat (8 * n + w)) = input (Int.ofNat (8 * n + w)))
    (hd : LibX86.Digest input' S n) : LibX86.Digest input S n := by
  have hw : LibX86.nodeWords input' n = LibX86.nodeWords input n := by
    funext w; exact h w
  intro w i hw' hi
  have := hd w i hw' hi
  rw [hw] at this; exact this

/-- `keccaktree_keccak256_x86_x1` as a kernel of the in-place library. -/
def kernelAl : Library.KernelThm X86.isaAl EntryAl LibX86.Digest where
  name := "keccaktree_keccak256_x86_x1"
  rank := 0
  targets := []
  rodata := rodata
  prog := prog
  entry := 0
  steps := fun _ c => 21 + 4269 * c
  thm := fun off count input T h => by
    obtain ⟨hm, hE, hin, hb⟩ := h
    have hO := x86_x1_inplace off count (fun q => T.mem rInput q) { T with pc := 0 } hm (hE.with_pc 0) hb rfl
    rw [← runAl_eq]
    obtain ⟨hh, he, -, hpre, -, hout⟩ := hO
    refine ⟨hh, he, fun q hq => hpre q hq, ?_⟩
    rcases hout with ⟨ht, hd⟩ | ⟨next, done, -, hmem, -⟩
    · refine Or.inl ⟨ht, fun n hn => digest_input _ _ _ _ (fun w => ?_) (hd n hn)⟩
      exact hin _ (by simp only [Int.ofNat_eq_coe]; omega)
    · simp at hmem

theorem ranks_al : Library.RanksOk [kernelAl] := Library.ranksOk_of_shape _ (by decide +kernel)

/-- **The in-place library theorem on the table `[x86_x1]`**: from the in-place calling convention,
the library run on the one buffer halts without a model fault with every node's digest in place. -/
theorem lib_inplace_x86_x1 (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64))
    (hT : EntryAl "keccaktree_keccak256_x86_x1" off count input T) : Library.LibOk [kernelAl] kernelAl off count input T :=
  Library.lib_correct [kernelAl] 0 (by simp [kernelAl]) ranks_al LibX86.digest_local _ kernelAl (by simp) off count input T
    (Nat.le_refl _) hT

end Keccaktree.Kernels.X86X1.InPlaceAll
