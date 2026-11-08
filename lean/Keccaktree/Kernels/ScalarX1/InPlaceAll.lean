import Keccaktree.Kernels.ScalarX1.All
import Keccaktree.Asm.ArmAliasTrace
import Keccaktree.Kernels.ScalarX1.InPlace.GenSE1
import Keccaktree.Kernels.ScalarX1.InPlace.GenSB
import Keccaktree.Kernels.ScalarX1.InPlace.GenSX
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_scalar_x1` (AArch64) in place (`out == in`), for every count

The access condition along the separate-region run (`access_all`): every input word is loaded at or
above the bound `4·(off + k)` while node `off + k` is hashed.  It mirrors `All.scalar_x1_all`: the
generated segments' footprint summaries (`InPlace.Gen*`, `Arm.alIsa.chain_access` at relocation
`rho m`), the concrete steps between them (`Arm.accessRun_step`), and the flags: each segment was
recorded with fixed flags (`norm S sc`); the run from the actual flags satisfies the same condition
(`Arm.accessRun_ann`, the kernel's flag annotation `ArmFlags.scalar_x1`).

`kernelAl` (`LibArmAl.mkKernelArmAl`) and **`lib_inplace_scalar_x1`**: the in-place library on
`[scalar_x1]`, from any flags at entry.
-/
namespace Keccaktree.Kernels.ScalarX1.InPlaceAll
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Asm.Nodes Keccaktree.Kernels.ScalarX1.All
open Keccaktree.Asm.LibX86 (Digest digest_local)
open Keccaktree.Kernels.ScalarX1 (prog rodata)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One iteration**: the body hashes node `m = off + k` with every input load at or above `4m`
and its digest stored below `4m + 4`; then `subs`, `b.ne`. -/
theorem body_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (k : Nat) (S : State (BitVec 64)) (hk : k < c) (hH : Head off c input S0 k S) :
    Arm.AccessRun rodata prog 2437 (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S := by
  obtain ⟨hcut, hok, hcnt, hin, hpre, hdig⟩ := hH
  have hρ := rho_ok (off + k)
  have hw : (rho (off + k)).within GenSB.B := rho_within (off + k) (by omega)
  have hok' : SliceCert.Ok (norm S GenSB.sc0) := hok
  have sr := GenSB.seg_run (rho (off + k)) hρ hw _ hcut hok'
  have ft0 := cut_fields _ _ _ _ hcut
  have hsegN : Arm.AccessRun rodata prog GenSB.segLen (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4)
      (norm S GenSB.sc0) := by
    rw [← InPlace.GenSB.len]
    apply Arm.alIsa.chain_access (rho (off + k)) hρ hw InPlace.GenSB.certs _ _ _ InPlace.GenSB.chain
      (by intro C hC; simp only [InPlace.GenSB.certs, List.head?_cons, Option.mem_def, Option.some.injEq] at hC; subst hC; exact hcut) hok'
    rw [InPlace.GenSB.sums, rho_wshift_in, rho_wshift_out]
    simp only [SummOk, nextB]
    simp [SummOk, nextB] <;> omega
  have hseg : Arm.AccessRun rodata prog GenSB.segLen (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S :=
    Arm.accessRun_ann rodata prog _ ArmFlags.scalar_x1_ok _ _ _ S (norm S GenSB.sc0) (Arm.ovr_all_flags S _ _ _ _)
      (by rw [ft0.2.2.2.2.2.2.2.1]; decide +kernel) (by rw [sr.1]; exact sr.2.1.1) hsegN
  have mv := GenSB.seg_moves (rho (off + k)) hρ hw _ hcut hok' 258 258 (by simp)
  have fl : Arm.isa.run rodata prog GenSB.segLen S =
      (GenSB.segAt25 (norm S GenSB.sc0)).withFlags S.zf S.cf S.nf S.vf :=
    GenSB.seg_flags (rho (off + k)) hρ hw _ hcut hok' S.zf S.cf S.nf S.vf
  rw [Reloc.var_lt _ 258 (by decide)] at mv
  generalize hSb' : GenSB.segAt25 (norm S GenSB.sc0) = Sb' at sr mv fl
  obtain ⟨_, hokb, hcutb⟩ := sr
  have fb := cut_fields _ _ _ _ hcutb
  generalize hSb : Sb'.withFlags S.zf S.cf S.nf S.vf = Sb at fl
  have hSbenv : ∀ i, envOf Sb i = envOf Sb' i := by intro i; rw [← hSb]; rfl
  have hhb : Sb.halted = false := by rw [← hSb]; exact hokb.2.1
  have heb : Sb.err = false := by rw [← hSb]; exact hokb.1
  have hpcb : Sb.pc = 2442 := by rw [← hSb]; exact fb.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hcntb : Sb.getGD 2 = gprWord ⟨0, (c : Int) - k⟩ := by
    have e1 : envOf Sb 258 = Sb.getGD 2 := envOf_gdVar Sb 2 (by decide)
    have e2 : envOf (norm S GenSB.sc0) 258 = (norm S GenSB.sc0).getGD 2 := envOf_gdVar _ 2 (by decide)
    rw [← e1, hSbenv, mv, e2]; exact hcnt
  have hb' : 64 * (off + c) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hsubs := Arm.exec_subs_num rodata Sb 2 2 1 ((c : Int) - k) hhb hcntb (wf_num _ (by omega) (by omega))
  generalize hV : Arm.next (Arm.setFlags (Sb.setGD 2 (gprWord ⟨0, (c : Int) - k - 1⟩)) ((c : Int) - k) 1) = V at hsubs
  have hpcV : V.pc = 2443 := by rw [← hV]; show Sb.pc + 1 = 2443; rw [hpcb]
  have hhV : V.halted = false := by rw [← hV]; exact hhb
  have heV : V.err = false := by rw [← hV]; exact heb
  have hsteps : Arm.AccessRun rodata prog 2 (4 * ((off + k : Nat) : Int) + 4) (4 * ((off + k : Nat) : Int) + 4) Sb := by
    apply Arm.accessRun_step rodata prog 1 _ _ Sb hhb
    · rw [hpcb, prog_2442, hsubs]; exact heV
    · intro cl hc; rw [hpcb, prog_2442] at hc; simp [Arm.reads] at hc
    · intro cl hc; rw [hpcb, prog_2442] at hc; simp [Arm.writes] at hc
    · rw [hpcb, prog_2442, hsubs]
      apply Arm.accessRun_step rodata prog 0 _ _ V hhV
      · rw [hpcV, prog_2443, Arm.exec_bcond_eq rodata V .ne 7 hhV]; exact heV
      · intro cl hc; rw [hpcV, prog_2443] at hc; simp [Arm.reads] at hc
      · intro cl hc; rw [hpcV, prog_2443] at hc; simp [Arm.writes] at hc
      · exact Int.le_refl _
  rw [show 2437 = GenSB.segLen + 2 by rw [body_len]]
  apply Arm.accessRun_add rodata prog _ _ _ _ _ S hseg
  rw [fl]; exact hsteps

/-- **The loop**: from the head of iteration `k`, the remaining iterations. -/
theorem loop_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ d k (S : State (BitVec 64)), k + d + 1 = c → Head off c input S0 k S →
      Arm.AccessRun rodata prog (2437 * (d + 1)) (4 * ((off + k : Nat) : Int)) (4 * ((off + c : Nat) : Int)) S := by
  intro d
  induction d with
  | zero =>
    intro k S hk hH
    have := body_access off c input S0 hb k S (by omega) hH
    rw [show ((off + c : Nat) : Int) = (off + k : Nat) + 1 by omega, show 2437 * (0 + 1) = 2437 from rfl]
    rw [show 4 * (((off + k : Nat) : Int) + 1) = 4 * ((off + k : Nat) : Int) + 4 by omega]
    exact this
  | succ d ih =>
    intro k S hk hH
    have h1 := (iter off c input S0 hb k S (by omega) hH).1 (by omega)
    rw [show 2437 * (d + 1 + 1) = 2437 + 2437 * (d + 1) by omega]
    apply Arm.accessRun_add rodata prog _ _ _ _ _ S (body_access off c input S0 hb k S (by omega) hH)
    have := ih (k + 1) _ (by omega) h1
    rw [show ((off + (k + 1) : Nat) : Int) = (off + k : Nat) + 1 by omega] at this
    rw [show 4 * ((off + k : Nat) : Int) + 4 = 4 * (((off + k : Nat) : Int) + 1) by omega]
    exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The epilogue (`ldp ×6; ret`) touches neither input nor output. -/
theorem exit_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (hm : 64 * m ≤ 2 ^ 54)
    (U : State (BitVec 64)) (hX : ExitAt off c input S0 m U) (b : Int) :
    Arm.AccessRun rodata prog 7 b b U := by
  obtain ⟨hcut, hok, hpre, hdig⟩ := hX
  have hρ := rho_ok m
  have hw : (rho m).within GenSX.B := rho_within m hm
  have hok' : SliceCert.Ok (norm U GenSX.sc0) := hok
  have sr := GenSX.seg_run (rho m) hρ hw _ hcut hok'
  have ft0 := cut_fields _ _ _ _ hcut
  have hsegN : Arm.AccessRun rodata prog GenSX.segLen b b (norm U GenSX.sc0) := by
    have := Arm.alIsa.seg1_access GenSX.cert0 (rho m) hρ hw _ hcut hok' InPlace.GenSX.sum0 b
    exact this
  have hseg : Arm.AccessRun rodata prog GenSX.segLen b b U :=
    Arm.accessRun_ann rodata prog _ ArmFlags.scalar_x1_ok _ _ _ U (norm U GenSX.sc0) (Arm.ovr_all_flags U _ _ _ _)
      (by rw [ft0.2.2.2.2.2.2.2.1]; decide +kernel) (by rw [sr.1]; exact sr.2.1.1) hsegN
  have fl : Arm.isa.run rodata prog GenSX.segLen U = (GenSX.segAt1 (norm U GenSX.sc0)).withFlags U.zf U.cf U.nf U.vf :=
    GenSX.seg_flags (rho m) hρ hw _ hcut hok' U.zf U.cf U.nf U.vf
  generalize hSx' : GenSX.segAt1 (norm U GenSX.sc0) = Sx' at sr fl
  obtain ⟨_, hokx, hcutx⟩ := sr
  have fx := cut_fields _ _ _ _ hcutx
  generalize hSx : Sx'.withFlags U.zf U.cf U.nf U.vf = Sx at fl
  have hpc : Sx.pc = 2450 := by rw [← hSx]; exact fx.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hhx : Sx.halted = false := by rw [← hSx]; exact hokx.2.1
  have hex : Sx.err = false := by rw [← hSx]; exact hokx.1
  rw [show 7 = GenSX.segLen + 1 by rw [exit_len]]
  apply Arm.accessRun_add rodata prog _ _ _ _ _ U hseg
  rw [fl]
  apply Arm.accessRun_step rodata prog 0 _ _ Sx hhx
  · rw [hpc, prog_2450, Arm.exec_ret_eq rodata Sx hhx]; exact hex
  · intro cl hc; rw [hpc, prog_2450] at hc; simp [Arm.reads] at hc
  · intro cl hc; rw [hpc, prog_2450] at hc; simp [Arm.writes] at hc
  · exact Int.le_refl _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The access condition of a whole call** (`c` nodes at node offset `off`): the bound starts at
`4·off` and ends at `4·(off + c)`. -/
theorem access_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    Arm.AccessRun rodata prog (14 + 2437 * c) (4 * (off : Int)) (4 * ((off + c : Nat) : Int)) S := by
  have hρ := rho_ok off
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hwf_in : (⟨rInput, 64 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 64 * (off : Int) ∧ 64 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hwf_out : (⟨rOutput, 32 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 32 * (off : Int) ∧ 32 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hc0 : relocState (rho off) (cutOf GenSE1.ctl0 GenSE1.sc0) = cutOf GenSE1.ctl0 (norm S GenSE1.sc0) := by
    apply relocState_cutOf (rho off) GenSE1.ctl0 GenSE1.sc0 (norm S GenSE1.sc0)
    · intro i hi
      simp only [GenSE1.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · rw [cutVar_ptr_of GenSE1.ctl0 (norm S GenSE1.sc0) 256 ⟨rOutput, 32 * (off : Int)⟩ (by decide) ((envOf_gdVar (norm S GenSE1.sc0) 0 (by decide)).trans hE.x0) hwf_out (by show rOutput ≠ 0; decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 256 = .ptr ⟨rOutput, 0⟩ by decide +kernel, reloc_ptr_out, Int.zero_add]
      · rw [cutVar_ptr_of GenSE1.ctl0 (norm S GenSE1.sc0) 257 ⟨rInput, 64 * (off : Int)⟩ (by decide) ((envOf_gdVar (norm S GenSE1.sc0) 1 (by decide)).trans hE.x1) hwf_in (by show rInput ≠ 0; decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 257 = .ptr ⟨rInput, 0⟩ by decide +kernel, reloc_ptr_in, Int.zero_add]
      · rw [cutVar_ptr_of GenSE1.ctl0 (norm S GenSE1.sc0) 287 ⟨rStack, 1048576⟩ (by decide) ((envOf_gdVar (norm S GenSE1.sc0) 31 (by decide)).trans hE.sp) (by decide) (by decide),
          show cutVar GenSE1.ctl0 GenSE1.sc0 287 = .ptr ⟨rStack, 1048576⟩ by decide +kernel, reloc_ptr_stack]
    · intro i hi h; simp only [GenSE1.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
    · obtain ⟨g, k, l, p, d⟩ := hE.ctrl
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show S.g = _; rw [g]; decide +kernel
      · show S.k = _; rw [k]; decide +kernel
      · show S.vl = _; rw [l]; decide +kernel
      · show S.pc = _; rw [p]; decide +kernel
      · show S.depth = _; rw [d]; decide +kernel
  have hw0 : (rho off).within (2 ^ 54) := rho_within off (by omega)
  have hok0 : SliceCert.Ok (norm S GenSE1.sc0) := hE.ok
  have s1 := GenSE1.seg_run (rho off) hρ hw0 _ hc0 hok0
  have ft0 := cut_fields _ _ _ _ hc0
  -- E1: the frame (stores to the stack only)
  have a1N : Arm.AccessRun rodata prog GenSE1.segLen (4 * (off : Int)) (4 * (off : Int)) (norm S GenSE1.sc0) := by
    have := Arm.alIsa.seg1_access GenSE1.cert0 (rho off) hρ hw0 _ hc0 hok0 InPlace.GenSE1.sum0 (4 * (off : Int))
    exact this
  have a1 : Arm.AccessRun rodata prog GenSE1.segLen (4 * (off : Int)) (4 * (off : Int)) S :=
    Arm.accessRun_ann rodata prog _ ArmFlags.scalar_x1_ok _ _ _ S (norm S GenSE1.sc0) (Arm.ovr_all_flags S _ _ _ _)
      (by rw [ft0.2.2.2.2.2.2.2.1]; decide +kernel) (by rw [s1.1]; exact s1.2.1.1) a1N
  have f1 := GenSE1.seg_frame (rho off) hρ hw0 _ hc0 hok0
  have m1 := GenSE1.seg_moves (rho off) hρ hw0 _ hc0 hok0 258 258 (by simp)
  have fl1 : Arm.isa.run rodata prog GenSE1.segLen S = (GenSE1.segAt1 (norm S GenSE1.sc0)).withFlags S.zf S.cf S.nf S.vf :=
    GenSE1.seg_flags (rho off) hρ hw0 _ hc0 hok0 S.zf S.cf S.nf S.vf
  rw [Reloc.var_lt _ 258 (by decide)] at m1
  generalize hT1' : GenSE1.segAt1 (norm S GenSE1.sc0) = T1' at s1 f1 m1 fl1
  obtain ⟨_, hok1, hcut1⟩ := s1
  have ft1 := cut_fields _ _ _ _ hcut1
  generalize hT1 : T1'.withFlags S.zf S.cf S.nf S.vf = T1 at fl1
  have hx2' : T1'.getGD 2 = gprWord ⟨0, c⟩ := by
    have e1 : envOf T1' 258 = T1'.getGD 2 := envOf_gdVar T1' 2 (by decide)
    have e2 : envOf (norm S GenSE1.sc0) 258 = (norm S GenSE1.sc0).getGD 2 := envOf_gdVar _ 2 (by decide)
    rw [← e1, m1, e2]; exact hE.x2
  have hx2 : T1.getGD 2 = gprWord ⟨0, c⟩ := by rw [← hT1]; exact hx2'
  have hpc1 : T1.pc = 6 := by rw [← hT1]; exact ft1.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hh1 : T1.halted = false := by rw [← hT1]; exact hok1.2.1
  have he1 : T1.err = false := by rw [← hT1]; exact hok1.1
  -- cbz x2
  have hcbz := Arm.exec_cbz_num rodata T1 2 2444 c hh1 hx2 (wf_num _ (by omega) (by omega))
  generalize hT2 : { T1 with pc := if (c : Int) = 0 then 2444 else T1.pc + 1 } = T2 at hcbz
  have hT2pc : T2.pc = if (c : Int) = 0 then 2444 else 7 := by rw [← hT2]; show (if (c : Int) = 0 then 2444 else T1.pc + 1) = _; rw [hpc1]
  have hT2env : ∀ i, envOf T2 i = envOf T1' i := by intro i; rw [← hT2, ← hT1]; rfl
  have hT2mem : T2.mem = T1'.mem := by rw [← hT2, ← hT1]; rfl
  have hT2c : T2.g = T1'.g ∧ T2.k = T1'.k ∧ T2.vl = T1'.vl ∧ T2.depth = T1'.depth := by
    rw [← hT2, ← hT1]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hT2ok : SliceCert.Ok T2 := by rw [← hT2, ← hT1]; exact hok1
  have hT2x2 : T2.getGD 2 = gprWord ⟨0, c⟩ := by rw [← hT2]; exact hx2
  have h7 : Arm.isa.run rodata prog 7 S = T2 := by
    rw [show 7 = GenSE1.segLen + 1 by rw [e1_len], Isa.run_add, fl1, Arm.run_one rodata prog T1 hh1,
      show prog.getD T1.pc .nop = .cbz 2 2444 by rw [hpc1]; exact prog_6, hcbz]
  have hpre2 : ∀ q : Int, T2.mem rOutput q = S.mem rOutput q := by
    intro q; rw [hT2mem]; exact f1 rOutput q rfl
  have hin2 : ∀ q : Int, T2.mem rInput q = input q := by
    intro q; rw [hT2mem, f1 rInput q rfl]; exact hE.inp q
  -- the 7 entry steps keep the bound
  have a7 : ∀ (m : Nat) (bf : Int), Arm.AccessRun rodata prog m (4 * (off : Int)) bf T2 →
      Arm.AccessRun rodata prog (7 + m) (4 * (off : Int)) bf S := by
    intro m bf hrest
    rw [show 7 + m = GenSE1.segLen + (m + 1) by rw [e1_len]; omega]
    apply Arm.accessRun_add rodata prog _ _ _ _ _ S a1
    rw [fl1]
    apply Arm.accessRun_step rodata prog _ _ _ T1 hh1
    · rw [hpc1, prog_6, hcbz]; exact hT2ok.1
    · intro cl hc; rw [hpc1, prog_6] at hc; simp [Arm.reads] at hc
    · intro cl hc; rw [hpc1, prog_6] at hc; simp [Arm.writes] at hc
    · rw [hpc1, prog_6, hcbz]; exact hrest
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have hX : ExitAt off 0 input S off T2 := by
      refine ⟨?_, hT2ok, fun q _ => hpre2 q, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      apply cut_transfer (rho off) (rho off) hρ hρ GenSE1.ctl1 GenSX.ctl0 GenSE1.sc1 GenSX.sc0 T1' (norm T2 GenSX.sc0) hcut1
        (hL_dec _ _ (by decide +kernel)) (fun i _ => hT2env i) (hval_same _ _ _ _ _ (by decide +kernel))
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show T2.g = _; rw [hT2c.1, ft1.1]; decide +kernel
      · show T2.k = _; rw [hT2c.2.1, ft1.2.1]; decide +kernel
      · show T2.vl = _; rw [hT2c.2.2.1, ft1.2.2.2.2.2.2.1]; decide +kernel
      · show T2.pc = _; rw [hT2pc]; decide +kernel
      · show T2.depth = _; rw [hT2c.2.2.2, ft1.2.2.2.2.2.2.2.2]; decide +kernel
    have he := exit_access off 0 input S off (by omega) T2 hX (4 * (off : Int))
    rw [show 14 + 2437 * 0 = 7 + 7 by rfl, show ((off + 0 : Nat) : Int) = (off : Int) by simp]
    exact a7 7 _ he
  · have hH : Head off c input S 0 T2 := by
      refine ⟨?_, hT2ok, ?_, hin2, fun q _ => hpre2 q, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      · apply cut_transfer (rho off) (rho (off + 0)) hρ hρ GenSE1.ctl1 GenSB.ctl0 GenSE1.sc1 GenSB.sc0 T1' (norm T2 GenSB.sc0) hcut1
          (hL_dec _ _ (by decide +kernel)) (fun i _ => hT2env i) (hval_same _ _ _ _ _ (by decide +kernel))
        refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
        · show T2.g = _; rw [hT2c.1, ft1.1]; decide +kernel
        · show T2.k = _; rw [hT2c.2.1, ft1.2.1]; decide +kernel
        · show T2.vl = _; rw [hT2c.2.2.1, ft1.2.2.2.2.2.2.1]; decide +kernel
        · show T2.pc = _; rw [hT2pc, if_neg (by omega)]; decide +kernel
        · show T2.depth = _; rw [hT2c.2.2.2, ft1.2.2.2.2.2.2.2.2]; decide +kernel
      · rw [hT2x2]; simp
    have hl := loop off c input S hb (c - 1) 0 T2 (by omega) hH
    rw [show c - 1 + 1 = c by omega] at hl
    have al := loop_access off c input S hb (c - 1) 0 T2 (by omega) hH
    rw [show c - 1 + 1 = c by omega, show ((off + 0 : Nat) : Int) = (off : Int) by simp] at al
    have ae := exit_access off c input S (off + c - 1) (by omega) _ hl (4 * ((off + c : Nat) : Int))
    rw [show 14 + 2437 * c = 7 + (2437 * c + 7) by omega]
    exact a7 _ _ (Arm.accessRun_add rodata prog _ _ _ _ _ T2 al ae)

/-! ## The in-place library on `[scalar_x1]` -/

/-- The access theorem of `scalar_x1` (`LibArmAl.AccessThmArm`): the bound runs from `4·off` to
`4·(off + c)`; the kernel hands nothing over. -/
theorem access_thm : LibArmAl.AccessThmArm rodata prog 0 (fun _ c => 14 + 2437 * c) := by
  intro off c input S hE hb hpc
  refine ⟨4 * ((off + c : Nat) : Int), access_all off c input S (Arm.entry_of_entryA hE hpc) hb, ?_⟩
  intro next done ht _
  obtain ⟨-, -, -, hout⟩ := norm_thm off c input S hE hb hpc
  rcases hout with ⟨ht', -⟩ | ⟨nx, dn, -, hmem, -⟩
  · exact absurd (ht'.symm.trans ht) (by simp)
  · simp at hmem

/-- `keccaktree_keccak256_scalar_x1` as a kernel of the in-place library (any flags at entry). -/
def kernelAl : Library.KernelThm Arm.alIsa.isaAl LibArmAl.EntryArmAl Digest :=
  LibArmAl.mkKernelArmAl "keccaktree_keccak256_scalar_x1" 0 [] rodata prog 0 (fun _ c => 14 + 2437 * c)
    (Arm.flagAnn ArmFlags.scalar_x1) ArmFlags.scalar_x1_ok ArmFlags.entries.1 norm_thm access_thm

theorem ranks_al : Library.RanksOk [kernelAl] := Library.ranksOk_of_shape _ (by decide +kernel)

/-- **The in-place library theorem on the table `[scalar_x1]`** (AArch64, one buffer, any flags at
entry): the library run halts without a model fault with every node's digest in the buffer. -/
theorem lib_inplace_scalar_x1 (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64))
    (hT : LibArmAl.EntryArmAl "keccaktree_keccak256_scalar_x1" off count input T) :
    Library.LibOk [kernelAl] kernelAl off count input T :=
  Library.lib_correct [kernelAl] 0 (by simp [kernelAl, LibArmAl.mkKernelArmAl, LibAliasGen.mkKernelAlG, LibArm.mkKernelArm])
    ranks_al digest_local _ kernelAl (by simp) off count input T (Nat.le_refl _) hT

end Keccaktree.Kernels.ScalarX1.InPlaceAll
