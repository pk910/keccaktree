import Keccaktree.Kernels.Rv64X1.All
import Keccaktree.Asm.RiscvAliasTrace
import Keccaktree.Kernels.Rv64X1.InPlace.GenSE
import Keccaktree.Kernels.Rv64X1.InPlace.GenSB
import Keccaktree.Kernels.Rv64X1.InPlace.GenSX
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `keccaktree_keccak256_rv64_x1` (RISC-V) in place (`out == in`), for every count

The access condition along the separate-region run (`access_all`, at `vlmax = 2`; every vector length
by `Riscv.accessRun_vlmax`, the kernel has no `vsetvli`), mirroring `All.rv64_x1_all`: the generated
segments' footprint summaries (`InPlace.Gen*`, `(Riscv.alIsa 2).chain_access` at relocation `rho m`) and
the concrete steps between them (the back edge `ld; addi; sd; beq` and `j` on the spilled count, the
entry `bnez`, the final `ret`), none of which touches input or output.

`kernelAl vlmax` (`LibRvAl.mkKernelRvAl`) and **`lib_inplace_rv64_x1`**: the in-place library on
`[rv64_x1]`, any `vl` at entry, every vector length.
-/
namespace Keccaktree.Kernels.Rv64X1.InPlaceAll
open Keccaktree.Asm Keccaktree.Asm.X86 Keccaktree.Kernels.RiscvCommon Keccaktree.Kernels.Rv64X1.All
open Keccaktree.Asm.Riscv (setR getR brHolds run_one exec_ld_word exec_sd_word exec_opi_eq exec_br_num exec_j_eq
  exec_ret_eq getR_zero getR_pos gprWord_dec setR_getGD_same setR_getGD_other next_getGD next_halted next_pc setR_halted
  setR_pc gx_word)
open Keccaktree.Kernels.Rv64X1 (prog rodata)

/-- The access condition at `vlmax = 2` (the vector length of `All.RV`). -/
abbrev AR := Riscv.AccessRun 2 rodata prog

theorem sp_cells (s : State (BitVec 64)) (hsp : s.getGD 2 = gprWord ⟨rStack, 1048352⟩) (c : Region × Int)
    (hc : c ∈ storeCells ⟨rStack, 1048352 + 80⟩ 1) : c.1 ≠ rInput ∧ c.1 ≠ rOutput := by
  simp only [storeCells, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hc
  subst hc; decide

theorem addr_sp (s : State (BitVec 64)) (hsp : s.getGD 2 = gprWord ⟨rStack, 1048352⟩) :
    Arm.addr s 2 80 = some ⟨rStack, 1048352 + 80⟩ := by
  simp only [Arm.addr, gx_word s 2 _ hsp sp_wf, Option.map_some]

set_option maxRecDepth 100000 in
/-- The back edge `ld t0, 80(sp); addi t0, t0, -1; sd t0, 80(sp); beq t0, zero, exit` touches only the stack. -/
theorem back_access (Sb : State (BitVec 64)) (n : Int) (hh : Sb.halted = false) (he : Sb.err = false) (hpc : Sb.pc = 5410)
    (hsp : Sb.getGD 2 = gprWord ⟨rStack, 1048352⟩) (hcnt : Sb.mem rStack 131054 = gprWord ⟨0, n⟩)
    (h0 : 1 ≤ n) (h1 : n < 2 ^ 55) (m : Nat) (b bf : Int) (hrest : AR m b bf (B4 Sb n)) :
    AR (4 + m) b bf Sb := by
  have hld := exec_ld_word 2 rodata Sb 5 2 80 ⟨rStack, 1048352⟩ hh hsp sp_wf (by decide) (by decide)
  rw [show ((⟨rStack, 1048352⟩ : Addr).off + 80) / 8 = 131054 by decide, show (⟨rStack, 1048352⟩ : Addr).region = rStack from rfl,
    hcnt] at hld
  have e1 : Riscv.exec 2 rodata (.ld 5 2 80) Sb = B1 Sb n := by rw [hld]; rfl
  have hh1 : (B1 Sb n).halted = false := by simp only [B1, next_halted, setR_halted, hh]
  have hpc1 : (B1 Sb n).pc = 5411 := by simp only [B1, next_pc, setR_pc, hpc]
  have hg1 : getR (B1 Sb n) 5 = gprWord ⟨0, n⟩ := by
    rw [getR_pos _ 5 (by decide), B1, next_getGD, setR_getGD_same Sb 5 (by decide) (by decide)]
  have e2 : Riscv.exec 2 rodata (.opi 5 5 .addi 0xffffffffffffffff#64) (B1 Sb n) = B2 Sb n := by
    rw [exec_opi_eq 2 rodata _ 5 5 .addi _ hh1, B2]
    show Riscv.next (setR (B1 Sb n) 5 (getR (B1 Sb n) 5 + 0xffffffffffffffff#64)) = _
    rw [hg1, gprWord_dec]
  have hh2 : (B2 Sb n).halted = false := by simp only [B2, next_halted, setR_halted, hh1]
  have hpc2 : (B2 Sb n).pc = 5412 := by simp only [B2, next_pc, setR_pc, hpc1]
  have hsp2 : (B2 Sb n).getGD 2 = gprWord ⟨rStack, 1048352⟩ := by
    rw [B2, next_getGD, setR_getGD_other _ 5 2 (by decide), B1, next_getGD, setR_getGD_other _ 5 2 (by decide), hsp]
  have hg2 : getR (B2 Sb n) 5 = gprWord ⟨0, n - 1⟩ := by
    rw [getR_pos _ 5 (by decide), B2, next_getGD, setR_getGD_same _ 5 (by decide) (by decide)]
  have hsd := exec_sd_word 2 rodata (B2 Sb n) 5 2 80 ⟨rStack, 1048352⟩ hh2 hsp2 sp_wf (by decide) (by decide)
  rw [show ((⟨rStack, 1048352⟩ : Addr).off + 80) / 8 = 131054 by decide, show (⟨rStack, 1048352⟩ : Addr).region = rStack from rfl,
    hg2] at hsd
  have e3 : Riscv.exec 2 rodata (.sd 5 2 80) (B2 Sb n) = B3 Sb n := by rw [hsd, B3]
  have hh3 : (B3 Sb n).halted = false := by simp only [B3, next_halted]; exact hh2
  have hpc3 : (B3 Sb n).pc = 5413 := by simp only [B3, next_pc, hpc2]
  have hg3 : getR (B3 Sb n) 5 = gprWord ⟨0, n - 1⟩ := by
    rw [getR_pos _ 5 (by decide), B3, next_getGD, Riscv.getGD_withMem]; rw [getR_pos _ 5 (by decide)] at hg2; exact hg2
  have e4 : Riscv.exec 2 rodata (.br .eq 5 0 5415) (B3 Sb n) = B4 Sb n := by
    rw [exec_br_num 2 rodata _ .eq 5 0 5415 (n - 1) 0 hh3 hg3 (getR_zero _)
        (by show 0 ≤ n - 1 ∧ n - 1 < 2 ^ 55; constructor <;> omega) (by decide), B4]
  have hc := B4_ctrl Sb n
  have he4 : (B4 Sb n).err = false := hc.2.2.2.2.2.2.2.2.2.1.trans he
  rw [show 4 + m = ((m + 1) + 1 + 1) + 1 by omega]
  apply Riscv.accessRun_step 2 rodata prog _ _ _ Sb hh
  · rw [hpc, prog_5410, e1]; exact he4
  · intro cl hcl; rw [hpc, prog_5410] at hcl; simp only [Riscv.reads, addr_sp Sb hsp] at hcl
    exact (sp_cells Sb hsp cl hcl).1
  · intro cl hcl; rw [hpc, prog_5410] at hcl; simp [Riscv.writes] at hcl
  rw [hpc, prog_5410, e1]
  apply Riscv.accessRun_step 2 rodata prog _ _ _ (B1 Sb n) hh1
  · rw [hpc1, prog_5411, e2]; exact he4
  · intro cl hcl; rw [hpc1, prog_5411] at hcl; simp [Riscv.reads] at hcl
  · intro cl hcl; rw [hpc1, prog_5411] at hcl; simp [Riscv.writes] at hcl
  rw [hpc1, prog_5411, e2]
  apply Riscv.accessRun_step 2 rodata prog _ _ _ (B2 Sb n) hh2
  · rw [hpc2, prog_5412, e3]; exact he4
  · intro cl hcl; rw [hpc2, prog_5412] at hcl; simp [Riscv.reads] at hcl
  · intro cl hcl; rw [hpc2, prog_5412] at hcl; simp only [Riscv.writes, addr_sp _ hsp2] at hcl
    exact sp_cells _ hsp2 cl hcl
  rw [hpc2, prog_5412, e3]
  apply Riscv.accessRun_step 2 rodata prog _ _ _ (B3 Sb n) hh3
  · rw [hpc3, prog_5413, e4]; exact he4
  · intro cl hcl; rw [hpc3, prog_5413] at hcl; simp [Riscv.reads] at hcl
  · intro cl hcl; rw [hpc3, prog_5413] at hcl; simp [Riscv.writes] at hcl
  rw [hpc3, prog_5413, e4]
  exact hrest

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **One iteration**: the body hashes node `m = off + k` with every input load at or above `4m` and
its digest stored below `4m + 4`; then the back edge, and `j` unless it is the last iteration. -/
theorem body_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (k : Nat) (S : State (BitVec 64)) (hk : k < c) (hH : Head off c input S0 k S) :
    AR 5373 (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S ∧
    (k + 1 < c → AR 5374 (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S) := by
  obtain ⟨hcut, hok, hcnt, hin, hpre, hdig⟩ := hH
  have hρ := rho_ok (off + k)
  have hw : (rho (off + k)).within GenSB.B := rho_within (off + k) (by omega)
  have hseg : AR GenSB.segLen (4 * ((off + k : Nat) : Int)) (4 * ((off + k : Nat) : Int) + 4) S := by
    rw [← InPlace.GenSB.len]
    apply (Riscv.alIsa 2).chain_access (rho (off + k)) hρ hw InPlace.GenSB.certs _ _ _ InPlace.GenSB.chain
      (by intro C hC; simp only [InPlace.GenSB.certs, List.head?_cons, Option.mem_def, Option.some.injEq] at hC; subst hC; exact hcut) hok
    rw [InPlace.GenSB.sums, rho_wshift_in, rho_wshift_out]
    simp only [SummOk, nextB]
    simp [SummOk, nextB] <;> omega
  have sr := GenSB.seg_run (rho (off + k)) hρ hw S hcut hok
  have fr := GenSB.seg_frame (rho (off + k)) hρ hw S hcut hok
  generalize hSb : GenSB.segAt25 S = Sb at sr fr
  obtain ⟨hrun, hokb, hcutb⟩ := sr
  have fb := cut_fields _ _ _ _ hcutb
  have hsp : Sb.getGD 2 = gprWord ⟨rStack, 1048352⟩ := by
    have e1 := cut_word (rho (off + k)) hρ GenSB.ctl25 GenSB.sc25 Sb hcutb 258 (Or.inl (by decide))
    rw [show cutVar GenSB.ctl25 GenSB.sc25 258 = .ptr ⟨rStack, 1048352⟩ by decide +kernel, reloc_ptr_stack] at e1
    rw [← envOf_gdVar Sb 2 (by decide)]
    exact cut_ptr GenSB.ctl25 Sb 258 (by decide) _ e1
  have hcntb : Sb.mem rStack 131054 = gprWord ⟨0, (c : Int) - k⟩ := by
    rw [fr rStack 131054 (by rw [rho_wshift_stack]; decide), hcnt]
  have hpcb : Sb.pc = 5410 := fb.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hhb : Sb.halted = false := hokb.2.1
  have hb' : 64 * (off + c) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have h55 : (c : Int) - k < 2 ^ 55 := by rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; omega
  have hrunS : RV.run rodata prog GenSB.segLen S = Sb := hrun
  refine ⟨?_, fun hk1 => ?_⟩
  · rw [show 5373 = GenSB.segLen + (4 + 0) by rw [body_len]]
    apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ S hseg
    rw [hrunS]
    exact back_access Sb _ hhb hokb.1 hpcb hsp hcntb (by omega) h55 0 _ _ (Int.le_refl _)
  · have hc := B4_ctrl Sb ((c : Int) - k)
    have hpcU : (B4 Sb ((c : Int) - k)).pc = 5414 := by
      rw [B4_pc _ _ hpcb, if_neg (by omega)]
    have hhU : (B4 Sb ((c : Int) - k)).halted = false := hc.2.2.2.2.2.2.2.2.1.trans hhb
    have heU : (B4 Sb ((c : Int) - k)).err = false := hc.2.2.2.2.2.2.2.2.2.1.trans hokb.1
    rw [show 5374 = GenSB.segLen + (4 + 1) by rw [body_len]]
    apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ S hseg
    rw [hrunS]
    apply back_access Sb _ hhb hokb.1 hpcb hsp hcntb (by omega) h55 1 _ _
    apply Riscv.accessRun_step 2 rodata prog 0 _ _ _ hhU
    · rw [hpcU, prog_5414, exec_j_eq 2 rodata _ 20 hhU]; exact heU
    · intro cl hcl; rw [hpcU, prog_5414] at hcl; simp [Riscv.reads] at hcl
    · intro cl hcl; rw [hpcU, prog_5414] at hcl; simp [Riscv.writes] at hcl
    · exact Int.le_refl _

/-- **The loop**: from the head of iteration `k`, the remaining iterations. -/
theorem loop_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    ∀ d k (S : State (BitVec 64)), k + d + 1 = c → Head off c input S0 k S →
      AR (5374 * d + 5373) (4 * ((off + k : Nat) : Int)) (4 * ((off + c : Nat) : Int)) S := by
  intro d
  induction d with
  | zero =>
    intro k S hk hH
    have := (body_access off c input S0 hb k S (by omega) hH).1
    rw [show ((off + c : Nat) : Int) = (off + k : Nat) + 1 by omega, show 5374 * 0 + 5373 = 5373 from rfl]
    rw [show 4 * (((off + k : Nat) : Int) + 1) = 4 * ((off + k : Nat) : Int) + 4 by omega]
    exact this
  | succ d ih =>
    intro k S hk hH
    have h1 := (iter off c input S0 hb k S (by omega) hH).1 (by omega)
    rw [show 5374 * (d + 1) + 5373 = 5374 + (5374 * d + 5373) by omega]
    apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ S ((body_access off c input S0 hb k S (by omega) hH).2 (by omega))
    have := ih (k + 1) _ (by omega) h1
    rw [show ((off + (k + 1) : Nat) : Int) = (off + k : Nat) + 1 by omega] at this
    rw [show 4 * ((off + k : Nat) : Int) + 4 = 4 * (((off + k : Nat) : Int) + 1) by omega]
    exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The epilogue (restores, `ret`) touches neither input nor output. -/
theorem exit_access (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (hm : 64 * m ≤ 2 ^ 54)
    (U : State (BitVec 64)) (hX : ExitAt off c input S0 m U) (b : Int) : AR 15 b b U := by
  obtain ⟨hcut, hok, hpre, hdig⟩ := hX
  have hρ := rho_ok m
  have hw : (rho m).within GenSX.B := rho_within m hm
  have hseg : AR GenSX.segLen b b U := by
    have := (Riscv.alIsa 2).seg1_access GenSX.cert0 (rho m) hρ hw U hcut hok InPlace.GenSX.sum0 b
    exact this
  have sr := GenSX.seg_run (rho m) hρ hw U hcut hok
  generalize hSx : GenSX.segAt1 U = Sx at sr
  obtain ⟨hrun, hokx, hcutx⟩ := sr
  have fx := cut_fields _ _ _ _ hcutx
  have hpc : Sx.pc = 5429 := fx.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hrunU : RV.run rodata prog GenSX.segLen U = Sx := hrun
  rw [show 15 = GenSX.segLen + 1 by rw [exit_len]]
  apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ U hseg
  rw [hrunU]
  apply Riscv.accessRun_step 2 rodata prog 0 _ _ Sx hokx.2.1
  · rw [hpc, prog_5429, exec_ret_eq 2 rodata Sx hokx.2.1]; exact hokx.1
  · intro cl hc; rw [hpc, prog_5429] at hc; simp [Riscv.reads] at hc
  · intro cl hc; rw [hpc, prog_5429] at hc; simp [Riscv.writes] at hc
  · exact Int.le_refl _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The access condition of a whole call** (`c` nodes at node offset `off`, `vlmax = 2`): the bound
starts at `4·off` and ends at `4·(off + c)`. -/
theorem access_all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    AR (32 + 5374 * c) (4 * (off : Int)) (4 * ((off + c : Nat) : Int)) S := by
  have hρ := rho_ok off
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hh : S.halted = false := hE.ok.2.1
  have hpc0 : S.pc = 1 := hE.ctrl.2.2.2.2.2.2.2.1
  have hcwf : (⟨0, (c : Int)⟩ : Addr).wf := by
    show 0 ≤ (c : Int) ∧ (c : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hbr : Riscv.exec 2 rodata (.br .ne 12 0 3) S = { S with pc := if brHolds .ne (c : Int) 0 then 3 else S.pc + 1 } :=
    exec_br_num 2 rodata S .ne 12 0 3 c 0 hh ((getR_pos S 12 (by decide)).trans hE.a2) (getR_zero S) hcwf (by decide)
  -- the entry `bnez a2`: no memory
  have a1 : ∀ (m : Nat) (bf : Int), AR m (4 * (off : Int)) bf { S with pc := if brHolds .ne (c : Int) 0 then 3 else S.pc + 1 } →
      AR (m + 1) (4 * (off : Int)) bf S := by
    intro m bf hrest
    apply Riscv.accessRun_step 2 rodata prog _ _ _ S hh
    · rw [hpc0, prog_1, hbr]; exact hE.ok.1
    · intro cl hc; rw [hpc0, prog_1] at hc; simp [Riscv.reads] at hc
    · intro cl hc; rw [hpc0, prog_1] at hc; simp [Riscv.writes] at hc
    · rw [hpc0, prog_1, hbr]; exact hrest
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- no node: `j` to the `ret`
    subst hc
    generalize hT1 : ({ S with pc := if brHolds .ne ((0 : Nat) : Int) 0 then 3 else S.pc + 1 } : State (BitVec 64)) = T1 at a1
    have hT1pc : T1.pc = 2 := by rw [← hT1]; simp [brHolds, hpc0]
    have hT1h : T1.halted = false := by rw [← hT1]; exact hh
    have hT1e : T1.err = false := by rw [← hT1]; exact hE.ok.1
    rw [show 32 + 5374 * 0 = 31 + 1 from rfl]
    apply a1
    rw [show (31 : Nat) = 30 + 1 from rfl]
    apply Riscv.accessRun_step 2 rodata prog _ _ _ T1 hT1h
    · rw [hT1pc, prog_2, exec_j_eq 2 rodata T1 5429 hT1h]; exact hT1e
    · intro cl hc; rw [hT1pc, prog_2] at hc; simp [Riscv.reads] at hc
    · intro cl hc; rw [hT1pc, prog_2] at hc; simp [Riscv.writes] at hc
    rw [hT1pc, prog_2, exec_j_eq 2 rodata T1 5429 hT1h, show (30 : Nat) = 29 + 1 from rfl]
    apply Riscv.accessRun_step 2 rodata prog _ _ _ { T1 with pc := 5429 } hT1h
    · rw [show ({ T1 with pc := 5429 } : State (BitVec 64)).pc = 5429 from rfl, prog_5429,
        exec_ret_eq 2 rodata { T1 with pc := 5429 } hT1h]; exact hT1e
    · intro cl hc; rw [show ({ T1 with pc := 5429 } : State (BitVec 64)).pc = 5429 from rfl, prog_5429] at hc
      simp [Riscv.reads] at hc
    · intro cl hc; rw [show ({ T1 with pc := 5429 } : State (BitVec 64)).pc = 5429 from rfl, prog_5429] at hc
      simp [Riscv.writes] at hc
    rw [show ({ T1 with pc := 5429 } : State (BitVec 64)).pc = 5429 from rfl, prog_5429,
      exec_ret_eq 2 rodata { T1 with pc := 5429 } hT1h]
    -- halted: the remaining steps keep the bound
    show (Riscv.alIsa 2).AccessRun rodata prog (28 + 1) _ _ _
    simp [AlIsa.AccessRun]
  · have hbrc : brHolds .ne (c : Int) 0 = true := by simp [brHolds]; omega
    rw [hbrc] at a1
    generalize hT1 : ({ S with pc := if true = true then 3 else S.pc + 1 } : State (BitVec 64)) = T1 at a1
    have hT1pc : T1.pc = 3 := by rw [← hT1]; rfl
    have hT1ok : SliceCert.Ok T1 := by rw [← hT1]; exact hE.ok
    have hT1env : ∀ i, envOf T1 i = envOf S i := by intro i; rw [← hT1]; rfl
    have hT1mem : T1.mem = S.mem := by rw [← hT1]
    have hwf_in : (⟨rInput, 64 * (off : Int)⟩ : Addr).wf := by
      show 0 ≤ 64 * (off : Int) ∧ 64 * (off : Int) < 2 ^ 55
      rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
    have hwf_out : (⟨rOutput, 32 * (off : Int)⟩ : Addr).wf := by
      show 0 ≤ 32 * (off : Int) ∧ 32 * (off : Int) < 2 ^ 55
      rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
    have hc0 : relocState (rho off) (cutOf GenSE.ctl0 GenSE.sc0) = cutOf GenSE.ctl0 T1 := by
      apply relocState_cutOf (rho off) GenSE.ctl0 GenSE.sc0 T1
      · intro i hi
        simp only [GenSE.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · rw [cutVar_ptr_of GenSE.ctl0 T1 258 ⟨rStack, 1048576⟩ (by decide)
              ((hT1env 258).trans ((envOf_gdVar S 2 (by decide)).trans hE.sp)) (by decide) (by decide),
            show cutVar GenSE.ctl0 GenSE.sc0 258 = .ptr ⟨rStack, 1048576⟩ by decide +kernel, reloc_ptr_stack]
        · rw [cutVar_ptr_of GenSE.ctl0 T1 266 ⟨rOutput, 32 * (off : Int)⟩ (by decide)
              ((hT1env 266).trans ((envOf_gdVar S 10 (by decide)).trans hE.a0)) hwf_out (by show rOutput ≠ 0; decide),
            show cutVar GenSE.ctl0 GenSE.sc0 266 = .ptr ⟨rOutput, 0⟩ by decide +kernel, reloc_ptr_out, Int.zero_add]
        · rw [cutVar_ptr_of GenSE.ctl0 T1 267 ⟨rInput, 64 * (off : Int)⟩ (by decide)
              ((hT1env 267).trans ((envOf_gdVar S 11 (by decide)).trans hE.a1)) hwf_in (by show rInput ≠ 0; decide),
            show cutVar GenSE.ctl0 GenSE.sc0 267 = .ptr ⟨rInput, 0⟩ by decide +kernel, reloc_ptr_in, Int.zero_add]
      · intro i hi h; simp only [GenSE.ctl0, List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
      · obtain ⟨g, k, z, cf, n, v, l, p, d⟩ := hE.ctrl
        have e : T1.g = S.g ∧ T1.k = S.k ∧ T1.zf = S.zf ∧ T1.cf = S.cf ∧ T1.nf = S.nf ∧ T1.vf = S.vf ∧ T1.vl = S.vl ∧
            T1.depth = S.depth := by rw [← hT1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := e
        rw [e1, e2, e3, e4, e5, e6, e7, e8, hT1pc, g, k, z, cf, n, v, l, d]
        decide +kernel
    have hw0 : (rho off).within (2 ^ 54) := rho_within off (by omega)
    -- E: frame stores and spills (stack only)
    have aE : AR GenSE.segLen (4 * (off : Int)) (4 * (off : Int)) T1 := by
      have := (Riscv.alIsa 2).seg1_access GenSE.cert0 (rho off) hρ hw0 T1 hc0 hT1ok InPlace.GenSE.sum0 (4 * (off : Int))
      exact this
    have s1 := GenSE.seg_run (rho off) hρ hw0 T1 hc0 hT1ok
    have f1 := GenSE.seg_frame (rho off) hρ hw0 T1 hc0 hT1ok
    have m1 := GenSE.seg_moves (rho off) hρ hw0 T1 hc0 hT1ok 2097155 268 (by simp)
    generalize hT2 : GenSE.segAt1 T1 = T2 at s1 f1 m1
    obtain ⟨hrun1, hok1, hcut1⟩ := s1
    have ft1 := cut_fields _ _ _ _ hcut1
    have hH : Head off c input S 0 T2 := by
      refine ⟨?_, hok1, ?_, fun q => (f1 rInput q rfl).trans ((congrFun (congrFun hT1mem rInput) q).trans (hE.inp q)),
        fun q _ => (f1 rOutput q rfl).trans (congrFun (congrFun hT1mem rOutput) q),
        fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      · apply cut_transfer (rho off) (rho (off + 0)) hρ hρ GenSE.ctl1 GenSB.ctl0 GenSE.sc1 GenSB.sc0 T2 T2 hcut1
          (hL_dec _ _ (by decide +kernel)) (fun i _ => rfl) (hval_same _ _ _ _ _ (by decide +kernel))
        obtain ⟨g1, k1, z1, c1, n1, v1, l1, p1, d1⟩ := ft1
        exact ⟨g1.trans (by decide +kernel), k1.trans (by decide +kernel), z1.trans (by decide +kernel),
          c1.trans (by decide +kernel), n1.trans (by decide +kernel), v1.trans (by decide +kernel),
          l1.trans (by decide +kernel), p1.trans (by decide +kernel), d1.trans (by decide +kernel)⟩
      · rw [rho_var_stack off 2097155 (by decide) (by decide +kernel), Reloc.var_lt (rho off) 268 (by decide)] at m1
        rw [show (2097155 : Nat) = memVar rStack 131054 by decide +kernel, envOf_mem] at m1
        rw [m1, hT1env, (envOf_gdVar S 12 (by decide) : envOf S 268 = S.getGD 12), hE.a2]
        simp
    have hl := loop off c input S hb (c - 1) 0 T2 (by omega) hH
    have al := loop_access off c input S hb (c - 1) 0 T2 (by omega) hH
    rw [show ((off + 0 : Nat) : Int) = (off : Int) by simp] at al
    have ae := exit_access off c input S (off + c - 1) (by omega) _ hl (4 * ((off + c : Nat) : Int))
    have hrun1' : RV.run rodata prog GenSE.segLen T1 = T2 := hrun1
    rw [show 32 + 5374 * c = (GenSE.segLen + ((5374 * (c - 1) + 5373) + 15)) + 1 by rw [entry_len]; omega]
    apply a1
    apply Riscv.accessRun_add 2 rodata prog _ _ _ _ _ T1 aE
    rw [hrun1']
    exact Riscv.accessRun_add 2 rodata prog _ _ _ _ _ T2 al ae

/-! ## The in-place library on `[rv64_x1]` -/

/-- The access theorem of `rv64_x1` at every vector length (`LibRvAl.AccessThmRv`). -/
theorem access_thm (vlmax : Nat) : LibRvAl.AccessThmRv vlmax rodata prog 1 (fun _ c => 32 + 5374 * c) := by
  intro off c input S hE hb hpc
  obtain ⟨⟨g, k, z, cf, n, v, l, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩ := hE
  have hE' : Entry off c input S := ⟨⟨g, k, z, cf, n, v, l, hpc, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩
  refine ⟨4 * ((off + c : Nat) : Int),
    Riscv.accessRun_vlmax 2 vlmax rodata prog scalar _ _ _ _ (access_all off c input S hE' hb), ?_⟩
  intro next done _ ht _
  obtain ⟨-, -, -, hout⟩ := norm_thm vlmax off c input S ⟨⟨g, k, z, cf, n, v, l, d⟩, hok, ha2, hsp, ha1, ha0, hin⟩ hb hpc
  rcases hout with ⟨ht', -⟩ | ⟨nx, dn, -, hmem, -⟩
  · exact absurd (ht'.symm.trans ht) (by simp)
  · simp at hmem

/-- `keccaktree_keccak256_rv64_x1` as a kernel of the in-place RISC-V library (any `vl` at entry). -/
def kernelAl (vlmax : Nat) : Library.KernelThm (Riscv.alIsa vlmax).isaAl LibRvAl.EntryRvAl Digest :=
  LibRvAl.mkKernelRvAl vlmax (LibTable.sym "rv64_x1") 0 [] rodata prog 1 (fun _ c => 32 + 5374 * c)
    (Riscv.vlAnn RvVl.rv64_x1) RvVl.rv64_x1_ok RvVl.entries.1 (norm_thm vlmax) (access_thm vlmax)

theorem ranks_al (vlmax : Nat) : Library.RanksOk [kernelAl vlmax] := by
  intro K hK t ht
  simp only [List.mem_singleton] at hK
  subst hK
  simp [kernelAl, LibRvAl.mkKernelRvAl, LibAliasGen.mkKernelAlG, LibRv.mkKernelRv] at ht

/-- **The in-place library theorem on the table `[rv64_x1]`** (RISC-V, VLEN = 64·`vlmax`, one buffer,
any `vl` at entry): the library run halts without a model fault with every node's digest in the
buffer. -/
theorem lib_inplace_rv64_x1 (vlmax : Nat) (off count : Nat) (input : Int → BitVec 64) (T : State (BitVec 64))
    (hT : LibRvAl.EntryRvAl (LibTable.sym "rv64_x1") off count input T) :
    Library.LibOk [kernelAl vlmax] (kernelAl vlmax) off count input T :=
  Library.lib_correct [kernelAl vlmax] 0 (by simp [kernelAl, LibRvAl.mkKernelRvAl, LibAliasGen.mkKernelAlG, LibRv.mkKernelRv])
    (ranks_al vlmax) LibX86.digest_local _ (kernelAl vlmax) (by simp) off count input T (Nat.le_refl _) hT

end Keccaktree.Kernels.Rv64X1.InPlaceAll
