#!/usr/bin/env python3
"""Render the all-count theorem `Keccaktree/Kernels/<Ns>/All.lean` of an AArch64 kernel from a template
(templates/arm_<kind>.lean.in) and the kernel's frame indices.  Usage: gen_all_arm.py <kernel>"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'templates'))
import arm_common as C

KERNELS = {
    # kernel: (kind, Ns, symbol, params)
    'sha3_x2': ('x2', 'Sha3X2', 'keccaktree_keccak256_sha3_x2', dict(SUBS=1597, RET=1603)),
    'neon_x2': ('x2', 'NeonX2', 'keccaktree_keccak256_neon_x2', dict(SUBS=3786, RET=3792)),
}

FT = 'fT'


def ctrl_refine(st, f, pc_tac, flags=None):
    """the control-part goals of `cut_transfer` for a state `st` whose control fields are those of the end
    cut fields `f` (g, k, vl, depth), with `pc` closed by `pc_tac`; flags `rfl` (normalised) unless given"""
    fl = 'rfl, rfl, rfl, rfl' if flags is None else '?_, ?_, ?_, ?_'
    s = f'      refine ⟨?_, ?_, {fl}, ?_, ?_, ?_⟩\n'
    s += f'      · show {st}.g = _; rw [{f}g]; decide +kernel\n'
    s += f'      · show {st}.k = _; rw [{f}k]; decide +kernel\n'
    if flags is not None:
        for t in flags:
            s += f'      · {t}\n'
    s += f'      · show {st}.vl = _; rw [{f}vl]; decide +kernel\n'
    s += f'      · show {st}.pc = _; {pc_tac}\n'
    s += f'      · show {st}.depth = _; rw [{f}d]; decide +kernel\n'
    return s


def iter_case(kind, P):
    """one batch of the x2 loop for r = c - 2k nodes left: a (r ≥ 3, back edge), b (r = 2), c (r = 1)"""
    HX = {'a': 'GenSHa', 'b': 'GenSHb', 'c': 'GenSHc'}[kind]
    BX = 'GenSBo' if kind == 'c' else 'GenSBe'
    NB = 1 if kind == 'c' else 2
    hyp = {'a': '(hr : 2 * k + 3 ≤ c)', 'b': '(hr : c = 2 * k + 2)', 'c': '(hr : c = 2 * k + 1)'}[kind]
    ZV, CV, NV = {'a': ('false', 'true', 'false'), 'b': ('true', 'true', 'false'), 'c': ('false', 'false', 'true')}[kind]
    GT = 'true' if kind == 'a' else 'false'
    dz = 'decide_eq_true' if ZV == 'true' else 'decide_eq_false'
    dc = 'decide_eq_true' if CV == 'true' else 'decide_eq_false'
    dn = 'decide_eq_true' if NV == 'true' else 'decide_eq_false'
    IT, SUBS = P['IT'], P['SUBS']
    concl = ('Head off c input S0 (k + 1) (Arm.isa.run rodata prog %d S)' % IT if kind == 'a'
             else 'ExitAt off c input S0 (off + 2 * k) (Arm.isa.run rodata prog %d S)' % IT)
    inv0 = 'inv0_e' if NB == 2 else 'inv0_o'
    s = f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- A batch with {"r ≥ 3 nodes left (back to the loop head)" if kind == "a" else ("two nodes left (to the epilogue)" if kind == "b" else "one node left (node 0 duplicated; to the epilogue)")}. -/
theorem iter_{kind} (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (hb : 64 * (off + c) ≤ 2 ^ 54)
    (k : Nat) (S : State (BitVec 64)) {hyp} (hH : Head off c input S0 k S) :
    {concl} := by
  have hH' := hH
  obtain ⟨hcut, hok, hcnt, hin, hpre, hdig⟩ := hH'
  obtain ⟨T', hrun4, hcutT, hokT, hcntT, hpcT, hmemT⟩ := pre off c input S0 hb k S (by omega) hH
  have hb' : 64 * (off + c) ≤ 18014398509481984 := by
    have : (2 : Nat) ^ 54 = 18014398509481984 := rfl
    omega
  have hρ := rho_ok (off + 2 * k)
  have hw : (rho (off + 2 * k)).within (2 ^ 54) := rho_within _ (by omega)
  have fT := cut_fields _ _ _ _ hcutT
  have hz : decide ((c : Int) - 2 * k = 2) = {ZV} := {dz} (by omega)
  have hcf : decide (2 ≤ (c : Int) - 2 * k) = {CV} := {dc} (by omega)
  have hn : decide ((c : Int) - 2 * k < 2) = {NV} := {dn} (by omega)
  generalize hV : Arm.next (Arm.setFlags T' ((c : Int) - 2 * k) 2) = V at hrun4
  have hVenv : ∀ i, envOf V i = envOf T' i := by intro i; rw [← hV]; rfl
  have hVok : SliceCert.Ok V := by rw [← hV]; exact hokT
  have hVmem : V.mem = S.mem := by rw [← hV, ← hmemT]; rfl
  have hVx2 : V.getGD 2 = gprWord ⟨0, (c : Int) - 2 * k⟩ := by rw [← hV]; exact hcntT
  -- the two `csel`, with the flags of `cmp`
  have hcH : relocState (rho (off + 2 * k)) (cutOf {HX}.ctl0 {HX}.sc0) = cutOf {HX}.ctl0 V := by
    apply cut_transfer (rho (off + 2 * k)) _ hρ hρ GenSH.ctl1 {HX}.ctl0 GenSH.sc1 {HX}.sc0 T' V hcutT
      (hL_dec _ _ (by decide +kernel)) (fun i _ => hVenv i) (hval_same _ _ _ _ _ (by decide +kernel))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hV]; show T'.g = _; rw [fT.1]; decide +kernel
    · rw [← hV]; show T'.k = _; rw [fT.2.1]; decide +kernel
    · rw [← hV]; show decide ((c : Int) - 2 * k = 2) = _; rw [hz]; decide +kernel
    · rw [← hV]; show decide (2 ≤ (c : Int) - 2 * k) = _; rw [hcf]; decide +kernel
    · rw [← hV]; show decide ((c : Int) - 2 * k < 2) = _; rw [hn]; decide +kernel
    · rw [← hV]; show false = _; decide +kernel
    · rw [← hV]; show T'.vl = _; rw [fT.2.2.2.2.2.2.1]; decide +kernel
    · rw [← hV]; show T'.pc + 1 = _; rw [hpcT]; decide +kernel
    · rw [← hV]; show T'.depth = _; rw [fT.2.2.2.2.2.2.2.2]; decide +kernel
  have sX := {HX}.seg_run _ hρ hw V hcH hVok
  have mX := {HX}.seg_moves _ hρ hw V hcH hVok 258 258 (by simp)
  have frX := {HX}.seg_frame _ hρ hw V hcH hVok
  rw [Reloc.var_lt _ 258 (by decide)] at mX
  generalize hW : {HX}.segAt1 V = W at sX mX frX
  obtain ⟨hrunX, hokW, hcutW⟩ := sX
  have fW := cut_fields _ _ _ _ hcutW
  have hWmem : ∀ r q, W.mem r q = S.mem r q := by intro r q; rw [frX r q rfl, hVmem]
  have hWx2 : W.getGD 2 = gprWord ⟨0, (c : Int) - 2 * k⟩ := by
    have e3 : envOf W 258 = W.getGD 2 := envOf_gdVar _ 2 (by decide)
    have e4 : envOf V 258 = V.getGD 2 := envOf_gdVar _ 2 (by decide)
    rw [← e3, mX, e4, hVx2]
  -- the batch, from any flags
  have hcB : relocState (rho (off + 2 * k)) (cutOf {BX}.ctl0 {BX}.sc0) = cutOf {BX}.ctl0 (norm W {BX}.sc0) := by
    apply cut_transfer (rho (off + 2 * k)) _ hρ hρ {HX}.ctl1 {BX}.ctl0 {HX}.sc1 {BX}.sc0 W (norm W {BX}.sc0) hcutW
      (hL_dec _ _ (by decide +kernel)) (fun i _ => rfl) (hval_same _ _ _ _ _ (by decide +kernel))
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show W.g = _; rw [fW.1]; decide +kernel
    · show W.k = _; rw [fW.2.1]; decide +kernel
    · show W.vl = _; rw [fW.2.2.2.2.2.2.1]; decide +kernel
    · show W.pc = _; rw [fW.2.2.2.2.2.2.2.1]; decide +kernel
    · show W.depth = _; rw [fW.2.2.2.2.2.2.2.2]; decide +kernel
  have hokW' : SliceCert.Ok (norm W {BX}.sc0) := hokW
  have hinW : ∀ q, (norm W {BX}.sc0).mem rInput q = input q := by
    intro q; show W.mem rInput q = _; rw [hWmem]; exact hin q
  have sB := {BX}.seg_run _ hρ hw _ hcB hokW'
  have frB := {BX}.seg_frame _ hρ hw _ hcB hokW'
  have datB := {BX}.seg_data _ hρ hw _ hcB hokW' _ ({inv0} input (norm W {BX}.sc0) (off + 2 * k) hinW)
  have mvB := {BX}.seg_moves _ hρ hw _ hcB hokW' 258 258 (by simp)
  have flB : Arm.isa.run rodata prog {BX}.segLen W = ({BX}.segAt25 (norm W {BX}.sc0)).withFlags W.zf W.cf W.nf W.vf :=
    {BX}.seg_flags _ hρ hw _ hcB hokW' W.zf W.cf W.nf W.vf
  rw [Reloc.var_lt _ 258 (by decide)] at mvB
  generalize hSb' : {BX}.segAt25 (norm W {BX}.sc0) = Sb' at sB frB datB mvB flB
  obtain ⟨_, hokb, hcutb⟩ := sB
  have fb := cut_fields _ _ _ _ hcutb
  generalize hSb : Sb'.withFlags W.zf W.cf W.nf W.vf = Sb at flB
  have hSbenv : ∀ i, envOf Sb i = envOf Sb' i := by intro i; rw [← hSb]; rfl
  have hhb : Sb.halted = false := by rw [← hSb]; exact hokb.2.1
  have hpcb : Sb.pc = {SUBS} := by rw [← hSb]; exact fb.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hcntb : Sb.getGD 2 = gprWord ⟨0, (c : Int) - 2 * k⟩ := by
    have e1 : envOf Sb 258 = Sb.getGD 2 := envOf_gdVar Sb 2 (by decide)
    have e2 : envOf (norm W {BX}.sc0) 258 = W.getGD 2 := envOf_gdVar _ 2 (by decide)
    rw [← e1, hSbenv, mvB, e2, hWx2]
  -- subs x2, x2, #2 ; b.gt loop
  have hsubs := Arm.exec_subs_num rodata Sb 2 2 2 ((c : Int) - 2 * k) hhb hcntb (wf_num _ (by omega) (by omega))
  generalize hVs : Arm.next (Arm.setFlags (Sb.setGD 2 (gprWord ⟨0, (c : Int) - 2 * k - 2⟩)) ((c : Int) - 2 * k) 2) = Vs at hsubs
  have hrunVs : Arm.isa.run rodata prog 1 Sb = Vs := by
    rw [Arm.run_one rodata prog Sb hhb, show prog.getD Sb.pc .nop = .subs 2 2 2 by rw [hpcb]; decide +kernel, hsubs]
  have hpcVs : Vs.pc = {SUBS + 1} := by rw [← hVs]; show Sb.pc + 1 = {SUBS + 1}; rw [hpcb]
  have hhVs : Vs.halted = false := by rw [← hVs]; exact hhb
  have hgt : Arm.condHolds Vs .gt = {GT} := by
    rw [← hVs]; show (!decide ((c : Int) - 2 * k = 2) && (decide ((c : Int) - 2 * k < 2) == false)) = {GT}
    rw [hz, hn]; rfl
  have hrunU : Arm.isa.run rodata prog 1 Vs = {{ Vs with pc := if Arm.condHolds Vs .gt then 5 else Vs.pc + 1 }} := by
    rw [Arm.run_one rodata prog Vs hhVs, show prog.getD Vs.pc .nop = .bcond .gt 5 by rw [hpcVs]; decide +kernel]
    exact Arm.exec_bcond_eq rodata Vs .gt 5 hhVs
  generalize hU : {{ Vs with pc := if Arm.condHolds Vs .gt then 5 else Vs.pc + 1 }} = U at hrunU
  have hlen : {IT} = 4 + {HX}.segLen + {BX}.segLen + 1 + 1 := by decide +kernel
  rw [hlen, Isa.run_add, Isa.run_add, Isa.run_add, Isa.run_add, hrun4, hrunX, flB, hrunVs, hrunU]
  -- the fields of U
  have hUmem : U.mem = Sb'.mem := by rw [← hU, ← hVs, ← hSb]; rfl
  have hUpc : U.pc = {5 if kind == "a" else SUBS + 2} := by
    rw [← hU]; show (if Arm.condHolds Vs .gt then 5 else Vs.pc + 1) = _
    rw [hgt, hpcVs]; rfl
  have hUenv : ∀ i, i ≠ 258 → envOf U i = envOf Sb' i := by
    intro i hi
    rw [← hSbenv i, ← Arm.envOf_setGD_other Sb 2 i (gprWord ⟨0, (c : Int) - 2 * k - 2⟩) (by omega), ← hU, ← hVs]; rfl
  have hUcnt : U.getGD 2 = gprWord ⟨0, (c : Int) - 2 * k - 2⟩ := by
    rw [← hU, ← hVs]; exact Arm.getGD_setGD_same Sb 2 _ (by decide)
  have hUg : U.g = Sb'.g.setIfInBounds 2 ⟨0, 0⟩ := by rw [← hU, ← hVs, ← hSb]; rfl
  have hUc : U.k = Sb'.k ∧ U.vl = Sb'.vl ∧ U.depth = Sb'.depth := by
    rw [← hU, ← hVs, ← hSb]; exact ⟨rfl, rfl, rfl⟩
  have hUok : SliceCert.Ok U := by rw [← hU, ← hVs, ← hSb]; exact hokb
  have hbi : ∀ q, U.mem rInput q = input q := by
    intro q; rw [hUmem, frB rInput q rfl]; exact hinW q
  have hbo : ∀ q : Int, q - 4 * ((off + 2 * k : Nat) : Int) < 0 → U.mem rOutput q = S.mem rOutput q := by
    intro q hq
    rw [hUmem, frB rOutput q (by rw [rho_wshift_out]; exact wok_out {NB} _ (Or.inl hq))]
    exact hWmem rOutput q
  have hdig' : ∀ n, n < 2 * k + {NB} → Digest input U (off + n) := by
    intro n hn
    by_cases hnk : n < 2 * k
    · apply digest_congr input S U (off + n) _ (hdig n hnk)
      intro w hw; exact hbo _ (by simp only [Int.ofNat_eq_coe]; omega)
'''
    if NB == 2:
        s += '''    · rcases (by omega : n = 2 * k + 0 ∨ n = 2 * k + 1) with rfl | rfl
      · rw [show off + (2 * k + 0) = (off + 2 * k) + 0 by omega]
        exact digest_congr input Sb' U _ (fun w _ => by rw [hUmem]) (dig_e0 input Sb' (off + 2 * k) datB)
      · rw [show off + (2 * k + 1) = (off + 2 * k) + 1 by omega]
        exact digest_congr input Sb' U _ (fun w _ => by rw [hUmem]) (dig_e1 input Sb' (off + 2 * k) datB)
'''
    else:
        s += '''    · rcases (by omega : n = 2 * k + 0) with rfl
      rw [show off + (2 * k + 0) = (off + 2 * k) + 0 by omega]
      exact digest_congr input Sb' U _ (fun w _ => by rw [hUmem]) (dig_o0 input Sb' (off + 2 * k) datB)
'''
    s += '''  have hL : ∀ (sc : State (BitVec 64)) (L' : List Nat), (L'.all fun i => decide (i ≠ 258)) = true →
      ∀ i ∈ L', envOf (norm U sc) i = envOf Sb' i := by
    intro sc L' hL' i hi
    have hne : i ≠ 258 := by have := List.all_eq_true.mp hL' i hi; simpa using this
    exact hUenv i hne
'''
    ctl = '''    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show U.g = _; rw [hUg, fb.1]; decide +kernel
    · show U.k = _; rw [hUc.1, fb.2.1]; decide +kernel
    · show U.vl = _; rw [hUc.2.1, fb.2.2.2.2.2.2.1]; decide +kernel
    · show U.pc = _; rw [hUpc]; decide +kernel
    · show U.depth = _; rw [hUc.2.2, fb.2.2.2.2.2.2.2.2]; decide +kernel
'''
    if kind == 'a':
        s += f'''  refine ⟨?_, hUok, ?_, hbi, fun q hq => (hbo q (by omega)).trans (hpre q hq), fun n hn => hdig' n (by omega)⟩
  · rw [show off + 2 * (k + 1) = (off + 2 * k) + 2 by omega, ← rho_add]
    apply cut_transfer (rho (off + 2 * k)) _ hρ (Reloc.add_ok _ _ hρ (rho_ok 2)) {BX}.ctl25 GenSH.ctl0 {BX}.sc25 GenSH.sc0 Sb'
      (norm U GenSH.sc0) hcutb (hL_dec _ _ (by decide +kernel)) (hL GenSH.sc0 _ (by decide +kernel))
      (hval_succ _ _ hρ (rho_ok 2) _ _ _ _ (by decide +kernel))
{ctl}  · rw [hUcnt]; exact congrArg (fun z : Int => gprWord ⟨0, z⟩) (by omega)

'''
    else:
        s += f'''  refine ⟨?_, hUok, fun q hq => (hbo q (by omega)).trans (hpre q hq), fun n hn => hdig' n (by omega)⟩
  apply cut_transfer (rho (off + 2 * k)) _ hρ hρ {BX}.ctl25 GenSX.ctl0 {BX}.sc25 GenSX.sc0 Sb' (norm U GenSX.sc0) hcutb
    (hL_dec _ _ (by decide +kernel)) (hL GenSX.sc0 _ (by decide +kernel)) (hval_same _ _ _ _ _ (by decide +kernel))
{ctl}
'''
    return s


def epilogue(P):
    XLEN, RET = P['XLEN'], P['RET']
    return f'''theorem prog_ret : prog.getD {RET} .nop = .ret := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The epilogue**: the `ldp` restores and `ret` halt with the memory unchanged. -/
theorem epilogue (off c : Nat) (input : Int → BitVec 64) (S0 : State (BitVec 64)) (m : Nat) (hm : 64 * m ≤ 2 ^ 54)
    (U : State (BitVec 64)) (hX : ExitAt off c input S0 m U) :
    (Arm.isa.run rodata prog {XLEN + 1} U).halted = true ∧ (Arm.isa.run rodata prog {XLEN + 1} U).err = false ∧
    (Arm.isa.run rodata prog {XLEN + 1} U).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (Arm.isa.run rodata prog {XLEN + 1} U).mem rOutput q = S0.mem rOutput q) ∧
    ∀ n, n < c → Digest input (Arm.isa.run rodata prog {XLEN + 1} U) (off + n) := by
  obtain ⟨hcut, hok, hpre, hdig⟩ := hX
  have hρ := rho_ok m
  have hw : (rho m).within GenSX.B := rho_within m hm
  have hok' : SliceCert.Ok (norm U GenSX.sc0) := hok
  have sr := GenSX.seg_run (rho m) hρ hw _ hcut hok'
  have fr := GenSX.seg_frame (rho m) hρ hw _ hcut hok'
  have fl : Arm.isa.run rodata prog GenSX.segLen U = (GenSX.segAt1 (norm U GenSX.sc0)).withFlags U.zf U.cf U.nf U.vf :=
    GenSX.seg_flags (rho m) hρ hw _ hcut hok' U.zf U.cf U.nf U.vf
  generalize hSx' : GenSX.segAt1 (norm U GenSX.sc0) = Sx' at sr fr fl
  obtain ⟨_, hokx, hcutx⟩ := sr
  have fx := cut_fields _ _ _ _ hcutx
  generalize hSx : Sx'.withFlags U.zf U.cf U.nf U.vf = Sx at fl
  have hpc : Sx.pc = {RET} := by rw [← hSx]; exact fx.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hhx : Sx.halted = false := by rw [← hSx]; exact hokx.2.1
  have hl : GenSX.segLen = {XLEN} := by decide +kernel
  have hr : Arm.isa.run rodata prog {XLEN + 1} U = {{ Sx with halted := true }} := by
    rw [show {XLEN + 1} = GenSX.segLen + 1 by rw [hl], Isa.run_add, fl, Arm.run_one rodata prog Sx hhx,
      show prog.getD Sx.pc .nop = .ret by rw [hpc]; exact prog_ret, Arm.exec_ret_eq rodata Sx hhx]
  have hmem : ∀ r q, Sx.mem r q = U.mem r q := by intro r q; rw [← hSx]; exact fr r q rfl
  rw [hr]
  refine ⟨rfl, ?_, ?_, fun q hq => (hmem _ _).trans (hpre q hq), fun n hn => ?_⟩
  · rw [← hSx]; exact hokx.1
  · rw [← hSx]; exact hokx.2.2
  exact digest_congr input U _ _ (fun w _ => hmem _ _) (hdig n hn)
'''


def entry_cut():
    return '''  have hc0 : relocState (rho off) (cutOf GenSE1.ctl0 GenSE1.sc0) = cutOf GenSE1.ctl0 (norm S GenSE1.sc0) := by
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
'''


def main_x2(P):
    XLEN, IT, CBZ, XS = P['XLEN'], P['IT'], P['CBZ'], P['XS']
    steps = f'{XLEN + 6} + {IT} * ((c + 1) / 2)'
    return f'''/-! ## The whole call -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`{P['SYM']}` on any number of nodes.**  For every count `c` and node offset `off` with
`64·(off + c) ≤ 2^54`, from an entry state (any flags), `{steps}` steps halt without a model fault
and without a tail call, keep the output words before node `off`, and leave the keccak256 digest of
input node `off + n` in output words `4(off+n) .. 4(off+n)+3`, for every `n < c`. -/
theorem all (off c : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hE : Entry off c input S) (hb : 64 * (off + c) ≤ 2 ^ 54) :
    (Arm.isa.run rodata prog ({steps}) S).halted = true ∧
    (Arm.isa.run rodata prog ({steps}) S).err = false ∧
    (Arm.isa.run rodata prog ({steps}) S).tail = none ∧
    (∀ q : Int, q < 4 * (off : Int) → (Arm.isa.run rodata prog ({steps}) S).mem rOutput q = S.mem rOutput q) ∧
    ∀ n, n < c → Digest input (Arm.isa.run rodata prog ({steps}) S) (off + n) := by
  have hρ := rho_ok off
  have hb54 : (2 : Nat) ^ 54 = 18014398509481984 := rfl
  have hwf_in : (⟨rInput, 64 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 64 * (off : Int) ∧ 64 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
  have hwf_out : (⟨rOutput, 32 * (off : Int)⟩ : Addr).wf := by
    show 0 ≤ 32 * (off : Int) ∧ 32 * (off : Int) < 2 ^ 55
    rw [show (2 : Int) ^ 55 = 36028797018963968 from rfl]; constructor <;> omega
{entry_cut()}  have hw0 : (rho off).within (2 ^ 54) := rho_within off (by omega)
  have hok0 : SliceCert.Ok (norm S GenSE1.sc0) := hE.ok
  have s1 := GenSE1.seg_run (rho off) hρ hw0 _ hc0 hok0
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
  have hpc1 : T1.pc = {CBZ} := by rw [← hT1]; exact ft1.2.2.2.2.2.2.2.1.trans (by decide +kernel)
  have hh1 : T1.halted = false := by rw [← hT1]; exact hok1.2.1
  -- cbz x2
  have hcbz := Arm.exec_cbz_num rodata T1 2 {XS} c hh1 hx2 (wf_num _ (by omega) (by omega))
  have hrunT2 : Arm.isa.run rodata prog 1 T1 = {{ T1 with pc := if (c : Int) = 0 then {XS} else T1.pc + 1 }} := by
    rw [Arm.run_one rodata prog T1 hh1, show prog.getD T1.pc .nop = .cbz 2 {XS} by rw [hpc1]; decide +kernel, hcbz]
  generalize hT2 : {{ T1 with pc := if (c : Int) = 0 then {XS} else T1.pc + 1 }} = T2 at hrunT2
  have hT2pc : T2.pc = if (c : Int) = 0 then {XS} else {CBZ + 1} := by
    rw [← hT2]; show (if (c : Int) = 0 then {XS} else T1.pc + 1) = _; rw [hpc1]
  have hT2env : ∀ i, envOf T2 i = envOf T1' i := by intro i; rw [← hT2, ← hT1]; rfl
  have hT2mem : T2.mem = T1'.mem := by rw [← hT2, ← hT1]; rfl
  have hT2c : T2.g = T1'.g ∧ T2.k = T1'.k ∧ T2.vl = T1'.vl ∧ T2.depth = T1'.depth := by
    rw [← hT2, ← hT1]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hT2ok : SliceCert.Ok T2 := by rw [← hT2, ← hT1]; exact hok1
  have hT2x2 : T2.getGD 2 = gprWord ⟨0, c⟩ := by rw [← hT2]; exact hx2
  have hl1 : GenSE1.segLen = {CBZ} := by decide +kernel
  have h5 : Arm.isa.run rodata prog {CBZ + 1} S = T2 := by
    rw [show {CBZ + 1} = GenSE1.segLen + 1 by rw [hl1], Isa.run_add, fl1, hrunT2]
  have hpre2 : ∀ q : Int, T2.mem rOutput q = S.mem rOutput q := by
    intro q; rw [hT2mem]; exact f1 rOutput q rfl
  have hin2 : ∀ q : Int, T2.mem rInput q = input q := by
    intro q; rw [hT2mem, f1 rInput q rfl]; exact hE.inp q
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- no node: straight to the epilogue
    subst hc
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
    have he := epilogue off 0 input S off (by omega) T2 hX
    rw [show {XLEN + 6} + {IT} * ((0 + 1) / 2) = {CBZ + 1} + {XLEN + 1} by rfl, Isa.run_add, h5]
    exact he
  · -- the loop and the epilogue
    have hH : Head off c input S 0 T2 := by
      refine ⟨?_, hT2ok, ?_, hin2, fun q _ => hpre2 q, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
      · apply cut_transfer (rho off) (rho (off + 2 * 0)) hρ hρ GenSE1.ctl1 GenSH.ctl0 GenSE1.sc1 GenSH.sc0 T1' (norm T2 GenSH.sc0) hcut1
          (hL_dec _ _ (by decide +kernel)) (fun i _ => hT2env i) (hval_same _ _ _ _ _ (by decide +kernel))
        refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
        · show T2.g = _; rw [hT2c.1, ft1.1]; decide +kernel
        · show T2.k = _; rw [hT2c.2.1, ft1.2.1]; decide +kernel
        · show T2.vl = _; rw [hT2c.2.2.1, ft1.2.2.2.2.2.2.1]; decide +kernel
        · show T2.pc = _; rw [hT2pc, if_neg (by omega)]; decide +kernel
        · show T2.depth = _; rw [hT2c.2.2.2, ft1.2.2.2.2.2.2.2.2]; decide +kernel
      · rw [hT2x2]; simp
    have hl := loop off c input S hb ((c + 1) / 2 - 1) 0 T2 (by omega) hH
    rw [show (c + 1) / 2 - 1 + 1 = (c + 1) / 2 by omega] at hl
    have he := epilogue off c input S (off + 2 * ((c + 1) / 2 - 1)) (by omega) _ hl
    rw [show {XLEN + 6} + {IT} * ((c + 1) / 2) = {CBZ + 1} + {IT} * ((c + 1) / 2) + {XLEN + 1} by omega, Isa.run_add, Isa.run_add, h5]
    exact he
'''


def lib(P):
    XLEN, IT = P['XLEN'], P['IT']
    steps = f'{XLEN + 6} + {IT} * ((c + 1) / 2)'
    return f'''/-! ## In the library -/

/-- The AArch64 calling convention of the library at node offset `off` (within the address bound). -/
def EntryArm (name : String) (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64)) : Prop :=
  Entry off count input {{ S with pc := 0 }} ∧ 64 * (off + count) ≤ 2 ^ 54

/-- `{P['SYM']}` as a kernel of the library (rank 0: it hands nothing over). -/
def kernel : Library.KernelThm Arm.isa EntryArm Digest where
  name := "{P['SYM']}"
  rank := 0
  rodata := rodata
  prog := prog
  entry := 0
  steps := fun _ c => {steps}
  thm := fun off count input S h => by
    obtain ⟨hh, he, ht, hp, hd⟩ := all off count input _ h.1 h.2
    exact ⟨hh, he, hp, Or.inl ⟨ht, hd⟩⟩

theorem ranks_ok : Library.RanksOk [kernel] := by
  intro K hK off count input S hS next done htail _
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
  subst hK
  have ht := (all off count input _ hS.1 hS.2).2.2.1
  have h := ht.symm.trans htail
  cases h

/-- **The library theorem on the table `[{P['SYM']}]`**. -/
theorem lib (off count : Nat) (input : Int → BitVec 64) (S : State (BitVec 64))
    (hS : EntryArm "{P['SYM']}" off count input S) : Library.LibOk [kernel] kernel off count input S :=
  Library.lib_correct [kernel] 0 (by simp [kernel]) ranks_ok digest_local _ kernel (by simp) off count input S
    (Nat.le_refl _) hS
'''


def render(kernel):
    kind, ns, sym, P = KERNELS[kernel]
    P = dict(P, SYM=sym, NS=ns)
    if kind == 'x2':
        P.update(CBZ=4, XS=P['SUBS'] + 2)
        P['XLEN'] = P['RET'] - P['XS']
        P['IT'] = 3 + 1 + 2 + (P['SUBS'] - 11) + 2
        t = open(os.path.join(HERE, 'templates', 'arm_x2.lean.in')).read()
        rep = {
            '@COMMON@': C.entry_struct(),
            '@INV0E@': C.inv0('inv0_e', 'GenSBe', 2), '@INV0O@': C.inv0('inv0_o', 'GenSBo', 1),
            '@DIGE0@': C.digest('dig_e0', 'GenSBe', 2, 0, 25), '@DIGE1@': C.digest('dig_e1', 'GenSBe', 2, 1, 25),
            '@DIGO0@': C.digest('dig_o0', 'GenSBo', 1, 0, 25),
            '@ITERA@': iter_case('a', P), '@ITERB@': iter_case('b', P), '@ITERC@': iter_case('c', P),
            '@EPI@': epilogue(P), '@MAIN@': main_x2(P), '@LIB@': lib(P),
            '@NS@': ns, '@SYM@': sym, '@IT@': str(P['IT']), '@XLEN6@': str(P['XLEN'] + 6),
        }
        for k, v in rep.items():
            t = t.replace(k, v)
        out = os.path.join(HERE, 'Keccaktree', 'Kernels', ns, 'All.lean')
        open(out, 'w').write(t)
        print(out)


if __name__ == '__main__':
    render(sys.argv[1])
