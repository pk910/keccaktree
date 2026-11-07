# Agent `rv`: every-count theorems for the RISC-V kernels

Branch `all-rv` (worktree `src/wt-rv`, off lean-verification f3a7dc5), remote workspace `/root/kt-rv`
(seeded from `/root/kt-loop` incl. `.lake`; rsync excluding .lake/.git/Gen*/).  Builds run under
`systemd-run --scope -p MemoryMax=20G` (`/root/kt-rv-build.sh <Ns> <P> <Gen...>`); P=3 for the
1-node scalar bodies (≈ 5–7 GB per slice; P=4 hit the 20 GB cap).

## Kernels and shapes
| kernel | entry | structure | per-iteration steps |
|---|---|---|---|
| rv64_x1 | 1 | `bnez a2` / frame+spills (GenSE, positions [1,18)) / body (GenSB [18,5387), 25 slices, LOOP) / back edge `ld t0,80(sp); addi -1; sd; beq; j 20` (concrete) / restores (GenSX [5391,5405)) / `ret` | 5374 (last 5373); total `32 + 5374·c` |
| zbb_x1  | 1 | identical frame, body [18,3456), back edge at 3479..3483, exit 3484, ret 3498 | 3443; total `32 + 3443·c` |
| rvv_v{2,4,8}, rvv_zvkb_v{2,4,8} | 1 | `beqz a2` / sp, `t5 = 1<<63`, `a7 = (a0|a1)&7` (concrete) / head 7: `mv t3,a2; beqz a7 →12; vsetvli t0,t3 (vl = min(r, VLMAX)); bnez a7` (concrete) / body from 14 (`vlseg`, rounds, `vsseg`, pointer advance by `vl<<6`/`vl<<5`) / `sub a2,a2,t0; bnez a2 → 7` (concrete) / `addi sp; ret` | body per vl value w ∈ 1..VLMAX (GenB{w}) |

Count-dependence: scalar kernels only through the spilled count word (`[sp+80]`, stack word 131054,
var 2097155) and the entry test; RVV through `vl = min(count, VLMAX)` (the last batch's body is the
variant `w = count mod VLMAX` when non-zero) and `a2`.

**Alignment precondition** (stated in each `Entry`): the buffers sit at byte offsets `64·off` / `32·off`
of their regions, i.e. 8-byte aligned; the misaligned byte-copy / bounce paths (`lbu/sb`,
`vle8/vse8`) are `unsupported` in the model and not covered.

## Core changes (additive / generalising; listed for the merge)
* `Asm/RiscvFoot.lean` (new): `Riscv.writes`, `Riscv.exec_frame`, `Riscv.isaFoot vlmax`.
* `Asm/RiscvSteps.lean` (new): `run_one`, concrete `ld`/`sd`/`opi`/`br`/`j`/`ret` on numbers,
  `gprWord_dec`, `envOf_setR_other`, `setR_*` field lemmas.
* `Asm/Iter.lean`: `E.fold` folds `ptr + e` for any *closed* `e`, with a *signed* offset (`k.toInt`):
  RISC-V moves `sp` down with `addi sp, sp, -224` (the unsigned `toNat` fold gave an unrepresentable
  pointer), RVV advances pointers by `vl << 6`.  `gprWord_add_const` uses `toInt`;
  `E.eval_reloc_fold` takes `hρ : ρ.ok` (one call site in `SliceCert.step`).  x86 glue facts unchanged
  (positive constants: `toInt = toNat`).
* `gen_plan_proof.py`: segment mode no longer hard-codes x86: `RELOC_EXPR`/`FOOT_EXPR` (defaults per
  `ISA`: `X86.isaReloc`/`X86.isaFoot`, `Arm.isaReloc`/`Arm.isaFoot`, `(Riscv.isaReloc v)`/`(Riscv.isaFoot v)`),
  slice import `SEG_IMPORT`; new `START_CTL` (words forced to be control words at the first cut).
* `gen_segments_rv.sh` (new): segments of the 1-node RISC-V kernels.

## Status
* rv64_x1: segments generated; GenSE/GenSX built; GenSB (25 slices) building; `Kernels/Rv64X1/All.lean` written.
