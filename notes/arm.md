# Agent `arm`: all-count theorems of the AArch64 kernels (phase 5)

Branch `all-arm` (worktree `src/wt-arm`, off `lean-verification` f3a7dc5), remote `/root/kt-arm`
(rsync excluding .lake/.git/Gen*/; lake builds under `systemd-run --scope -p MemoryMax=25G`).

## Status
| kernel | all-count theorem | axioms | notes |
|---|---|---|---|
| scalar_x1 | `ScalarX1.All.scalar_x1_all`, `lib_scalar_x1` PROVED | propext, Classical.choice, Quot.sound + 610 bv_decide certs, no sorry | 3 segments (E1, body, epilogue) |
| sha3_x2 / neon_x2 | in progress | | 8 segments (E1, head, 3 csel variants, even/odd batch, epilogue) |
| sha3_x3 / neon_x3 | planned | | tail call to scalar_x1 |
| sha3_x3r | planned | | tail call to sha3_x2, `cmp x2, #4` paths |

## Findings
* **Translator bug (fixed, 3b5de45)**: `asm2lean.py` split the AArch64 operands on commas outside brackets, so the
  post-index form `ldp x29, x30, [sp], #128` lost its `#128`: the epilogue's final `ldp` was modelled without
  writeback, i.e. `sp` was not restored.  Harmless for a kernel that returns (the model halts at `ret`) but
  wrong for the tail-call hand-over (`sha3_x3 → scalar_x1` would start with `sp` 192 bytes too low).  Fixed
  (joins the post-index argument; `ldr`/`str` with a post-index now raise); the six AArch64 `Program.lean`
  regenerated from `results/disasm/obj3` (= PR #17 objects; only the final `ldp` of each kernel changes).
  **The single-batch proofs of the AArch64 kernels must be rebuilt on the new programs** (main queue).
* **Flags at a cut**: a slice certificate fixes the whole control part of its start cut, the flags included.
  The AArch64 loop heads are reached with the entry flags and with the flags of `subs`/`cmp` (different), and a
  kernel entered by a tail call has arbitrary flags.  New generic theory `Asm/Flags.lean`: `Isa.FlagObl`
  (instructions that neither read nor write the flags), `Isa.cpath` (a concrete path), `SliceCert.cpath_at`,
  `SliceCert.step_flags`; `Asm/ArmFlags.lean`: `Arm.flagObl` (all but `subs`, `cmp`, `csel`, `b.cond`).  The
  generator emits `seg_flags` (FLAG_OBL=Arm.flagObl): a flag-free segment runs from any flags.  Consequence:
  the AArch64 `Entry` has **no condition on the flags** (closes the "flags at entry after a tail call" gap for
  AArch64; the same construction works for x86 with an `X86.flagObl` instance).
* **Library**: `KernelThm.thm` demands `done = 0 → count > 0` for a tail call; sha3_x3 / neon_x3 / sha3_x3r
  tail-call on count 0 (`count < 3` → `b scalar_x1` with `x2 = 0`), as do several x86 kernels (avx2_x4 → x86_x1
  at count 0).  The condition is not used by `lib_step` (`hpos` unused) — it should be dropped (agent `lib`).
* Tail names are the symbols (`keccaktree_keccak256_scalar_x1`); the AArch64 kernels use them as `KernelThm.name`.

## Generator lessons
* Body plans take the per-node rounds from `find_plan.py` (three-node kernels interleave a NEON pair and a scalar
  node: their round-r completions differ, 48 cuts); the round-24 cut of a node is delayed until its four digest
  words are present (`settle_digest_cuts`: `find_plan` counts *any* four round-24 lanes, and sha3_x2 applies the
  iota of lane 0 right before the store — the old cut left that lane without a hypothesis and `bv_decide` found a
  counterexample in the last slice).
* `All.lean` of the two-/three-node kernels is rendered on the remote after the segments (slice counts from the
  plans): `/root/kt-arm-pipe.sh <kernel> <Ns> <P> <segs…>` = gen_segments_arm.py + gen_all_arm.py + builds.

## Integration with agent `lib` (merged: lean-verification 8e53c82 → all-arm 7cdeb3a)
`lib` provides `LibTable.EntryA` (same fields as `Arm.Entry`: ctrl/ok/x2/sp/x1/x0/inp, but flags = false and no
`pc`), `LibTable.EntryArm name := EntryA (normCtl S) ∧ bound`, `LibArm.NormThmArm` (kernel theorem from `EntryA`
with `S.pc = entry`, conclusion `Library.Outcome EntryArm Digest targets …`) and `mkKernelArm` (+ its own flag
annotations `Kernels/ArmFlags.lean`).  Our theorems are stronger on the entry side (any flags, `Arm.Entry`), so
`NormThmArm k` follows: `EntryA S ∧ S.pc = 0 → Arm.Entry`; the hand-over `Arm.Entry … {Sf with halted := false,
tail := none, pc := 0}` gives `EntryA (normCtl …)`.  `Digest`: `Nodes.Digest` and `LibX86.Digest` have the same
body — now one definition: `Nodes` uses `LibX86.Digest`/`nodeWords`.  `Library.Outcome` lost its unused
`(done = 0 → count > 0)` clause (7cdeb3a; false for sha3_x3/neon_x3/sha3_x3r at count 0 and for the x86 kernels
that tail-call at count 0; `lib_step` never used it; LibX86/LibArm/LibRv patterns adjusted).
Each AArch64 `All.lean` ends with `norm_thm : LibArm.NormThmArm …` (from `all` via `Arm.entry_of_entryA`, hand-over
via `Arm.entryA_of_entry`) and `kernel := LibArm.mkKernelArm … (Arm.flagAnn ArmFlags.<k>) ArmFlags.<k>_ok …`.

## New/changed files (core changes are additive)
* `Asm/ArmFootprint.lean`: `Arm.writes`, `Arm.exec_frame`, `Arm.isaFoot`.
* `Asm/Flags.lean` (generic), `Asm/ArmFlags.lean`, `Asm/ArmSteps.lean` (`run_one`, `exec_cbz_num`, `exec_subs_num`,
  `exec_sub_num`, `exec_cmp_num`, `exec_bcond_eq`, `exec_ret_eq`, `exec_tailcall_eq`, `getGD_setGD_*`, `envOf_setGD_other`).
* `Asm/Nodes.lean`: `rho`, relocation lemmas, `nodeWords`, `Digest`, `digest_congr`, `digest_local` — the same
  definitions as `Kernels/X86X1/All.lean`, shared so that all kernels' theorems use one `Digest` in the library.
* `gen_plan_proof.py`: segment mode parametrised by ISA (`ISA_RELOC`, `ISA_FOOT`, `SEG_IMPORT`; AArch64 hand-over
  registers x2/x1/x0); `MOVE_CHAIN=1` follows a moved word through the slices (x2 → [sp+112] → x2); `FLAG_OBL`
  emits `seg_flags`.  x86 output unchanged when the new variables are unset.
* `gen_segments_scalar_x1.sh`, `gen_segments_arm.py` (table of segments per kernel), `gen_all_arm.py` +
  `templates/` (renders `All.lean` of the two-node kernels).
* `asm2lean.py`: post-index fix.

## Commands
    rsync -az --exclude .lake --exclude .git --exclude 'Gen*/' ./ root@2.28.133.253:/root/kt-arm/
    cd /root/kt-arm/lean; lake build kttool            # after a Program.lean change
    python3 gen_segments_arm.py sha3_x2 [build P]      # segments; ./gen_segments_scalar_x1.sh build 6
    python3 gen_all_arm.py sha3_x2                     # (local) renders Kernels/Sha3X2/All.lean
    lake build Keccaktree.Kernels.ScalarX1.All
