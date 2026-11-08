# Agent `int`: integration of the per-agent branches

Branch `integrate` (worktree `src/wt-int`, from `lean-verification` c50027f), remote workspace `/root/kt-int`
(rsync of the worktree excluding .git/.lake; fresh `.lake` built on the merged core, no hard links into
other workspaces).  Generated `Gen*/` dirs are not committed: copied from the finished workspaces
(`/root/kt-arm`, `/root/kt-rv`), their sha256 recorded in `results/manifest.txt`.

## Merges
| branch | state | merged | conflicts |
|---|---|---|---|
| lean-verification (all-lib, all-rv, all-diff) | base | c50027f | — |
| all-arm (336067c) | finished | yes | `lean/gen_plan_proof.py` only (below) |
| all-x86, all-x86b | running | later (main's go) | expected: `gen_plan_proof.py` (count-spill moves, seg_count, RC kinds at .gd), `Asm/Iter.lean` (already reconciled on all-x86 2d8ec35) |
| all-inplace (075f5f9) | finished | fb7795f | none (clean); its ArmAlias now imports ArmFootprint: the duplicate `Arm.writes` is gone |
| all-rvu | running | after the rvu agent's go | — |

### gen_plan_proof.py reconciliation (all-rv vs all-arm)
Both made the segment mode ISA-generic:
* naming: kept rv's `RELOC_EXPR` / `FOOT_EXPR` (with the RISC-V `VLMAX`-parametric defaults
  `(Riscv.isaReloc V)`, `(Riscv.isaFoot V)`), dropped arm's `ISA_RELOC` / `ISA_FOOT` (no script set them;
  the defaults coincide for X86/Arm).  all-x86/x86b branch from all-rv, so they already use this naming.
* `SEG_IMPORT` (slice files): X86 `Iter`, Arm `ArmFootprint` (arm), Riscv `RiscvFoot` (rv).
* Seg.lean imports (`seg_file_imports`): Arm: `import <SEG_IMPORT>` + the flags-module line (empty
  without FLAG_OBL, as arm emitted it); X86/Riscv: `import Keccaktree.Asm.Iter` (+ flags module only when
  FLAG_OBL is set).  Kept per ISA so that both proved artifact sets regenerate byte-identically.
* moves block: arm rewrote `seg_moves` (per-move `seg_move<m>` theorems along `MOVE_PATHS`); rv/x86 use the
  single `seg_moves` theorem.  arm always runs with `MOVE_CHAIN=1`, rv/x86 never, so
  `seg_moves_text()` = `seg_moves_chain_text()` (arm's) with MOVE_CHAIN, else `seg_moves_kept_text()` (rv's,
  byte-identical).  The per-slice `moves<c>` lemma uses `MOVE_PATHS` (without MOVE_CHAIN the path is
  `[s, d, d, …]`, i.e. the old `(d, s)` / `(d, d)` pairs).
* flags block: arm's `seg_flags_text` (FLAG_OBL, `cpath_flags` / `run_of_cpath`) unchanged.
* `HANDOVER_REGS` per ISA (arm), `START_CTL` (rv), `move_paths` (arm): no overlap.
* For the x86 merge: their moves change (`(loc_out, loc_in)`, `seg_count`) goes into the
  non-chain branch (`seg_moves_kept_text`) / a new flag, leaving the chain branch for ARM.

Evidence (remote, `/root/kt-int-regen.sh`, scratch copy `/root/kt-int-scratch`, kttool of the merged
core): regenerated segments diffed against the proved Gen dirs — see "Regeneration check" below.

## Remote build (`/root/kt-int`)
Scripts: `/root/kt-int-queue.sh <queuefile>` (lines `gen <Ns> <P> <Gen…>` / `mod <Module…>` /
`stopifdisk <GB>`; log `/root/kt-int-logs/queue.log`), `/root/kt-int-mem.sh <unit>` (summed RSS of the
unit's processes every 30 s → `/root/kt-int-logs/mem.log`, stops the unit above 24 GB), units
`kt-int-build`, `kt-int-mem` (`systemd-run -p MemoryMax=infinity -p OOMPolicy=continue -p CPUWeight=200`).
Phase A queue `/root/kt-int-queueA.txt` (unit `kt-int-build`, log `queue.log`): core + programs, ARM kernels
(P=2 for 1-/2-node, P=1 for 3-node), ArmLib, X86X1 All/Lib.  (`error: build failed` after each segment's
Invs/Final step in the log is `build_plan.sh` asking for the non-existent `Final` module of a segment dir.)
Phase B (`/root/kt-int-chain.sh` waits for phase A, then unit `kt-int-buildB`, `/root/kt-int-queue2.sh
/root/kt-int-queueB.txt`, log `queueB.log`): `#print axioms` of ARM + X86X1 (`/root/kt-int/axioms/<Name>.lean`
→ `out_<Name>.txt`), prune the ARM Gen oleans only if that output is complete and clean, then Rv64X1/ZbbX1, and
per VLEN group V ∈ {2,4,8}: RvvV, RvvZvkbV bodies (P=2 for ≤2 nodes, else 1), their All + RvLib<V>, axioms,
prune; `stopifdisk 27` before every RVV body.  `RvLib.lean` (pure re-export of RvLib2/4/8, no theorems) is
not built: the three groups do not fit on disk together.
Core result (06:34): `Keccaktree.Asm.LibTable`, `Keccaktree.Dispatch` and all programs build on the merged
core; `#print axioms` of `LibTable.lib_x86/lib_arm/lib_rv`, `Dispatch.hash_x86/hash_x86_reachable/hash_arm/
hash_rv`: `[propext, Classical.choice, Quot.sound]`.

Disk: ARM proofs ≈ 15 GB of oleans; RISC-V Gen sources are 357 MB for the RVV variants alone (olean/source
≈ 150–290×), so all RISC-V at once may not fit next to ARM above the 25 GB floor: phase B builds per VLEN
group after pruning the ARM oleans (axioms recorded first).

### Regeneration check (2026-11-08 06:30–06:45 UTC): byte-identical
Merged generator + kttool built on the merged core (`/root/kt-int/lean/.lake/build/bin/kttool`), each
kernel's own driver, scratch copy, `diff -r` against the proved Gen dirs:
| kernel | driver | reference | result |
|---|---|---|---|
| scalar_x1 (MOVE_CHAIN, FLAG_OBL, data) | `gen_segments_scalar_x1.sh` | /root/kt-arm | GenSB, GenSE1, GenSX identical |
| sha3_x2 (8 segments, flag and non-flag) | `gen_segments_arm.py sha3_x2` | /root/kt-arm | all 8 identical |
| rv64_x1 (moves `2097155:268`, non-chain) | `gen_segments_rv.sh rv64_x1 Rv64X1 18 5387 5391 5405 2097155` | /root/kt-rv | GenSB, GenSE, GenSX identical |
| rvv_v2 (START_CTL, VLMAX 2) | `gen_segments_rvv.sh rvv_v2 RvvV2 Rvv 2 5777` | /root/kt-rv | GenB1, GenB2 identical |
| rvv_zvkb_v4 (VLMAX 4, up to 4 nodes) | `gen_segments_rvv.sh rvv_zvkb_v4 RvvZvkbV4 RvvZvkb 4 3170` | /root/kt-rv | GenB1–GenB4 identical |

Finding (driver, not generator): `gen_segments_arm.py scalar_x1` does **not** reproduce the proved
`ScalarX1/GenSX` (its plan has rounds `[[0],[0]]`, the proved one was generated by
`gen_segments_scalar_x1.sh` with `[[24],[24]]`; the driver's Batch.lean gains an extra `aat_0` lemma).
GenSB/GenSE1 agree.  notes/arm.md already names `gen_segments_scalar_x1.sh` as the scalar_x1 recipe; the
`scalar_x1` entry of `gen_segments_arm.py` should get round 24 for GenSX (left as is; not a proof issue).

## Open issues / notes for later merges
* **ArmAlias vs ArmFootprint (latent duplicate)**: on `integrate`, `Asm/ArmAlias.lean` (from the in-place
  work in c50027f) and `Asm/ArmFootprint.lean` (all-arm) both define `Keccaktree.Asm.Arm.writes`; a module
  importing both fails (`environment already contains 'Keccaktree.Asm.Arm.writes._sparseCasesOn_3'`, checked
  with `RiscvAlias` + `ArmFootprint`).  No module on `integrate` imports both today (only `RiscvAlias` imports
  `ArmAlias`, and nothing imports `RiscvAlias`).  all-inplace 7dda8a7 resolves it (ArmAlias imports
  ArmFootprint, one `Arm.writes`; its ArmFootprint.lean is blob-identical to all-arm's), so the all-inplace
  merge fixes it.
* **x86 / x86b generator merge (design)**: from `git diff 6774b63 all-x86b -- lean/gen_plan_proof.py`:
  - `seg_count_text`/`COUNT_LOCS` (count followed through its stack spill) replaces `seg_moves` only when
    `COUNT_LOCS` is set (X86 only) → goes next to `seg_moves_kept_text`; the chain variant stays for ARM.
  - Seg.lean: `import Keccaktree.Asm.X86Kernel` and `seg_facts_text()` (`X86K.SegFacts`) are written
    unconditionally there → must be gated to `ISA == 'X86'` in `seg_file_imports` / the Seg footer, or the
    ARM/RISC-V segments stop regenerating byte-identically (and would not compile without X86Kernel).
  - `PRUNE_RC` defaults to on and the RC-kind filter in `matches` is X86-gated; PRUNE_RC is not, so the
    ARM/RISC-V regeneration check must be rerun after that merge (or PRUNE_RC gated to X86).
  - `NODES`, mid-way `aat_n` (X A form), `FLAGS`/`HEAL`/`K1` overrides: env-gated, default-off; fine.

## Build results on the merged core
| item | result | axioms |
|---|---|---|
| core: LibTable, Dispatch, programs | built 06:34 | lib_x86/lib_arm/lib_rv, hash_*: propext, Classical.choice, Quot.sound |
| scalar_x1: GenSX, GenSE1, GenSB (25 slices, P=2, peak 9 GB), All | built 07:01 (27 min) | scalar_x1_all, norm_thm, kernel, lib: standard 3 + 609 bv_decide certificates, no sorryAx; the certificate set is identical to the one of `/root/kt-arm` (diffed; notes/arm.md's "610" is a counting difference) |
| sha3_x2 (07:33), neon_x2 (10:01; P=2 peak 21 GB) | built | in phase B |
| sha3_x3, sha3_x3r, neon_x3, ArmLib, X86X1 | phase A queue running | — |
| in place: 8 kernels + ArmLibInPlace | phase B, before the ARM prune (one module per `mod` line) | — |
| RISC-V | phase B (chained) | — |

Manifest: `results/manifest.txt` (generated by `results/mkmanifest.py . results/gen_sha256.txt <axioms outputs>`;
the axioms outputs are `/root/kt-int/axioms/out_*.txt`).  Entries still marked NOT CHECKED are pending builds.

### all-inplace merge (fb7795f)
Clean merge; it touches only alias/in-place files (`Asm/Alias*`, `ArmAlias`, `ArmAliasTrace`, `RiscvAliasTrace`,
`EntryCtlAl`, `LibAlias*`, `X86AliasIsa`, `Kernels/*/InPlace*`, `ArmLibInPlace`, gen_inplace*.py); none of them
is imported by an every-count module, so the 56 files were rsynced into /root/kt-int while phase A runs.
The in-place modules need the every-count Gen oleans, so phase B builds them (and `#print axioms`,
`axioms/InPlaceArm.lean`, 12 theorems; `InPlaceRv.lean`) before pruning the ARM oleans; the prune is skipped
(queue stops) unless both the ARM and the in-place axioms outputs are complete and clean.
Phase B P changes (budget 20 GB): RISC-V scalar bodies and all 2-node RVV bodies P=1 (neon_x2 at P=2 peaked 21 GB).
