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

## BASE FREEZE (2026-11-08, coordinator / user instruction)
Final shared base = `integrate` at the commit carrying this note:
* `Asm/Iter.lean` 28ac8a7 and `Asm/Tools.lean` 771e2cc from all-x86 (e263eb1; Tools is imported only by
  `Tools/Main.lean`, i.e. kttool, never by a proof module); merged with rvu's Tools additions (clean);
* the RISC-V model from all-rvu 42f493b (merge 970020d, clean incl. gen_plan_proof.py);
* Library / LibX86 / LibArm / LibRv / LibTable as on integrate.
No shared file (Asm/*.lean, Library, Lib* tables, ISA models, Kernels/*Common*.lean) changes after this.
kt-int is the single final build: every artifact built once against this base.  Consequences:
* the phase-A ARM outputs (built on f9527b5) and all-rv's / kt-rvu's RISC-V outputs (f9527b5) are stale:
  ARM and RISC-V are built once in kt-int; x86 kernels (proved on 28ac8a7) are hard-linked from
  /root/kt-x86, /root/kt-x86b after a `lake build --no-build` check (never rebuilt);
* stopped units kt-int-chain, kt-int-build (12:51 UTC) by name; phase A had reached Sha3X3/GenSB.
* deferred: rv64_x1 in place (RiscvAlias.reads has a `_ => []` fallback and misses rvu's lbu/vle8 reads;
  exec_local/RiscvAliasTrace need the new constructors; its summaries are of the removed GenSB) — inplace2.
* x86b's `X86AnnAl.lean` (all-inplace 16e5e81) imports x86b's `X86Ann`: merge after x86b.

## Source merges after the base freeze (no builds)
| merge | commit | notes |
|---|---|---|
| all-rvu 1819ab5 (final) | 9316c81 | delta since 42f493b: RvLibUV*.lean, generated AllUM, notes only |
| all-x86 6b5fc3f | b03bffa | gen_plan_proof.py conflict resolved (below) |
| all-x86b 5570ba2 | ef7280b | no textual conflict; RC lane proof form gated (RC_BV) |
| all-inplace 16e5e81 | 092d70c | new `Asm/X86AnnAl.lean` (imports x86b's X86Ann) |
Frozen-file check after each merge (Iter, Tools, Riscv*, RvVl, Library, LibX86/Arm/Rv/Table): blobs equal to
e43c5ea.  Since e43c5ea only new files were added under Asm/ (X86Frame, X86Kernel, X86Thresh, X86Ann, X86AnnAl).
Tools.lean on integrate is c2ffef0 = x86's 771e2cc + rvu's hunks (clean merge; kttool only).

gen_plan_proof.py after the x86/x86b merges (every addition gated so each branch's committed output stays):
* `matches(..., regs_only)` (rvu) with x86's `DROP_RC` gate (6b5fc3f: default AVX2 + x86_x1, DROP_RC=0/1);
* `moves<c>`: arm's MOVE_PATHS pairs, then x86's count-location override (COUNT_LOCS, X86 only);
* Seg.lean: `seg_file_imports()` (+ `X86Kernel` for X86); footer moves | seg_count (X86) | seg_flags (FLAG_OBL) |
  seg_facts (X86);
* invariants: rvu's INV0/INVK modes when the variable is set, otherwise x86's (NODES, mid-way start/end; equal to
  'input'/'out' for plans from round 0 to 24); NO_RC_MID; x86b's PRUNE_RC (X86 only);
* x86b's RC lane proof (`simp only [E.eval, hyps]; first | decide +kernel | bv_decide`) only with RC_BV
  (default: X86 without DROP_RC = the AVX-512 kernels); otherwise the plain `decide` form (ARM has no RC
  lanes; rvu's RvvV4/V8 and x86's Avx2X9/X10 slices use the plain form).
To be checked by regeneration once kttool is built on the base: ARM, RISC-V (rvu drivers), x86 and x86b samples.

## x86 replay into kt-int (hard links, never rebuilt)
* kt-x86 is NOT used (built on Iter 2a55570); its AVX2 / x86_x1 kernels are rebuilt there on the frozen base and
  linked after each passes.
* kt-x86b → kt-int, avx512_x8 / avx512_x8d (2026-11-08 12:58): the import closure of `Avx512X8.Lib` and
  `Avx512X8d.Lib` in kt-int's sources is 562 modules (`/root/kt-int-closure.py`); every one has a byte-identical
  source in kt-x86b and an .olean there.  Their `lib/lean` and `ir` outputs were hard-linked (`/root/kt-int-link.sh`,
  2930 files; Gen sources copied).  No lake ever runs in kt-x86b.
* `lake build --no-build` over the 562 first reported 42 targets out of date (each kernel's Program and Gen*.Invs).
  Cause: x86b's disk cleanup deleted `.lake/build/ir/Keccaktree/Kernels/Avx512X8{,d}`; the traces record a `.c`
  output for every module (532 of the 562).  The trace inputs are identical (checked on Program: source
  6a345ef1780640ba, imports b4a4dcf653bccf4c / bce00ffc3e650413, Lean 4.35.0 407ce514b71d5a10, options).
* Fix (coordinator-approved): for those 532 modules a fresh, empty placeholder `ir/<module>.c` and `ir/<module>.c.hash`
  holding the hash recorded in the trace, in kt-int only (no links).  The .c files are the compiled-code outputs of
  the C backend; no proof and no importing module reads them (importers read the .olean).  For every one of the 532,
  the `.olean.hash` equals the olean hash recorded in the trace (checked); olean and trace inputs are unchanged.
  List with the recorded c / olean hashes: `results/x86b_replay_placeholder_c.txt`.
* Re-run: `lake build --no-build` over the 562 → `All targets up-to-date (563 jobs)`.  Later real builds in kt-int
  never touched a linked file (link count / mtime checked).
* kttool of the frozen base is built in a separate workspace `/root/kt-int-tool` (it imports every Program, so
  building it in kt-int would have touched linked modules); generation runs there and the Gen dirs are copied.

## lean4checker
The Lean 4.35.0 toolchain ships it as `leanchecker` (also `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`):
`lake env leanchecker <Module>` replays every declaration of the modules whose name has that prefix into the
environment of their imports, through the kernel, without elaboration (tested: Asm.Iter 0.8 s, a GenSE1 slice
1.3 s, ~0.7 GB).  Caution: without a module argument (or with an unknown flag such as `--help`) it checks the whole
project in parallel (a stray `--help` reached 41 GB before I stopped it).  Final run: per module, P ≤ 2, timing per kernel.

## Compiled-C truncations in kt-int (disk)
* 21:14 (coordinator): 799 `.c` files > 1 MB, older than 60 min, with `.c.hash`, truncated to 0 bytes (mtime and
  `.c.hash` kept; 55 GB): `/root/kt-int-logs/truncated_c.txt` (original sizes).  420 of them were hard links into
  /root/kt-x86b (`truncated_c_hardlinked.txt`), so kt-x86b's copies are empty too.  Proofs unaffected (.olean and
  traces untouched, lake trusts the .hash files; --no-build stays up to date).  Rule: no executable is rebuilt in
  kt-x86b / kt-x86; the final regeneration checks use /root/kt-int-tool.
* From then on `kt-int-diskguard` (below 30 GB free, every 10 min): same truncation with `-links 1` (never a
  hard-linked file), log `truncated_c2.txt`.  To be listed in the manifest with the placeholder lists.

## Offloaded olean trees (coordinator, 2026-11-09 09:12)
`/root/kt-int/lean/.lake/build/lib/lean/Keccaktree/Kernels/{RvvV4,RvvZvkbV4,ScalarX1,Sha3X2,NeonX2,Sha3X3,Sha3X3r,NeonX3}` are
symlinks to `/mnt/kt-store/kt-int-lib/Kernels/<d>` (sshfs archive disk of another VM; storage only).  Copied with
links=1 only, verified with `rsync -c`, then `lake build --no-build` of RvLib4, RvLibUV4, ArmLib, ArmLibInPlace
up to date; no olean bytes changed.  Nothing writes into them; if the mount drops: `mount /mnt/kt-store`.

## Regeneration notes (for the manifest)
* avx2_x9 / avx2_x10: `GenX3/Slice0.lean` carries `set_option maxRecDepth 100000 in` on its step theorem (252-element
  output tuple), added in kt-x86 by the coordinator; the generator does the same under STEP_DEPTH_ALL (1d8f2bb, default
  only for avx2_x9/x10, condition outs + chyps > 240; a scan of all x86 slices triggers exactly these two files).  The
  kt-x86 Gen files are taken as they are when linked.
* avx512_x9 / x9d: linked from kt-x86b, Gen dirs not regenerated (mixed generator versions overnight).
* x86_x1 InPlace summaries: committed one-decide form kept; the current gen_inplace.py writes a per-slice form with
  identical statements (proof form only).
* avx2_x4 InPlaceAll: regenerated (0c27870; the committed one predated the threshold-only exit filter).
