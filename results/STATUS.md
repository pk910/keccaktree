# Verification status (2026-11-09 19:30 UTC)

What is proved, what the evidence is, what is still pending, and what a reviewer has to read.

## The theorems

For every kernel `K` of the library, `Lib.kernel : Library.KernelThm isa Entry Digest` says: started at
the kernel's symbol, with any input count, any 64-byte-node input buffer (aligned, non-overlapping),
any flags, masks and (RISC-V) `vl` at entry, and on a call or a tail call from another kernel, the machine
code returns, or tail-calls the next kernel with the remaining count. Every digest it has written then
equals `Spec.keccak256` (FIPS 202, Ethereum padding) of its node, and nothing outside the output range
is written. The per-ISA tables (`lib_x86`, `ArmLib.lib_arm_all`, `RvLib.lib*`) quantify over all
kernels, and `Dispatch` proves that `keccaktree.c`'s CPU-feature dispatch only calls kernels the CPU supports.

**In place** (`InPlaceAll.kernelAl`, `lib_inplace_*`): the same statement when the output buffer is the input
buffer (`out = in`, the tree's level-by-level hashing): every node is read before its digest overwrites it.

**Misaligned** (RISC-V, `AllU`/`AllUM`, `RvLibU`, `RvLibUV`): input and output at any byte offset.

## Every-count proofs on the frozen base: 23 of 24 kernels done (in place: 22)

All rows below were checked against the frozen shared base (see "Base freeze"); `results/attestation/frozen/`
has Lean's `#print axioms` output for each one. "certs" = number of bv_decide SAT certificates in the proof.

| ISA | kernel | every count (aligned) | in place | certs |
|---|---|---|---|---|
| x86-64 | x86_x1 | ✅ `X86X1.Lib.lib_x86_x1` | ✅ `lib_inplace_x86_x1` | 721 |
| x86-64 | avx2_x2 | ✅ | ✅ | 786 |
| x86-64 | avx2_x4 (+ every threshold: `LibV`) | ✅ | ✅ (`InPlaceAll`, `InPlaceAllV`) | 2201 |
| x86-64 | avx2_x5 | ✅ | ✅ | 1597 |
| x86-64 | avx2_x6 | ✅ | ✅ | 2294 |
| x86-64 | avx2_x8 | ✅ | ✅ | 1720 |
| x86-64 | avx2_x9 | ✅ (Nov 9) | ✅ (Nov 9) | 8348 |
| x86-64 | **avx2_x10** (+ threshold variant) | ⏳ building, about half of the segments | ⏳ after | |
| x86-64 | avx512vl_x4 | ✅ | ✅ | 3297 |
| x86-64 | avx512vl_x4d | ✅ | ✅ | 3297 |
| x86-64 | avx512_x8 | ✅ | ✅ | 4455 |
| x86-64 | avx512_x8d | ✅ | ✅ | 4455 |
| x86-64 | avx512_x9 | ✅ | ✅ | 6182 |
| x86-64 | avx512_x9d | ✅ (Nov 9) | ✅ (Nov 9) | 6178 |
| AArch64 | scalar_x1, sha3_x2, neon_x2, sha3_x3, sha3_x3r, neon_x3 | ✅ all six, table `ArmLib.lib_arm_all` | ✅ all six, `ArmLibInPlace.lib_inplace_arm_all` | 609 / 1187 / 1185 / 1277 / 1323 / 1185 (table 6631) |
| RISC-V | rv64_x1, zbb_x1 | ✅ + misaligned (`RvLibU.libU`) | ✅ | 741 each |
| RISC-V | rvv, rvv_zvkb at VLEN 128 | ✅ `RvLib.lib2` (+ any `vl` choice `lib2ch`) + misaligned `RvLibUV.lib2U` | ✅ | 1186 (misaligned 2521) |
| RISC-V | rvv, rvv_zvkb at VLEN 256 | ✅ `RvLib.lib4`, `lib4ch`, misaligned `lib4U` | ✅ | 2344 (misaligned 4837) |
| RISC-V | rvv at VLEN 512 | ✅ aligned + misaligned (Nov 9) | ✅ (Nov 9) | 4660 (misaligned 9469) |
| RISC-V | rvv_zvkb at VLEN 512 | ✅ aligned + misaligned (Nov 9) | ⏳ building | 4660 (misaligned 9469) |
| RISC-V | tables at VLEN 512 | ✅ `RvLib.lib8`, `lib8ch` (10585), misaligned `RvLibUV.lib8U` (20017); all-VLEN `RvLib`, `RvLibUV` built | | |

The kernel table counts 24 entries: 14 x86, 6 ARM, 4 RISC-V families (RVV counted once across its VLEN
configurations). RVV with VLEN ≥ 1024 is not covered: the model has 8 lanes per vector register.
That needs a decision: either cap `vlenb <= 64` upstream, or extend the model.

Also proved: **dispatch** (`Dispatch.hash_x86`, `hash_arm`, `hash_rv`, `detect*_sound`,
`hash_x86_reachable`). **Differential tests**: every instruction form of the three ISA models against
hardware or qemu (x86, AArch64, RISC-V at VLEN 128/256/512). **Portable C and Go kernels**:
`Generic.lean` transcribes them; CI checks the transcription statement by statement
(`lean/check_tables.py`) and `Proof.lean` proves both equal `Spec.keccak256`.

## Pending, with estimates

| item | state | estimate |
|---|---|---|
| avx2_x10 every count | GenX4, GenX3 done; GenX2 building; 4 slices in parallel, ~30 min each | Nov 10 morning |
| avx2_x10 threshold variant, library kernels, axioms | runs right after (same segments) | Nov 10 ~12:00 |
| avx2_x10 / x10V in place | after that | Nov 10 ~15:00 |
| rvv_zvkb VLEN 512 in place | 209 modules building | Nov 9 night |
| final single-tree assembly: in-place library tables for x86 and RISC-V, combined axioms check, `results/manifest.txt`, `leanchecker` replay of every module | after both | Nov 10 evening |
| VLEN ≥ 1024, x86/ARM misaligned buffers | not started | needs a decision |

## Attestation

`results/attestation/frozen/` (this run, frozen base):

* `kt-int/<name>.lean`: the check script, `import <modules>` followed by `#print axioms` for every theorem.
* `kt-int/out_<name>.txt.gz`: Lean's output for that script, run in the single integration tree `kt-int`.
  `kt-x86/*.ax.txt.gz`: the same for the every-count theorems in the x86 build tree, where the large AVX2 and
  AVX-512 proofs were built (their oleans are linked into `kt-int`, and `lake build --no-build` there confirms
  they are up to date against `kt-int`'s sources).
* `summary.txt`: one row per theorem (221 rows) with its certificate count, produced by `lean/axsum.py`,
  which fails unless every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` and
  `<decl>._native.bv_decide.ax_*` certificate axioms and no output contains an error or `sorryAx`.
* `base.txt`: git blob ids of the shared trusted files in each build tree. They equal this branch's files,
  except that the x86 trees still have the older `Asm/Riscv.lean`. No x86 kernel module imports it, so this
  does not affect them: their oleans are up to date in `kt-int`, which has the current file.
* `SHA256SUMS`: hashes of the raw outputs before compression.

**Result:** 221 theorems, all clean: no `sorryAx`, no axiom besides the three standard ones and the bv_decide
certificates (checked by Lean's verified LRAT checker run as compiled code).

`results/attestation/interim/` (Nov 8) holds the earlier per-workspace run, with import-closure blob digests;
the frozen run supersedes it. The final step produces `results/manifest.txt` and a `leanchecker` replay.

To re-check anything: `cd lean && lake build <module>`, then `lake env lean <check script>`.

## What a reviewer has to read (trust base)

The proof code is large (about 585k generated lines under `lean/Keccaktree/Kernels`, a 19k-line proof core
under `lean/Keccaktree/Asm`, 24 Python generators), but none of it has to be trusted. Lean's kernel checks
every proof step, so a bug in a generator or a lemma can only make a proof **fail** to check; it cannot make a
false theorem check. What `#print axioms` shows (above) rules out `sorry` and any extra assumption.

What does have to be trusted is the **statement**: that the theorem says what we mean, about the code we ship.
That is about 2,100 lines to read:

| what | file | lines | why it matters |
|---|---|---|---|
| Keccak-256 specification | `lean/Keccaktree/Spec.lean` | 201 | the reference function; `SpecVectors.lean` (35) evaluates it on test vectors |
| what "kernel correct" means | `Asm/Library.lean` (`Outcome`, `KernelThm` lines 25–66, `lib_correct` 168–198) | ~75 | the theorem statement |
| buffer layout and digest per ISA | `Asm/LibX86.lean` (119), `LibArm.lean` (66), `LibRv.lean` (66), `LibAlias.lean` (214, in place) | 465 | alignment and non-overlap hypotheses, digest = `Spec.keccak256` |
| machine model | `Asm/Machine.lean` (202), `Exec.lean` (59) | 261 | registers, memory, fetch-execute |
| instruction semantics | `Asm/X86.lean` (554), `Arm.lean` (258), `Riscv.lean` (305) | 1117 | also differentially tested against hardware and qemu (`lean/difftest`) |
| code import | `lean/asm2lean.py` (891), `Asm/Rodata.lean` (415) | | turns the shipped object files (`objdump -d -r`) into the Lean programs; constant tables |
| dispatch model | `lean/Keccaktree/Dispatch.lean` | 447 | model of `keccaktree.c`'s CPU dispatch |

Plus the Lean 4.35.0 kernel and the bv_decide pipeline (Lean's compiler and the verified LRAT checker it runs).
The `leanchecker` replay in the final step re-checks every module's declarations with an independent run of
the kernel.

## Base freeze

Branches built in parallel had diverged on one proof-library file, `Asm/Iter.lean`. Lean rechecks every
module downstream of a changed file. From commit e43c5ea on, the shared files are frozen at `Iter.lean`
28ac8a7, the RISC-V model of all-rvu, and `Library`/`Lib*`/`LibTable` as on integrate. Every artifact is
built **once** against that base. Generator changes since then are gated so the outputs for proved kernels
stay byte-identical (`notes/int.md` lists each gate: `STEP_DEPTH_ALL` for avx2_x9/x10, the `w > 4` split in
`gen_all_rvvu.py` for VLEN 512).
