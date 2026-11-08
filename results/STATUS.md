# Verification status (2026-11-08)

What is proved, what the evidence is, and what is still pending. The final step re-checks
every kernel in **one** tree against a frozen shared base (see "Base freeze"). Until that has run,
the results below were checked in per-ISA workspaces. Each one is a complete Lean check of that
theorem, but against the shared proof-library files of its own workspace.

## The theorems

For every kernel `K` of the library, `Lib.kernel : Library.KernelThm isa Entry Digest` says: started at
the kernel's symbol, with any input count, any 64-byte-node input buffer (aligned, non-overlapping),
any flags, masks and (RISC-V) `vl` at entry, and on a call or a tail call from another kernel, the machine
code returns, or tail-calls the next kernel with the remaining count. Every digest it has written then
equals `Spec.keccak256` (FIPS 202, Ethereum padding) of its node, and nothing outside the output range
is written. The per-ISA tables (`lib_x86`, `ArmLib.lib_arm_all`, `RvLib.lib*`) quantify over all
kernels, and `Dispatch` proves that `keccaktree.c`'s CPU-feature dispatch only calls kernels the CPU supports.

## Every-count proofs: 20 of 24 kernels

| ISA | kernel | every count | bv_decide certs | checked where (Iter blob) | final single-tree build |
|---|---|---|---|---|---|
| x86-64 | x86_x1 | proved (`X86X1.Lib.lib_x86_x1`) | 721 | kt-lib (35daf84) | rebuild queued (kx-final) |
| x86-64 | avx2_x2 | proved | 786 | kt-x86 (2a55570) | rebuild queued (kx-final) |
| x86-64 | avx2_x4 (every threshold, `LibV`) | proved | 2201 | kt-x86 (2a55570) | rebuild queued |
| x86-64 | avx2_x5 | proved | 1597 | kt-x86 (2a55570) | rebuild queued |
| x86-64 | avx2_x6 | proved | 2294 | kt-x86 (2a55570) | rebuild queued |
| x86-64 | avx2_x8 | proved | 1720 | kt-x86 (2a55570) | rebuild queued |
| x86-64 | avx2_x9 | **building** | | kt-x86 (frozen) | built once there |
| x86-64 | avx2_x10 | **building** | | kt-x86 (frozen) | built once there |
| x86-64 | avx512vl_x4 | proved (Nov 7) | 3297 | kt-x86b (28ac8a7 = frozen) | segment oleans deleted, rebuild in kt-int |
| x86-64 | avx512vl_x4d | proved (Nov 8) | 3297 | kt-x86b (frozen) | rebuild in kt-int |
| x86-64 | avx512_x8 | proved | 4455 | kt-x86b (frozen) | **final**: replayed by hard link |
| x86-64 | avx512_x8d | proved | 4455 | kt-x86b (frozen) | **final**: replayed by hard link |
| x86-64 | avx512_x9 | **building** (body, prologue, exits 1–3 built) | | kt-x86b (frozen) | built once there |
| x86-64 | avx512_x9d | pending (after x9) | | kt-x86b (frozen) | built once there |
| AArch64 | scalar_x1, sha3_x2, neon_x2, sha3_x3, sha3_x3r, neon_x3 | proved (`ArmLib.lib_arm_all`) | 6631 | kt-arm (35daf84) | rebuild in kt-int |
| RISC-V | rv64_x1, zbb_x1, rvv, rvv_zvkb, VLEN 128 / 256 | proved (`RvLib.lib2`, `lib4`, any vl choice: `lib2ch`, `lib4ch`) | 3637 / 5953 | kt-rvu (f9527b5) | rebuild in kt-int |
| RISC-V | rvv, rvv_zvkb, VLEN 512 | proved on the previous RISC-V model; pending on the current one | | | build in kt-int |

The kernel table counts 24 entries: 14 x86, 6 ARM, 4 RISC-V, with RVV counted once over its VLEN
configurations. RVV with VLEN ≥ 1024 is not covered: the model has 8 lanes per vector register.
That needs a decision: either cap `vlenb <= 64` upstream, or extend the model.

## Beyond the aligned every-count theorem

| property | proved | pending |
|---|---|---|
| **in place** (output = input) | x86_x1 (`lib_inplace_x86_x1`, generic `LibAlias.lib_inplace_x86`); scalar_x1, sha3_x2, neon_x2, sha3_x3 (`lib_inplace_*`, generic `LibArmAl.lib_inplace_arm`); rv64_x1 on the previous RISC-V model | sha3_x3r, neon_x3, ARM table; AVX-512 (generator done, avx512_x8 pilot building); AVX2 (generated, waiting for the rebuild); RISC-V on the new byte/vector-load model |
| **misaligned buffers** (RISC-V) | rv64_x1, zbb_x1 for any input/output byte offset (`RvLibU.libU`, `libU_ch`); rvv, rvv_zvkb VLEN 128 (`RvLibUV.lib2U`, default `vl` rule) | VLEN 256/512 (generated); x86/ARM unaligned not started |
| **dispatch** (`keccaktree.c`) | `Dispatch.hash_x86`, `hash_arm`, `hash_rv`, `detect*_sound`, `hash_x86_reachable` | |
| **differential tests** | every instruction form of the three ISA models against hardware or qemu (x86, AArch64, RISC-V at VLEN 128/256/512) | |

## Attestation

`results/attestation/interim/` holds the evidence for every row marked proved:

* `<ws>.<module>.lean`: the check script, `import <module>` followed by `#print axioms` for every theorem in it.
* `<ws>.<module>.ax.txt.gz`: Lean's output: the header line with workspace, module, UTC time and `lean --version`
  (4.35.0, commit eb6cafb7), then one `depends on axioms` line per theorem.
* `<ws>.closure.json`: the import closure of each checked module, with the git blob id of **every** source file
  in it and a sha256 digest over the sorted `(module, blob)` list. Any file can be compared with the repository
  by `git hash-object`.
* `summary.txt`: the per-theorem axioms digest of the above. `closures.md`: one row per root module.
* `SHA256SUMS`: hashes of the raw outputs before compression.

**Result of every check:** only `propext`, `Classical.choice`, `Quot.sound`, plus `bv_decide` certificate
axioms (`<decl>._native.bv_decide.ax_*`, checked by Lean's verified LRAT checker run as compiled code).
No `sorryAx`, no other axiom. The certificate count is the number of SAT problems in a kernel's proof.

Interim caveat: the x86 AVX2 rows (and x86_x1) were checked against `Iter.lean` blob 2a55570. Their workspace
file was swapped to the frozen 28ac8a7 minutes before this run; `x86.closure.json` records the blob the oleans
were built with. These rows are superseded by the frozen-base rebuild.

To re-check anything: `cd lean && lake build <module>`, then run the check script with `lake env lean`.

## Base freeze

Branches built in parallel had diverged on one proof-library file, `Asm/Iter.lean` (four versions of the
expression folder `E.fold`). Lean rechecks every module downstream of a changed file. From commit e43c5ea on,
the shared files are frozen at `Iter.lean` 28ac8a7 (the superset: the signed/closed fold RISC-V needs, plus the
x86 region-0 case), the RISC-V model of all-rvu, and `Library`/`Lib*`/`LibTable` as on integrate.
Every remaining artifact is built **once** against that base:

* kt-x86: avx2_x9, avx2_x10, then avx2_x2, x4 (+V), x5, x6, x8, x86_x1
* kt-x86b: avx512_x9, x9d; avx512_x8/x8d already on the base
* kt-int (one tree): ARM, RISC-V (aligned + misaligned), all in-place modules, avx512vl_x4/x4d,
  the x86 kernels by hard link, then `results/manifest.txt` with one combined axioms check

## Pending, with estimates

| item | estimate |
|---|---|
| avx2_x9, avx512_x9 | Nov 8 night |
| avx2_x10, avx512_x9d | Nov 9 morning |
| AVX2/x86_x1 rebuild on the frozen base | Nov 9 |
| kt-int: ARM, RISC-V, in-place, combined manifest | Nov 9 evening |
| VLEN ≥ 1024, x86/ARM unaligned | needs a decision |
