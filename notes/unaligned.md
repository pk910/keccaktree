# Unaligned buffers and in-place hashing: what the model covers, what it would take

Queued item 3 (research only; no proofs changed).  Upstream `origin/main` (6ede9ab, `src/` identical to the
verified sources) checked on 2026-11-07.

## 1. What the API promises

* `keccaktree.h` / README: `keccaktree_hash(output, input, count)`; no alignment requirement is stated, and
  **"`output` may alias `input` for in-place layer reduction"** (exact aliasing only: the Java binding copies
  the input when the ranges overlap partially, "the kernels only support exact in-place aliasing").
* The test suites exercise both: `src/test.c` runs every backend on byte offsets 1..7 of input and output
  (count 37) and in place (`f(ip, ip, 300)`); `tests/keccaktree.rs`, the Nim and Java tests and `hash_test.go`
  do the same through the bindings.
* So **unaligned input/output (any byte offset) and exact in-place aliasing are supported uses** and belong
  in the correctness statement.

Evidence collected now (remote, `/root/kt-diff/up`):

| backends | how | count 0..300 + offsets 1..7 + in place |
|---|---|---|
| generic, x86_x1, avx2_* (all tail settings) | native (AVX2 host) | all OK |
| avx512vl_x4(d), avx512_x8(d), avx512_x9(d) + all above | Intel SDE `-spr` (aborts on any misaligned aligned move) | all OK |
| neon_x2/x3, scalar_x1, sha3_x2/x3/x3r | qemu-aarch64 `-cpu max`, `KT_TEST_SHA3=1` | all OK |
| rv64_x1, zbb_x1, rvv, rvv_zvkb | qemu-riscv64 VLEN 128/256/512 (+zbb, zvkb), `KT_TEST_*=1` | all OK |

## 2. Unaligned paths per kernel

| kernels | how they read input / write output | alignment-dependent code |
|---|---|---|
| x86_x1 | scalar `mov`/`xor`/`rorx` with memory operands | none |
| avx2_x2..x10 | `vmovdqu` / VEX memory operands (`vpxor ymm, ymm, [rsi+..]`, `vinserti128`), `rep movsb` for the padded tail copy | `vmovdqa` only on the stack frame (bases r9/r11/r8, set up from the realigned rsp) |
| avx512vl_x4(d), avx512_x8/x9(d) | `vmovdqu64` (also masked `{k1}` loads of the tail nodes), EVEX memory operands | `vmovdqa64` only on the stack frame |
| scalar_x1, neon_x2/x3, sha3_x2/x3/x3r | `ldp`/`ldr` (x, q, d) on input, `stp`/`str` on output | none (Normal memory, no alignment trap in user mode); `sp`-based accesses need 16-byte sp (ABI) |
| rv64_x1, zbb_x1 | `ld`/`sd` | `andi t1, t0, 7; beqz`: misaligned input is copied byte by byte (`lbu`/`sb`, 64 bytes) to a stack bounce buffer; misaligned output: digest words are stored to the stack and copied out by `lbu`/`sb` (32 bytes) |
| rvv, rvv_zvkb | `vlseg8e64.v` / `vsseg4e64.v` | `or a7, a0, a1; andi a7, a7, 7`: if either pointer is misaligned, the avl is capped at 8 nodes and the batch goes through a stack bounce buffer with `vsetvli e8,m8` + `vle8.v`/`vse8.v` (input) and `vsetvli e8,m4` + `vle8.v`/`vse8.v` (output) |

## 3. What the current model and proofs say

* Memory is per region (1 input, 2 output, 3 stack, 4 constants), 8-byte words, `loadWords`/`storeWords`
  require `off % 8 = 0` **relative to the region**; regions never overlap.
* The kernel theorems start from `Entry`: `rsi = ⟨rInput, 64·off⟩`, `rdi = ⟨rOutput, 32·off⟩` (resp. x1/x0,
  a1/a0) — offsets *relative to the region*; nothing says where the region starts on the machine.

### x86 and AArch64: the proofs already cover unaligned buffers — under an interpretation to be made explicit

Read region `r` as "the bytes starting at the user's pointer".  Then every input/output access of these
kernels is at a region-relative multiple of 8, so the model's alignment check passes whatever the
machine alignment is, and the instructions used on regions 1/2 do not depend on the absolute alignment
(VEX/EVEX memory operands, `vmovdqu*`, scalar `mov`, `rep movsb`; AArch64 `ldr`/`ldp`/`str`/`stp` on Normal
memory).  The two absolute-alignment-dependent things are
1. aligned vector moves (`vmovdqa`, `vmovdqa64`): the model checks only 8-byte region-relative alignment
   (found by the differential tests, `notes/diff.md` M5) — they are used only on the stack frame (static
   audit by `alignaudit`: 3.7M executed aligned moves over all x86 kernels and counts 0..64+2N, none outside
   the stack frame; SDE run of test.c with offsets 1..7 never aborts);
2. `and rsp, -64`: the model assumes the stack region base is 64-byte aligned.  On the machine the frame
   lands at a different (consistent) relabelling of the stack cells; since every cell is accessed through
   one view only (the pre-alignment pushes via rsp/rbp, the frame via the realigned rsp), values agree.
To turn this into a theorem: (a) make the aligned forms distinguishable in the model (`vmov`/`vstore` with an
`aligned` flag, failing unless the address is in region 3), and (b) state the machine-level correspondence
with a region base map `B : Region → Addr` that is arbitrary for regions 1/2 and 64-aligned for region 3
after `and rsp, -64` (or: prove the relabelling lemma for the stack).  No kernel proof changes beyond
regenerating the slices that contain aligned moves (the flag adds a side condition that the symbolic run
discharges: the base is a stack pointer).

### RISC-V: the misaligned (bounce) paths are **not** covered

`E.low3`/`E.addrP` compute the low three bits of a pointer from its region-relative offset, i.e. they assume
region bases are 8-byte aligned; with that assumption the proofs take the aligned branch only.  `lbu`, `sb`,
`vle8.v`, `vse8.v` and `vsetvli e8,m4/m8` are `.unsupported` (the model fails on them).  The machine takes
the bounce path whenever the user pointers are misaligned.

### In-place aliasing: **not** covered on any ISA

Input and output are separate regions in every `Entry`.  With `output == input` the digests of batch `k`
overwrite input bytes `[32k, 32k+32N)`, which for `k < N` lie inside the batch being hashed; the kernels are
correct only if every input word of a batch is read before an overlapping digest word is written (true on
the hardware runs above, unproved).

## 4. Design for closing the gaps

1. **Region base misalignment as a parameter.** `State` gets `rb : Region → Fin 8` (machine address of the
   region base mod 8; `rb 3 = 0` for the stack after realignment, `rb 4 = 0`).  `E.low3 (.ptr ⟨r, o⟩) =
   rb r + o`, likewise `addrP`'s alignment mask; `Entry` takes `rb rInput`, `rb rOutput` as parameters.
   Nothing else changes for x86/ARM (no instruction reads `low3` there), so their proofs carry over verbatim
   with `rb` free.
2. **Byte instructions (RISC-V).** Model `lbu d, o(b)` = `(word (o / 8) >>> 8·(o % 8)) &&& 0xff` and
   `sb` = masked update of one word (`E` already has `and/or/shl/shr`); region-relative offsets, so no
   absolute alignment enters.  `vsetvli e8, m4/m8` sets a byte `vl` (`vlb`) and the register-group shape;
   `vle8.v vd, (b)` with `vlb = 64·n` loads `n·8` words into the group `vd..vd+7` (element `i` → register
   `vd + i / (VLEN/8)`, byte `i % (VLEN/8)`; as words: lane `(i % (VLEN/8)) / 8`) — region-relative
   word-aligned in every use (the bounce source/destination offsets are `64·k`/`32·k`), so it is a word copy;
   `vse8.v` symmetrically.  The bounce path then becomes one more per-class segment (classes: input aligned
   or not × output aligned or not; RVV: `a0|a1` aligned or not), proved with the existing pipeline.
3. **Byte-granular stores are needed only for the RISC-V output bounce** (`sb` of 32 bytes): the symbolic
   run produces per-word `or`/`and` trees that `bv_decide` sees through (8 bytes per word, constant shifts).
4. **In-place.** A second `Entry` variant with `rdi = ⟨rInput, 32·off⟩` (same region as the input).  The
   symbolic run of each segment then tracks overwritten input words automatically (memory is a function);
   the generated lane lemmas stay the same iff no input word is read after an overlapping store.  Cheaper
   alternative: a footprint lemma per segment (`Footprint.lean` already has "a step changes only the cells
   it stores to") plus the decidable fact, checked on the recorded traces of each count class, that every
   load of input word `q` precedes every store to output word `q' ≥ …` with `32·off + 8q' = 64·off + 8q`.
   Relocation: an iteration shifts input by `64·N` and output by `32·N` bytes, so the overlap pattern is
   not invariant across iterations; but from iteration 1 on (`k ≥ N`) the written range lies below the read
   range, so only the first iteration (and the per-count entry/tail segments) needs the check.
5. **Estimated proof impact.** (1) is a model-wide change (all `exec_map`/`exec_reloc` lemmas mention
   `low3` only through `asAddr`, so a handful of lemmas), no regeneration for x86/ARM; (2)+(3) new
   instructions in `Riscv.lean`/`RiscvHom.lean`/`RiscvReloc.lean` plus bounce segments for the 4 RISC-V
   kernels × VLEN; (4) one extra entry segment per kernel and count class (or the trace check).
