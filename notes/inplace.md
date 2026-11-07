# In-place hashing (`out == in`) and unaligned buffers — agent `diff`, phase 6

Branch `all-diff` (after merging lean-verification 0fbdb01), remote `/root/kt-diff/repo/lean`.

## (a) In-place hashing

### Model of the aliased machine (no core change)
`Asm/Alias.lean` (x86):
* `joinMem`, **`execAl`**, `runAl`: one storage (region 1). A step runs `exec` on the *joined view*: loads
  through the output pointer, a region-2 pointer, read the storage at the same offset. Stores through the
  output pointer are copied into the storage (`writes` of the step). The output pointer stays a region-2
  pointer, so `exec` and all existing lemmas are reused unchanged. Hom, Reloc, EntryCtl and every kernel
  proof are untouched.
  - Region-1 vs region-2 pointer comparisons fault in the model (region mismatch).
  - The in-place theorems state `err = false`, so no such comparison occurs.

### Generic results (proved; axioms propext, Classical.choice, Quot.sound)
* `reads s i`: the cells an instruction loads; the counterpart of `Footprint.writes`.
* **`exec_local`** (all 62 x86 constructors): a non-failing step depends on memory only through the cells
  it reads. On a state with memory `m'` agreeing on those cells, it computes the same registers, flags and
  stored words; the other cells keep `m'`.
* `Sim s t` relates the separate-region state `s` to the aliased state `t`:
  - registers and control are equal;
  - storage `t.mem 1` equals `s.mem 2`;
  - the other regions are equal.
* `Clean B s`: above `B` the output region still holds the input.
* `AccessOk B s i`:
  - input loads only at or above `B`;
  - no input stores.

  `bumpB` raises `B` past every output word stored.
* **`sim_step`** and **`sim_run`**: under `AccessRun` (the condition at every step of the separate run),
  the aliased run follows the separate one. At the end:
  - the output region is still clean above the final bound `Bf`;
  - the input region is unchanged.
* `dupState T`: the separate run starts with its output region equal to the storage (`Entry` puts no
  constraint on the output region). `sim_dup`, `clean_dup`, `accessRun_mono` (a smaller start bound
  keeps the condition).
* `accessCheck` (Boolean `AccessRun` on concrete states) with **`accessCheck_sound`**.
* `Asm/LibAlias.lean` **`inplace_lift`**: from `LibX86.NormThm` (any kernel's all-count theorem) and
  `AccessRun … (dupState T)`, the aliased run from `T` (`Entry` of `dupState T`) satisfies `OutcomeAl`:
  - halted, no model fault;
  - storage words below `4·off` kept, storage above `Bf` kept;
  - either every digest is in the storage (`DigestAl`), or a tail call happens and the next kernel's
    `EntryX86` holds in place. That entry reads its message from the storage
    (`input' = Tf.mem rInput`), which equals the message above `Bf`.

### What a kernel must provide: `AccessRun rodata prog (steps off count) B0 Bf (dupState T)`
* **Evidence (concrete, every kernel):** `Tools/InplaceAudit.lean` (`inplaceaudit`) runs every x86 kernel
  model on counts 0 .. 64+2N in place, with `out == in` at offset 0. It checks `accessCheck` along the
  separate-region run and runs the aliased machine `runAl` directly, checking that every digest the
  kernel writes lands in the storage. Result: see "Audit" below.
* **Proof for every count (recipe; not yet done for x86_x1):** `AccessRun` decomposes along the
  segments like the digest proof. Per segment, the concrete reads and writes are the relocated reads
  and writes of the base symbolic trace:
  - input cells shift by `8m` words and output cells by `4m` (`m` = node offset of the iteration);
  - the needed transfer lemma is `reads/writes (eval (reloc Σ)) i ⊆ shift (reads/writes Σ i)` when the
    symbolic step does not fail. It goes per instruction through `memAddr?_map_some`/`memAddr?_reloc`,
    with the slice certificate's `dec` (decoded addresses below the bound) giving `relocOk`.

  The per-segment condition is then decidable on the base trace:
  - every input read `(1, q)` satisfies `q + 8m ≥ B_entry(m)`; for the body, `B_entry = 4m`, so
    `q ≥ -4m` and `q ≥ 0` suffices;
  - for every input read `(1, q)` after an output write `(2, q')` in the same segment,
    `4m ≥ q' - q + 1`;
  - the segment writes no input cells.

  Only finitely many `m` can fail the second condition (the first iterations). For x86_x1 there is no
  read after a write in the body (the digest is stored after the last load), so the condition holds
  for every `m`.
* **Library level:** `Library.lib_correct` composes `KernelThm`s over `Isa.run`. The in-place library
  theorem needs the same induction over `OutcomeAl` with `runAl`, plus the input function changing at
  each hand-over (`input' = storage`, equal to the message above `Bf ≤ 8·(off+done)`). This is a copy of
  `Library.lean` with these two changes; not done.

### Status
* Done: aliased semantics, the full generic simulation, the kernel-level lifting theorem, the checker
  with its soundness proof, and the concrete audit for all x86 kernels.
* Open:
  - the transfer lemma and the per-kernel all-count `AccessRun` (x86_x1 pilot);
  - the in-place library composition;
  - ARM/RISC-V versions (`reads` + `exec_local` per ISA, ~250 lines each following the x86 file:
    `reads` definition, `_loc` combinators, generated case list).

### Audit
`inplaceaudit <Kernel>` on `/root/kt-diff` (memory compacted every 256 steps):

| | |
|---|---|
| kernels | all 14 x86 kernels |
| counts | 0 .. 64+2N each, 1,104 runs |
| `accessCheck` | true |
| aliased machine | halts, no model fault |
| digests | every digest the kernel writes is in the storage |
| failures | 0 |

Per kernel: Avx2X10 85/85, Avx2X2 69/69, Avx2X4 73/73, Avx2X5 75/75, Avx2X6 77/77, Avx2X8 81/81,
Avx2X9 83/83, Avx512vlX4(d) 73/73, Avx512X8(d) 81/81, Avx512X9(d) 83/83, X86X1 67/67.

## (b) Unaligned buffers
* x86/ARM: the argument in `notes/unaligned.md` ("region base = user pointer") stands, with evidence:
  - `alignaudit`: 0 of 3.7M aligned moves outside the stack frame;
  - SDE run of upstream test.c with offsets 1..7 never aborts.

  Making it formal needs an `aligned` flag on `vmov`/`vstore` restricted to the stack region. That
  changes `X86.Instr`, so every Hom, Reloc, EntryCtl and Footprint lemma and every x86 `Program.lean`
  and kernel proof must be regenerated and rebuilt — not cheap, so not done.
* RISC-V bounce paths: **handed to agent `rv`** (coordinator, scope update). Nothing was started
  here beyond the design in `notes/unaligned.md` §4: per-region misalignment `rb`, `lbu`/`sb`, `vle8`/
  `vse8` as region-relative word copies, `vsetvli e8,m4/m8`, and bounce segments per class. The M9 model
  fix also goes to `rv`.
