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

### All-count proof of the access condition (DONE for x86_x1)
* `Asm/AliasTrace.lean`:
  - `decOk_of_exec`: a step that does not fail decodes every address its footprints use.
  - **`cells_map`** / **`cells_reloc`**: a concrete step's read and write cells are those of the
    symbolic step, shifted by the relocation (`shiftCell`).
  - **`path_access`**: along a relocated symbolic path, the access condition follows from the base
    cells (`traceCells`, `accessCells`).
  - **`SliceCert.access`**: the hook for one certified slice.
  - Summaries `summ` (lowest input word read, highest output word written, smallest read-after-write
    distance, input writes) and `summ_access`: the condition at relocation `ρ` reduces to linear
    inequalities in `ρ.wshift`.
  - **`chain_access`**: a whole generated segment (`ChainOk` list of certificates), from the per-slice
    summaries (`SummOk`).
* `Alias.lean`: `accessRun_add` (sequencing), `accessRun_step` (a concrete step with no input or output
  cells).
* **`Kernels/X86X1/InPlaceAll.lean`**:
  - `body_access`: the body hashes node `m`, reading input words ≥ 0 relative (absolute ≥ `8m`) and
    writing output words ≤ 3 relative (absolute < `4m+4`).
  - `loop_access`, `exit_access`, `access_all`: the bound runs from `4·off` to `4·(off+c)`.
  - **`x86_x1_inplace`**: every count, on the aliased machine.
  - **`kernelAl`**, **`lib_inplace_x86_x1`**: the in-place library on `[x86_x1]`, through
    `Library.lib_correct` with `X86.isaAl`.
  - Axioms: propext, Classical.choice, Quot.sound + 721 bv_decide certificates; no sorry.
* Where it was checked: `/root/kt-diff/ws`, a copy of `/root/kt-x86/lean`, whose core differs from
  `lean-verification` 8d8f560 only in `Iter.lean`/`Tools.lean` (`E.fold` generalised by agent rv).
  The x86_x1 `Gen*` dirs were rebuilt there. On the current core the same files build once the kernel's
  `Gen*` dirs are rebuilt (they only use the `SliceCert` API).
* Library design change: the aliased machine now shows the one buffer in both regions (`mirror`). The
  digests are then `LibX86.Digest` (output view), so `Library.lean` applies unchanged to
  `X86.isaAl` (`execAl_map`, `err_execAl`). The calling convention is `EntryAl`:
  - one buffer (`Mirror`);
  - `LibX86.Entry` of `dupState T` with the buffer as message;
  - agreement with `input` from word `8·off` on.

  At a hand-over the message switches to the buffer contents, which agree with `input` above the
  final bound.
* Not covered yet: entry with *dirty* control (flags/masks left by a tail call) on the aliased machine.
  `EntryAl` takes the control of a fresh call; `kernelAl` needs no hand-over (x86_x1 tail-calls
  nothing). For kernels that tail-call:
  - an `execAl` version of `EntryCtl.exec_ovr` (`writes` ignores control fields, so it follows from
    `exec_ovr`);
  - the run lemmas `run_ovr_prefix`/`run_ovr_static` for `X86.isaAl`.

## (3) Recipe for the kernel agents (x86 now; ARM/RISC-V after the transfer lemmas below)
1. `python3 gen_inplace.py <Kernel> <Seg>... --eval` (from `lean/`, in a workspace where the kernel's
   `Gen*/Seg.lean` are built) writes `Keccaktree/Kernels/<Kernel>/InPlace/<Seg>.lean`:
   - `certs`, `chain`, `len`;
   - `sums`, computed by `#eval` and checked by `decide +kernel`; a few seconds per slice.

   Your generated proof files are only read, never modified.
2. In the kernel's in-place file (template: `Kernels/X86X1/InPlaceAll.lean`), per segment at relocation
   `rho m`:

       chain_access (rho m) hρ hw InPlace.<Seg>.certs S b bf InPlace.<Seg>.chain <cut> <Ok>
         (by rw [InPlace.<Seg>.sums, rho_wshift_in, rho_wshift_out]; simp [SummOk, nextB] <;> omega)

   with `b` = the current bound (`4·(first node of the batch)` for a batch at node `m`) and `bf` = the
   bound after the segment. One-slice segments without input/output cells use `seg1_access`. Concrete
   steps between segments use `accessRun_step`; composition uses `accessRun_add`. The structure mirrors
   the kernel's every-count proof (same `Head`/`iter`/`loop` states).
3. Batches of `N` nodes whose last digest stores come after some input loads of the same batch
   (`gap` ≠ `none` in a summary): `SummOk` then needs `4m + 1 ≤ gap + 8m`, i.e. `m ≥ (1 - gap)/4`.
   Earlier iterations (first batches) must be shown with the actual small `m`. With `m` free in the
   segment lemma, `omega` handles it when the inequality holds for all `m ≥ 0`.
4. `x86_x1_inplace` → `inplace_lift` (`LibAlias.lean`) needs only the kernel's `NormThm` and the
   access proof. A kernel instance for the in-place library follows `kernelAl` (and needs the
   dirty-control lemma above if the kernel tail-calls).

## (4) AArch64 and RISC-V
* `Asm/AliasGen.lean`: the aliased machine, the access condition and **the simulation (`sim_step`,
  `sim_run`) for any `FootIsa`**. A `FootIsa` is an instruction set with read/write footprints, write
  cells independent of memory, and memory locality.
* `Asm/ArmAlias.lean`: AArch64 `reads`/`writes`, **`Arm.exec_local`** (all 36 constructors),
  `Arm.footIsa`.
* `Asm/RiscvAlias.lean`: RISC-V `reads` (with `RiscvFoot.writes`), **`Riscv.exec_local`** (all 24
  constructors), `Riscv.footIsa vlmax`.
* Still open for ARM/RISC-V:
  - the symbolic transfer (`cells_map`/`cells_reloc` + `path_access`, as in `AliasTrace.lean`, using
    `ArmReloc`/`RiscvReloc`);
  - an `Isa` instance of their aliased machines (as `X86.isaAl`);
  - a lifting theorem from `LibArm`/`LibRv` `NormThm*` (as `inplace_lift`).

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
