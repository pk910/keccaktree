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
* **Entry with dirty control (DONE, agent `inplace2`)**: `Asm/EntryCtlAl.lean`:
  - `writes_ovr` (the stored cells do not depend on flags/masks/vl), `execAl_ovr_of`, **`execAl_ovr`**
    (`exec_ovr` on the aliased machine);
  - **`run_ovr_static_al`**, `prefix_step_al`, **`run_ovr_prefix_al`**, **`run_normCtl_al`**: the run
    lemmas of `EntryCtl.lean` for `X86.isaAl`; `normCtl_ovr`, `dupState_ovr`, `dupState_normCtl`.
  - `Asm/LibAlias.lean`: **`EntryAlX86`** (in-place calling convention with *any* flags/masks/vl:
    `Mirror T ∧ Entry off count (T.mem rInput) (normCtl (dupState T)) ∧ message from word 8·off ∧ bound`),
    **`AccessThm`** (what a kernel's in-place proof provides, see below), `digest_input`,
    **`inplace_outcome`** (NormThm + AccessThm ⇒ `Library.Outcome EntryAlX86` of the aliased run, hand-over
    in place), `outcome_ovr_al`, **`mkKernelAl`** (as `LibX86.mkKernel`: same `prefixOk`/static checks),
    **`lib_inplace_x86`** (any table of the x86 shape over `X86.isaAl`, per threshold configuration).
  - `Kernels/X86X1/InPlaceAll.lean`: `access_thm`, `kernelAl := mkKernelAl … Lib.norm_thm access_thm`,
    **`lib_inplace_x86_x1`** now from `EntryAlX86` (any control state). Axioms: propext, Classical.choice,
    Quot.sound + bv_decide certificates; no sorry.
  - `AccessThm rodata prog entry steps`: for every normalised entry (`LibX86.Entry`, bound, `pc = entry`)
    `∃ Bf, AccessRun rodata prog (steps off count) (4·off) Bf S` and, if the run ends in a tail call whose
    hand-over is `Entry (off+done) …`, `Bf ≤ 8·(off+done)` (the next kernel's message words are still in
    the buffer; a kernel whose batches stored digests up to node `off+done` has `Bf = 4·(off+done)`).
    For kernels that never tail-call the second part follows from `NormThm` (`tail = none`), see
    `X86X1.InPlaceAll.access_thm`.
  - AVX-512 kernels (masked moves) cannot use the static check: like `mkKernelAnn` (agent x86b) they need
    an annotated version on the aliased machine — `execAl_ovr` is the per-step lemma; the run lemma is
    the same induction as `run_ovr_ann_gen` (`AliasIsa.lean`) instantiated with x86's `ctlOk/ctlAfter`
    and the call/return successor relation used by `mkKernelAnn`.

## (3) Generic layer (agent `inplace2`): any instruction set, any kernel

### Files
| file | content |
|---|---|
| `Asm/AliasBase.lean` | split of `Alias.lean` without the x86 step: `rebase`, `Agree`, locality of the state operations, `joinMem`, `Sim`, `Clean`, `Mirror`, `dupState`, `sim_dup`, `clean_dup` |
| `Asm/AliasCells.lean` | split of `AliasTrace.lean`: `shiftCell`, `storeCells_addr`, `accessCells`, `Summ`/`summ`/`summ_access`, `nextB`/`SummOk`, `view_map` |
| `Asm/Alias.lean`, `Asm/AliasTrace.lean` | the x86 parts (unchanged content) |
| `Asm/AliasIsa.lean` | **`AlIsa`** (an `Isa`, its `Relocatable`, `reads`/`writes`, `fpOk`, `exec_local`, `cells_map`, `cells_reloc`); `isaAl` (aliased machine as an `Isa`), `AccessRun`, `sim_run`, `accessRun_add/step/mono`, **`accessRun_ovr`** (the access condition ignores control components), `traceCells`, `path_access`, `sliceAccess`, `ChainOk`, **`chain_access`**, `seg1_access`; `normCtl_ovr`, `dupState_ovr` |
| `Asm/LibAliasGen.lean` | **`EntryN E0`**, **`EntryAlG E0`**, **`AccessThmG`**, **`CtlThm`**, `MemInput`, `PcFree`, `digest_input`, `outcome_al`, **`mkKernelAlG`**, `ctlThm_of`, `ctlThm_of_pred` |
| `Asm/ArmAliasTrace.lean` | `Arm.cells_map`, `Arm.cells_reloc`, **`Arm.alIsa`**; `Arm.AccessRun`, `Arm.accessRun_add/step`, `Arm.ovr_all_flags`, **`Arm.accessRun_ann`** (segments recorded with fixed flags); `LibArmAl`: `EntryArmAl`, `AccessThmArm`, **`mkKernelArmAl`**, **`lib_inplace_arm`** |
| `Asm/RiscvAliasTrace.lean` | `Riscv.cells_map`, `Riscv.cells_reloc`, **`Riscv.alIsa vlmax`** (`fpOk := ctlOk`: vector footprints depend on `vl`), `Riscv.AccessRun`, `accessRun_add/step`, **`accessRun_vlmax`**; `LibRvAl`: `EntryRvAl`, `AccessThmRv`, **`mkKernelRvAl`**, **`lib_inplace_rv`** |
| `Asm/X86AliasIsa.lean` | **`X86.alIsa`**, `isaAl_eq : X86.alIsa.isaAl = X86.isaAl` (rfl), `accessRun_iff`, `accessThm_g`, **`mkKernelAlOf`** |
| `Asm/ArmFootprint.lean` | adopted verbatim from `all-arm` (the one `Arm.writes`; `ArmAlias.lean` no longer defines it — a merge of all-arm sees identical additions) |

### How a kernel enters the in-place library (no aliased run lemma needed)
`mkKernelAlG I E0 K ha hctl`: from the separate-region kernel `K : KernelThm I.isa (EntryN E0) Digest`
(what `mkKernel`/`mkKernelArm`/`mkKernelRv`/`mkKernelAnn` produce), the access theorem `ha` (normalised
entry) and `hctl` (the run from any control state is, at every step count, the normalised run with some
components overridden — from the same annotation as `K`): the aliased run from `T` (any control state)
follows the separate-region run from `dupState T` (`sim_run`); that run satisfies the access condition
of the normalised run (`accessRun_ovr`) and has `K`'s outcome. Per ISA:
* x86, static programs: `LibAlias.mkKernelAl` (same args as `mkKernel` + `AccessThm`).
* x86, annotated programs (AVX-512, agent x86b's `mkKernelAnn`): `LibAlias.mkKernelAlOf (mkKernelAnn …) ha
  (ctlThm_of_pred X86.alIsa Entry … (annIv …) (annIv_entry …) DepthInv hP (fun _ => rfl) (run_ovr_annJ …))`.
* AArch64: `LibArmAl.mkKernelArmAl` (args of `mkKernelArm` + `AccessThmArm`).
* RISC-V: `LibRvAl.mkKernelRvAl vlmax` (args of `mkKernelRv` + `AccessThmRv vlmax`).

## (4) Recipe: a kernel's in-place theorem from its every-count proof (mechanical)
Inputs: the kernel's every-count file (`Kernels/<K>/All.lean`: `Head`, `ExitAt`, `iter`, `loop`, the
segment lemmas `Gen*.seg_run/seg_frame/seg_moves`) and its built segments `Gen*/Seg.lean`.
1. `python3 gen_inplace.py <K> <Seg>... --eval` (from `lean/`, in the workspace where `Gen*/Seg.lean`
   are built; run it under `systemd-run`, it runs `lake env lean`). The instruction set is read off the
   certificates' type. Output `Kernels/<K>/InPlace/<Seg>.lean`: `certs`, `chain`, `len`, one
   `sum<k>` per slice (`decide +kernel`; peak memory of one slice: scalar_x1 body 25 slices 216 s,
   4.5 GB; all slices in one `decide` needed > 12 GB) and `sums` (by rewriting). Your generated
   proof files are only read.
2. `Kernels/<K>/InPlaceAll.lean`, following the template of the same ISA:
   x86 `Kernels/X86X1/InPlaceAll.lean`, AArch64 `Kernels/ScalarX1/InPlaceAll.lean`, RISC-V
   `Kernels/Rv64X1/InPlaceAll.lean`. One lemma per lemma of `All.lean`, same states and case splits:
   - segment with input/output cells at relocation `rho m` (a batch at node `m`, bound `b = 4m`,
     after the segment `bf = 4m + 4N` for `N` nodes, or the intermediate bound):

         rw [← InPlace.<Seg>.len]
         apply <I>.chain_access (rho m) hρ hw InPlace.<Seg>.certs _ _ _ InPlace.<Seg>.chain <cut> <Ok>
         rw [InPlace.<Seg>.sums, rho_wshift_in, rho_wshift_out]; simp only [SummOk, nextB]
         simp [SummOk, nextB] <;> omega

     (`<I>` = `X86.`-namespace `chain_access` for x86, `Arm.alIsa.chain_access`,
     `(Riscv.alIsa V).chain_access`);
   - one-slice segment without input/output cells: `<I>.seg1_access C.cert0 … InPlace.<Seg>.sum0 b`;
   - concrete steps between segments: `accessRun_step` (x86) / `Arm.accessRun_step` /
     `Riscv.accessRun_step`: `hr`/`hw` by `rw [hpc, prog_N] at hc; simp [reads/writes] at hc` (no cells),
     or, for stack loads/stores, compute the cell (`addr_sp`/`sp_cells` in the RISC-V template);
   - composition: `accessRun_add` with the run equations of `All.lean` (`seg_run`, `run_back`, …);
   - AArch64: segments are recorded with fixed flags (`norm S sc`); `Arm.accessRun_ann … (flag
     annotation of the kernel) … (Arm.ovr_all_flags S _ _ _ _)` moves the condition to the actual state
     (needs `ann pc = Dom.all` at the segment start, decided);
   - the loop: induction as `loop`, with `iter` (from `All.lean`) for the next `Head`.
   - `access_all`: bound `4·off` → `4·(off+done)`; for a tail-calling kernel, `done` = the nodes its
     batches finished before the hand-over (the bound stays at `4·(off+done)` while the remaining
     nodes are not touched).
3. `access_thm : AccessThm… rodata prog entry steps` from `access_all`; the hand-over clause
   (`Bf ≤ 8·(off+done)`): for kernels that never tail-call it follows from `norm_thm` (`tail = none`,
   see the templates); for tail-calling kernels, from the hand-over `Entry` (its output pointer is
   `32·(off+done)`: `LibAlias.done_eq_of_rdi`; the clause also gets `done ≤ count`) and `Bf = 4·(off+done) ≤ 8·(off+done)`.
4. `kernelAl := mkKernelAl… … norm_thm access_thm` and the table: in the order of `LibTable.x86Shape`
   (resp. `armShape`, `rvShape`), `LibAlias.lib_inplace_x86 (fun cfg => T cfg) hT`,
   `LibArmAl.lib_inplace_arm T hT`, `LibRvAl.lib_inplace_rv V T hT`.
5. Batches of `N` nodes whose digest stores come after some input loads of the same batch (`gap` ≠
   `none` in a summary): `SummOk` needs `4m + (hiW+1) ≤ gap + 8m`, i.e. a condition on `m`; with `m`
   free, `omega` decides it when it holds for all `m ≥ 0`, otherwise the first iteration(s) need the
   actual `m`.

### Status of the pilots (agent `inplace2`)
* **x86_x1**: `lib_inplace_x86_x1` from `EntryAlX86` (any flags/masks/vl) through `mkKernelAl`.
* **scalar_x1 (AArch64)**: `Kernels/ScalarX1/InPlaceAll.lean`: `body_access`, `loop_access`,
  `exit_access`, `access_all`, `access_thm`, `kernelAl`, **`lib_inplace_scalar_x1`**. Needs all-arm's
  `ScalarX1/All.lean` and segments (+ `Asm/{Flags,ArmFlags,ArmSteps,Nodes,ArmEntry}.lean`): checked in
  `/root/kt-inplace/arm` (a copy of `/root/kt-arm/lean`). Axioms: propext, Classical.choice, Quot.sound
  + bv_decide certificates; no sorry.
* **rv64_x1 (RISC-V)**: `Kernels/Rv64X1/InPlaceAll.lean` (`back_access`, `body_access`, `loop_access`,
  `exit_access`, `access_all` at `vlmax = 2`, `access_thm` for every `vlmax` via `accessRun_vlmax`,
  `kernelAl`, **`lib_inplace_rv64_x1`**). Being checked in `/root/kt-inplace/rv` (unit `kt-inplace-rv3`:
  the rv64_x1 body segment (rebuilt on this core, one slice ~13 GB), then `/root/kt-inplace/rv2.sh`:
  `gen_inplace.py Rv64X1 GenSE GenSB GenSX --eval`, the `InPlace/*` modules, `InPlaceAll`, axioms in
  `/root/kt-inplace/logs/ax3.log`; log `/root/kt-inplace/logs/rv2.log`). The `InPlace/*.lean` files are
  generated there (copy them into the branch after the run).

### Open issues (agent `inplace2`)
* **RISC-V model change (agent `rvu`, branch all-rvu: `lbu`, `sb`, `vsetvli e8`, `vle8.v`, `vse8.v`, M9
  shift fix)**: after that merge, `RiscvAlias.reads`/`exec_local` and `RiscvAliasTrace.cells_map/
  cells_reloc/reads_ovr/writes_ovr` need the new constructors (byte loads/stores: cells of the word
  containing the byte; `vle8/vse8`: `nf·vl` bytes → words), and the RISC-V kernels' in-place proofs
  follow their new segments (`GenSC`, `GenSI`, `GenSJ`, …).
* **all-arm merge**: `Asm/ArmFootprint.lean` here is a verbatim copy of all-arm's (identical addition);
  `ScalarX1/InPlaceAll.lean` needs all-arm's `ScalarX1/All.lean` and `Asm/{Flags,ArmFlags,ArmSteps,
  Nodes,ArmEntry}.lean` (not on lean-verification yet).
* **x86 AVX-512**: route `mkKernelAlOf` + `ctlThm_of_pred` with x86b's `run_ovr_annJ` (branch
  all-x86b, not merged here) — not instantiated yet (no AVX-512 every-count proof on this branch).
* The x86 core in the checking workspace `/root/kt-inplace/x86` is that of `/root/kt-diff/ws`
  (`Iter.lean`/`Tools.lean` of all-x86); the in-place files do not depend on the difference.
  RISC-V was checked in `/root/kt-inplace/rv` with this branch's core.
* Segment sizes: one body slice of rv64_x1 needs ~13 GB (`decide`/`bv_decide` of the kernel agents'
  segment, not of the in-place summaries).

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
