# Agent `lib`: library layer (entry control state, thresholds, table, dispatch)

Branch `all-lib` (worktree `src/wt-lib`, off f3a7dc5), remote `/root/kt-lib/lean`
(`./sync.sh <targets>` rsyncs `lean/` and runs `lake build` under `systemd-run -p MemoryMax=10G`).

## 1. Control state left by a tail call (DONE)
* `Asm/EntryCtl.lean` (x86): `ovr D c s` overrides the *dirty* control components `D : Dom`
  (zf, cf, nf, vf, vl, mask registers `k` listed) with values `c : Ctl`.
  - `exec_ovr`: `ctlOk D i → s.halted = false → (exec i s).err = false →
     exec i (ovr D c s) = ovr (ctlAfter D i) c (exec i s)` — one theorem for all instructions
     (reads: jcc/jcct per condition, masked vmov, `sub` (may write flags); must-writes: test/cmp*/xorz
     zf+cf, dec/decm zf, bt cf, kmovw k_j).
  - `exec_ovr_sub_ptr`: `sub` on a pointer register writes no flag (model) — commutes for any `D`.
  - `run_ovr_path`: along a run visiting `idx` (pcs), `ctlOkTrace D (idx.map prog.getD)` ⇒
     `run (ovr D c s) = ovr (ctlAfterTrace ..) c (run s)`  ← for kernels whose masks are written inside
     the batch (AVX-512: `kmovw k1` at the batch start); `pathOk` of a segment gives the pcs.
  - `run_ovr_static`: no instruction of the program touches `D` (decided on `prog`) ⇒ every run commutes.
  - `run_ovr_prefix`: entry prefix = set-up (`push`, `mov d≠rsp`, `sub rsp`, `andi rsp`, rsp tracked as a
     stack pointer offset) then a compare (`test`/`cmpi`/`cmpr`) — flags clean afterwards.
  - `normCtl s` (= fresh-call control), `ovr_normCtl`, `run_normCtl` (prefix + static combined).
* `Asm/LibX86.lean`: the shared x86 calling convention `Entry` (no pc constraint), `Digest`,
  `digest_local`, **`EntryX86 name off count input S := Entry off count input (normCtl S) ∧ bound`**
  (any flags/masks/vl), `NormThm` (what a kernel proof provides, from a normalised entry state),
  `mkKernel` (NormThm + `prefixOk` + static check ⇒ `Library.KernelThm`), `outcome_ovr`.
* `Asm/Library.lean` refactor: `Outcome` predicate; `KernelThm.targets` (static tail-call targets,
  `next ∈ targets` in the outcome); `RanksOk` now static (every target in the table with lower rank),
  `shapeOk`/`ranksOk_of_shape` (decidable on name/rank/targets).
* `Kernels/X86X1/Lib.lean`: `kernel := mkKernel "x86_x1" 0 [] … 8 (decide) (decide) … norm_thm`,
  `lib_x86_x1` for `EntryX86` (any control state). Axioms: propext, Classical.choice, Quot.sound +
  bv_decide certificates; no sorry. (Old `EntryX86`/`kernel` section removed from `All.lean`.)

### Statement shape for kernel agents (x86)
Provide `NormThm rodata prog entry steps targets`:
`∀ off count input S, LibX86.Entry off count input S → 64*(off+count) ≤ 2^54 → S.pc = entry →
  Library.Outcome EntryX86 Digest targets off count input S (X86.isa.run rodata prog (steps off count) S)`
(hand-over: `EntryX86 next (off+done) (count-done) input {Sf with halted := false, tail := none}`, i.e.
`LibX86.Entry` of the normalised hand-over state: g all zero, depth 0, rdx/rsp/rsi/rdi, input).
Then `mkKernel name rank targets rodata prog entry steps m (by decide +kernel) (by decide +kernel) hm thm`.
For AVX-512 kernels (masked moves) the static check fails: use `run_ovr_path` per segment (the batch
starts with `kmovw k1`), or prove `NormThm` directly for `EntryX86` states.

## 2. Runtime thresholds (word 112 of the constant image) (DONE: model lemmas)
`Asm/Rodata.lean` (x86):
* `AgreeExcept r1 r2 w` (images agree except word `w`), `noReadW w i s` (the instruction's loads avoid word
  `w`; `false` if an address does not decode), **`exec_rodata_eq`**: `noReadW → exec r1 i s = exec r2 i s`
  (all instructions).
* **`pathW r prog w idx t`** (symbolic, like `pathOk`, plus `noReadW` at every step; kernel-decidable on a
  cut) ⇒ **`pathW_run`**: for every env, `run r2 … (eval t) = run r1 … (eval t)`; `pathOk_of_pathW`;
  **`pathW_reloc`**: `pathW` holds at every relocated cut (same side condition as `pathOk_reloc`).
* `exec_cmprm_word` (the policy `cmp reg, [rip+8w]` with the word = number `v < 2^55`),
  `classRep lo hi v = max (lo-1) (min v hi)`, `classRep_gt`, **`policy_ja_class`**: `cmp x,[w]; ja t`
  with `x ∈ [lo,hi]` under image `setWord rodata w v` = under `setWord rodata w (classRep lo hi v)` up to
  dirty ZF/CF (`ovr {zf,cf}`), `classes_small_tail` (avx2_x4: x ∈ [2,3], reps {1,2,3}),
  `classes_mid_tail` (avx2_x10: x ∈ [5,9], reps {4..9}), `setWord_agree`, `setWord_getD`.
* Recipe for the x86 agent (avx2_x4 / avx2_x10, any threshold v < 2^55): prove the kernel for the image
  `setWord rodata 112 rep` for each class rep; for a value v: every segment except the policy step has
  `pathW (setWord rodata 112 rep) prog 112 idx cut` (decide; `pathW_reloc` for relocated cuts) ⇒ same run
  under v (`pathW_run`); the policy step: `policy_ja_class`; the dirty flags after it: `run_ovr_path` with
  `D = {zf, cf}` up to the next compare (`cmpi 0 (2)` before the `jcct`).
* (Former gap, fixed by the core change below: threshold words ≥ 2^56 used to decode as pointers.)

## 3. Library tables (DONE: statements; kernel theorems to be plugged in)
`Asm/LibTable.lean`: `x86Shape` (14 kernels), `armShape` (6), `rvShape` (4; one table per `vlmax`):
(symbol `keccaktree_keccak256_<k>`, rank = depth in the tail-call graph, static targets from the programs'
`tailcall`/`jcct`), `shapeOk` decided for all three; `lib_of_shape` (any table of a given shape ⇒ every kernel,
every count, every node); `lib_x86` (per threshold configuration), `lib_arm`, `lib_rv vlmax`.
Calling conventions: `LibX86.EntryX86` (rdi/rsi/rdx/rsp), `LibTable.EntryArm` (x0/x1/x2/sp=31),
`LibTable.EntryRv` (a0/a1/a2/sp=x2); all normalise the control part (`normCtl`): any flags/masks/vl.
Kernel names must be the full symbols (`KernelThm.name`), e.g. `X86X1.Lib.kernel` = `keccaktree_keccak256_x86_x1`.
**Plug-in**: `T := [k_x86_x1, k_avx2_x2, …]` in the order of `x86Shape`, `hT : T.shape = x86Shape := rfl`
(or `by decide`), then `LibTable.lib_x86 (fun cfg => T cfg) hT`.

## 4. Dispatch (`src/keccaktree.c`, upstream main 6ede9ab = PR #17 merge, src identical to lean-verification) (DONE)
`Keccaktree/Dispatch.lean`: `detectX86` (OSXSAVE, XCR0 ymm/zmm state, AVX2, AVX512F/VL, BMI1/2;
calibration = oracle returning a candidate; tail/mid-tail calibration writes), `detectArm` (Linux HWCAP / Apple
sysctl / other OS), `detectRv` (hwprobe V/Zbb/Zvkb, vlenb ≥ 16).
Proved: `detectX86_sound`/`detectArm_sound`/`detectRv_sound` (portable C kernel or a library kernel whose ISA
extensions the CPU reports; `needs*_closed`: tail targets need no more than the caller), `detectX86_cfg`
(thresholds after detection: small ∈ {1,2}, mid ∈ {4,5,9}), `hash_x86`/`hash_arm`/`hash_rv`: after
`keccaktree_init(NULL)`, `keccaktree_hash(out,in,count)` is `Proof.hashC_spec` (generic C) or a library run with
every digest (`LibOk`) from the entry state at offset 0.  Axioms: propext, Classical.choice, Quot.sound.
Trusted (documented in the file): C compiler/ABI (argument registers ↔ `Entry`), CPUID/XGETBV/HWCAP/hwprobe
reports, calibration runs (in-place `fns[i](buf, buf, n)`, aliasing not in the model, results discarded),
thread races on first call, user overrides, user setter values ≥ 2^55, buffer alignment (model regions are
64-byte aligned; unaligned = queued item 3), `64·count ≤ 2^54` bytes.
RVV: dispatch picks rvv/rvv_zvkb for every VLEN ≥ 128; kernel proofs exist per VLEN (`lib_rv vlmax`) — the
proved VLENs bound the claim (gap for VLENs not proved).

## 5. AArch64 flags at entry (DONE)
`Asm/ArmEntryCtl.lean`: `Arm.exec_ovr` (all AArch64 instructions; reads: `csel`/`b.cond` per condition;
must-writes: `cmp`/`subs` all of NZCV), `exec_pc` (static successors `succs`; AArch64 has no calls), dirty-set
annotations `AnnOk prog ann` ⇒ **`run_ovr_ann`** (run from any flags = run from the normalised state up to the
still-dirty components), `ovr_mono`, the may-dirty fixpoint `annotate` and compact interval certificates
`flagAnn I` / `flagAnnOk` (kernel-decidable, iterates over `prog.toList`; ~1-2 GB, seconds).
`Asm/LibArm.lean`: `NormThmArm`, **`mkKernelArm`** (NormThmArm + `AnnOk` + entry dirty ⇒ `KernelThm Arm.isa EntryArm
Digest`), `outcome_ovr_arm`.  `Kernels/ArmFlags.lean`: certificates for all 6 AArch64 kernels (no kernel reads a
flag before its own `cmp`/`subs` on any path): scalar_x1 [(0,2443),(2444,2451)], sha3_x2 [(0,9),(1599,1604)],
neon_x2 [(0,9),(3788,3793)], sha3_x3/sha3_x3r/neon_x3 [(0,1)].
For the arm agent: `mkKernelArm (sym k) rank targets rodata prog 0 steps (flagAnn ArmFlags.k) (ArmFlags.k_ok)
(ArmFlags.entries.…) normThm`.
Open: the same for RISC-V `vl` (RVV kernels: `vl` at a call is unspecified by the ABI; the model's entry has
vl = 0) — the static-successor approach applies (RISC-V kernels make no calls either); x86 masks for the AVX-512
kernels need `run_ovr_path` on the segment paths (the x86 batch is a `call`ed subroutine, so its `ret` has a
dynamic successor).

## 6. RISC-V vector length at entry (DONE)
`Asm/RiscvEntryCtl.lean`: `Riscv.exec_ovr` (reads `vl`: every vector instruction; writes: `vsetvli`), `exec_pc`,
`AnnOk`, **`run_ovr_ann`**, `vlAnn`/`vlAnnOk` interval certificates, `annotate`/`vlIntervals`.
`Asm/LibRv.lean`: `NormThmRv vlmax`, **`mkKernelRv`**.  `Kernels/RvVl.lean`: certificates for rv64_x1, zbb_x1,
rvv, rvv_zvkb (entry index 1): rvv [(1,13),(383,384)], rvv_zvkb [(1,13),(240,241)] — `vl` is set by `vsetvli`
before any vector instruction on every path.  Axioms: propext, Quot.sound (no bv_decide).

## Summary of open items (lib)
* x86 AVX-512 masks at entry: `mkKernel`'s static check fails for the six AVX-512 kernels (masked moves); the
  x86 agent must use `run_ovr_path` along the batch path (the batch starts with `kmovw k1`) or a dirty-set
  annotation with call/return handling (the x86 batch is `call`ed: `ret` has a dynamic successor).
* Thresholds ≥ 2^56 (model decodes them as pointers); VLENs without RVV kernel proofs.
* Calibration runs alias input and output (`fns[i](buf, buf, n)`): outside the model (results discarded).


## CORE CHANGE (follow-up 1, commit ca9c63d): unsigned policy compare `cmprm`
Kernel agents: this changes `X86.exec` for one instruction.
* `.cmprm a m` (`cmp reg, qword ptr [m]`; used only by avx2_x4 idx 761 and avx2_x10 idx 1884, both
  `[rip + 896]` = `.data` word 112) now reads the loaded word as a **data constant** (`asConst`) and compares
  it with the register's number as **64-bit unsigned** (`X86.setFlagsNum s x w`: ZF = `ofInt x = w`,
  CF = `(ofInt x).toNat < w.toNat`); the register must be a number (region 0), else fault.  Before: the word
  was decoded as an address (`asAddr`), so words ≥ 2^56 decoded as pointers and the compare faulted.
* `X86.decodes (.cmprm a m)` no longer lists the loaded word (it is not decoded as an address any more):
  `mb m ++ [s.getGD a]` — fewer `relocOk` side conditions.
* Updated proofs: `Hom.exec_map_cmprm`/`err_exec_cmprm`, `Reloc.exec_reloc_cmprm`; `EntryCtl.exec_ovr`,
  `Rodata.exec_rodata_eq`/`pathW_reloc`, `Footprint` unchanged and green.  `Rodata.exec_cmprm_word` and
  **`policy_ja_class` now hold for every `v < 2^64`** (`classRep` covers all 64-bit setter values:
  avx2_x4 `≥ 3` and avx2_x10 `≥ 9` include every large value).
* Runs unchanged: identical for every count in which the word is < 2^56 (all existing runs): see the kttool
  `paths` comparison below.  X86X1 All/Lib rebuilt on the new core (see below).

## Follow-up 2: dispatch (commit ca9c63d)
* Setters `keccaktree_avx2_small_tail`/`_x10_mid_tail` store their `uint64_t` unclamped (asm:
  `mov qword ptr [rip+.L…], ARG_OUT; ret`) — modelled as `Event.writeSmall/writeMid v` (value mod 2^64);
  every value is in a covered class.
* `Event` model of the globals (`detectStore`, `override`, setter writes), `reachable`: after any interleaving,
  `hash_ptr` is init_and_hash / generic / a supported library kernel / a user override; `reachable_cfg`;
  `hash_x86_reachable`: in every reachable state the library theorem holds for whatever thresholds a call
  reads.  Memory-model assumption (documented in Dispatch.lean): aligned 8-byte plain stores/loads of
  `hash_ptr` and the threshold words are not torn (x86-64 atomic, AArch64/RISC-V single-copy atomic); C11
  formally calls the race UB.  Remaining trusted: compiler/ABI, CPU feature reports, calibration's in-place
  scratch runs (aliasing, results discarded), user override functions.
