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
