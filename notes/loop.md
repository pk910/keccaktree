# Agent `loop`: composition of segment proofs (multi-batch, tails, cross-kernel)

Branch `loop` (worktree `src/wt-loop`), remote workspace `/root/kt-loop` (rsync excluding .lake/.git/Gen*/).

## Design
* **Plan-driven generator** `lean/gen_plan_proof.py` (+ `find_plan.py`, `build_plan.sh`): a *plan* is one
  recorded run on `count` nodes with a list of cuts and a per-node round schedule (`rounds[c][n]`); a
  slice advances any subset of nodes by one round (`act c n`, `sched A c`); nodes already finished keep
  their digest cells as carried invariants (`KT_CELLS` makes kttool report unwritten cells as bare
  variables). The one-batch generator is the special case "23 cuts, all nodes advance". Output modules
  `Keccaktree/Kernels/<K>/GenC<count>/{Invs,Slice*,Batch,Final}.lean`, namespace `<K>.C<count>`:
  `chain : Inv0 env0 A → InvK (envAt env0 K) (AAt A K)`, `aat_n : AAt A K n = Spec.rounds r (A n)`,
  `kernel_keccak256` for the nodes finished (`done` list), `handover` (tail-call registers closed) when
  the run ends in a tail call. `find_plan.py <kernel> <count> <lanes>` derives the plan from a scan
  (first step each node's round r is complete; round 24 = digest words in the output region).
* **`Asm/Loop.lean`** (builds): `RelocFacts isa` — the interface expected from agent `reloc`
  (`Reloc`, `one`/`comp`, `relocE`, `relocState`, `shiftVar`/`unshiftVar` inverse pair, `BranchSafe`,
  `relocState_one/comp`, `execTrace_reloc`, `pathOk_reloc`, `readVar_reloc`, `eval_reloc`, `err_reloc`);
  `SliceFacts` (ctl, sc, idx, ctlNext, scNext, `path`, `safe`, `glue` for every ρ);
  `SliceFacts.run_reloc`: a slice at a relocated cut runs its path and lands on the evaluation of the
  relocated symbolic result, env = `conj ρ (envMap result)`; `seg_run_reloc`: chained slices;
  `IterFacts` (body segment whose end cut is the head cut relocated by `step`), `IterFacts.run`:
  m iterations from iteration k₀ reach iteration k₀+m (induction); `KernelOutcome` (done / handover).
* **`Asm/Library.lean`** (builds): `KernelThm` (per-kernel all-count theorem shape: steps, digests of
  finished nodes, earlier output words preserved, tail call to `next` with the remaining nodes from
  its entry state at the advanced offset), `LibRun` (continue in the called kernel), `RanksOk`,
  `DigestLocal`, `lib_step`, `lib_correct`: by induction on `count·(maxRank+1) + rank`, every
  library run from any kernel's entry state finishes every node.

## Status
* `Asm/Loop.lean`, `Asm/Library.lean`: build on the remote (axiom-free; relocation facts are hypotheses).
* Plan generator validated end to end: **X86X1 count 2** (two iterations of the batch loop, 49 slices,
  schedule: node 0 rounds 1..24 then node 1) — `Keccaktree.Kernels.X86X1.C2.kernel_keccak256` proved
  (both digests; axioms propext, Classical.choice, Quot.sound + 1397 bv_decide certificates).
* Running: X86X1 counts 1, 3; Avx2X4 count 5 (batch + tail call to avx2_x2), count 8 (two batches).

## Lessons (generator)
* `envAt` with literal arms is compiled by well-founded recursion (irreducible): chain with
  per-bound equation lemmas `envAt_c` (`simp only [envAt]`) and an ascribed `have` per step; an
  unascribed 49-step chain made the final defeq check blow up (70 GB, OOM).
* `AAt A K` must never be unfolded at once (`sched` duplicates `AAt A c n` in both `if` branches):
  per-node facts `aat_n` are proved one bound at a time (`sched_act`/`sched_nact`, `rounds_succ`).
* Builds of plan modules run under `systemd-run --scope -p MemoryMax=40G` (shared machine).

## Integration with `reloc` (what remains)
* `RelocFacts` is the exact interface Loop.lean needs; `Reloc.lean` must provide an instance per ISA
  (`X86.isa`, `Arm.isa`, `Riscv.isa v`): `relocState`, `relocE`, `shiftVar`/`unshiftVar` (memVar of
  rInput/rOutput shifted by the batch offset in words), `execTrace_reloc`/`pathOk_reloc` under
  `BranchSafe`, `readVar_reloc`, `eval_reloc`, `err_reloc`.
* Generator (next step): for a kernel with batch size N, emit the loop-body segment once (the plan's
  slices of iteration 0, from loop head to loop head) as `SliceFacts` values (`path` = the existing
  kernel-checked `path{c}`, `glue` from `ctrl{c}`/`ctlv{c}` + `RelocFacts`), an `IterFacts` with
  `step` = shift by N nodes, and the per-count-class entry/exit/tail segments (proved per value of
  the remaining count r < N, plus the entry policy classes) — then `KernelThm.thm` for every count from
  `IterFacts.run` (m = count / N iterations) + the exit plan for r = count % N.
* The lane invariants (`Inv`, `step`) are per-node and position independent except for the
  input/output memory variables, which relocation shifts: the iteration's `chain` at iteration k is
  the base chain under `envShift` (`eval_reloc`), so the digest facts of iteration k follow from the
  base ones with node index n + k·N.

## Integration with `paths`
* The plan finder needs, per kernel, the loop head / exit / tail instruction indices; `paths`' JSON
  (segments per count class) replaces `find_plan.py`'s whole-run scan for the segment generator.

## Commands
    rsync -az --exclude .lake --exclude .git --exclude 'Gen*/' ./ root@2.28.133.253:/root/kt-loop/
    python3 find_plan.py x86_x1 2 0 > plans/x86_x1_c2.json
    PLAN=plans/x86_x1_c2.json OUTDIR=Keccaktree/Kernels/X86X1/GenC2 GEN=GenC2 NS=X86X1.C2 PROG_NS=X86X1 BATCH=1 \
      python3 gen_plan_proof.py x86_x1 X86X1 2 0
    ./build_plan.sh X86X1 GenC2 <K> 6
