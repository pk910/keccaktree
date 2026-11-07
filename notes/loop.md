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
* Loop.lean, Library.lean: compile (axiom-free, relocation facts are hypotheses).
* gen_plan_proof.py: validating on X86X1 count 2 (two one-node batches) — see log /root/kt-loop-t1.log.

## Commands
    rsync -az --exclude .lake --exclude .git --exclude 'Gen*/' ./ root@2.28.133.253:/root/kt-loop/
    python3 find_plan.py x86_x1 2 0 > plans/x86_x1_c2.json
    PLAN=plans/x86_x1_c2.json OUTDIR=Keccaktree/Kernels/X86X1/GenC2 GEN=GenC2 NS=X86X1.C2 PROG_NS=X86X1 BATCH=1 \
      python3 gen_plan_proof.py x86_x1 X86X1 2 0
    ./build_plan.sh X86X1 GenC2 <K> 6
