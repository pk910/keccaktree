#!/bin/bash
# Generate (and optionally build) the body variants of an RVV kernel's all-count theorem
# (Keccaktree/Kernels/<Ns>/All.lean): GenB<w> = the batch body with vl = w (w = 1..VLMAX), from the
# count-w run, positions [10, SUB) (instruction 14 `vlseg` .. the `sub a2, a2, t0`).  The frame
# (entry test, sp, t5 = 1<<63, a7 = (a0|a1)&7), the head (mv, beqz a7, vsetvli, bnez a7) and the
# back edge (sub, bnez a2) are concrete steps of All.lean.
# Usage: gen_segments_rvv.sh <kernel> <Ns> <ProgNs> <VLMAX> <sub_pos> [w ...]   (default: all w)
set -e
cd "$(dirname "$0")"
k=$1; ns=$2; pns=$3; V=$4; SUBP=$5; shift 5
WS=${*:-$(seq 1 $V)}
mkdir -p plans
for w in $WS; do
  python3 find_plan.py $k $w $V > plans/${k}_c$w.json
  K=$k W=$w SUBP=$SUBP python3 - <<'PY'
import json, os
k, w, sp = os.environ['K'], int(os.environ['W']), int(os.environ['SUBP'])
p = json.load(open(f"plans/{k}_c{w}.json"))
cuts = [t for t in p["cuts"] if 10 < t + 1 < sp]
body = {"kernel": k, "count": w, "lanes": 0, "entry": 10, "end": sp, "cuts": cuts,
        "rounds": [[0] * w] + [[min(i + 1, 24)] * w for i in range(len(cuts))] + [[24] * w]}
json.dump(body, open(f"plans/{k}_b{w}.json", "w"))
PY
  rm -rf Keccaktree/Kernels/$ns/GenB$w
  PLAN=plans/${k}_b$w.json OUTDIR=Keccaktree/Kernels/$ns/GenB$w GEN=GenB$w NS=$ns.GenB$w PROG_NS=$pns ISA=Riscv \
    ISA_EXPR="(Riscv.isa $V)" BATCH=1 SEG=1 START_CTL=286 END_CTL=${END_CTL:-261,266,267,273,286} FORBID_CTL=268 \
    WRITE_OK="fun p => p.1 == 2 && decide (0 ≤ p.2) && decide (p.2 < $((4 * w)))" MOVES=268:268 \
    python3 gen_plan_proof.py $k $ns $w $V > plans/gen_${k}_b$w.log 2>&1 || { echo "GenB$w FAILED"; tail -5 plans/gen_${k}_b$w.log; }
  echo "GenB$w: $(grep 'control words' plans/gen_${k}_b$w.log | cut -c1-160) warnings=$(grep -c WARNING plans/gen_${k}_b$w.log)"
done
