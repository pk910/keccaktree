#!/bin/bash
# Generate the misaligned-batch bodies of an RVV kernel (Keccaktree/Kernels/<Ns>/GenM<w>): from the
# `vlseg8e64 v0, (sp)` (instruction 21) to the `bnez a7` after the rounds, in the count-w run with the
# input at byte 1 (KT_MIS=1,0: the bounce path), positions [17, END).  Its input is the bounce buffer
# (stack words), its output the digest lanes in v0..v3; the pointers, count and a7 are kept (moves),
# never control words, so the body does not depend on the misalignment.  The head, the byte copies
# (vle8/vse8), the vsseg4 into the buffer and the pointer advance are concrete steps (AllU.lean).
# Usage: gen_segments_rvvu.sh <kernel> <Ns> <ProgNs> <VLMAX> <end_pos> [w ...]
#   rvv: end 5776; rvv_zvkb: end 3169
set -e
cd "$(dirname "$0")"
k=$1; ns=$2; pns=$3; V=$4; EP=$5; shift 5
WS=${*:-$(seq 1 $V)}
mkdir -p plans
export KT_MIS=1,0
for w in $WS; do
  python3 find_plan.py $k $w $V > plans/${k}_m_c$w.json
  K=$k W=$w EP=$EP python3 - <<'PY'
import json, os
k, w, ep = os.environ['K'], int(os.environ['W']), int(os.environ['EP'])
p = json.load(open(f"plans/{k}_m_c{w}.json"))
cuts = [t for t in p["cuts"] if 17 < t + 1 < ep]
body = {"kernel": k, "count": w, "lanes": 0, "entry": 17, "end": ep, "cuts": cuts,
        "rounds": [[0] * w] + [[min(i + 1, 24)] * w for i in range(len(cuts))] + [[24] * w]}
json.dump(body, open(f"plans/{k}_m{w}.json", "w"))
PY
  rm -rf Keccaktree/Kernels/$ns/GenM$w
  PLAN=plans/${k}_m$w.json OUTDIR=Keccaktree/Kernels/$ns/GenM$w GEN=GenM$w NS=$ns.GenM$w PROG_NS=$pns ISA=Riscv \
    ISA_EXPR="(Riscv.isa $V)" BATCH=1 SEG=1 START_CTL=286 END_CTL=258,261,286 FORBID_CTL=266,267,268,273 \
    WRITE_OK="fun _ => false" MOVES=266:266,267:267,268:268,273:273 INV0=mem3 INVK=regs NO_RC_MID=1 \
    python3 gen_plan_proof.py $k $ns $w $V > plans/gen_${k}_m$w.log 2>&1 || { echo "GenM$w FAILED"; tail -5 plans/gen_${k}_m$w.log; }
  echo "GenM$w: $(grep 'control words' plans/gen_${k}_m$w.log | cut -c1-160)"
done
