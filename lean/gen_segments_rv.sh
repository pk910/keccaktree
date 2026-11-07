#!/bin/bash
# Generate (and optionally build) the segments of a 1-node RISC-V kernel's all-count theorem
# (Keccaktree/Kernels/<Ns>/All.lean): the loop is
#   entry:  br .ne a2, zero (concrete) ; [frame stores, count spill]   = GenSE
#   head:   GenSB = loop body (one node, 25 slices; end cut = start cut moved by one node, LOOP=1)
#   back:   ld t0,[sp+CNT]; addi t0,t0,-1; sd t0,[sp+CNT]; beq t0,zero,exit; j head   (concrete)
#   exit:   GenSX = restores ; ret (concrete)
# Step positions are those of the count-1 run (kttool paths <k> 1 ...: position 0 = the entry `br`).
# Usage: gen_segments_rv.sh <kernel> <Ns> <se_end> <sb_end> <sx_start> <sx_end> <cnt_cell_var> [build P]
set -e
cd "$(dirname "$0")"
k=$1; ns=$2; SE_END=$3; SB_END=$4; SX_A=$5; SX_B=$6; CNTV=$7
CNTQ=$(python3 -c "v=$CNTV-288; r=v%8; e=v//8; print(e//2 if e%2==0 else -(e+1)//2)")
mkdir -p plans
python3 find_plan.py $k 1 0 > plans/${k}_c1.json
K=$k SE_END=$SE_END SB_END=$SB_END SX_A=$SX_A SX_B=$SX_B python3 - <<'PY'
import json, os
k = os.environ['K']; se, sb, xa, xb = (int(os.environ[v]) for v in ('SE_END', 'SB_END', 'SX_A', 'SX_B'))
p = json.load(open(f"plans/{k}_c1.json"))
cuts = [t for t in p["cuts"] if se < t + 1 < sb]
body = {"kernel": k, "count": 1, "lanes": 0, "entry": se, "end": sb, "cuts": cuts,
        "rounds": [[0]] + [[min(i + 1, 24)] for i in range(len(cuts))] + [[24]]}
json.dump(body, open(f"plans/{k}_body.json", "w"))
for name, a, b, r in (("e", 1, se, 0), ("ex", xa, xb, 24)):
    json.dump({"kernel": k, "count": 1, "lanes": 0, "entry": a, "end": b, "cuts": [], "rounds": [[r], [r]]},
              open(f"plans/{k}_{name}.json", "w"))
PY
ctl0() { python3 -c "
import sys, ast
l = [l for l in open(sys.argv[1]).read().splitlines() if l.startswith('control words')][0]
print(','.join(str(x) for x in ast.literal_eval(l.split(':', 1)[1].strip())[0]))" "$1"; }
gen() { # name gendir end_ctl write_ok moves data loop
  rm -rf Keccaktree/Kernels/$ns/$2
  PLAN=plans/${k}_$1.json OUTDIR=Keccaktree/Kernels/$ns/$2 GEN=$2 NS=$ns.$2 PROG_NS=$ns ISA=Riscv ISA_EXPR="(Riscv.isa 2)" \
    BATCH=1 SEG=1 END_CTL=$3 FORBID_CTL=268,$CNTV WRITE_OK="$4" MOVES=$5 DATA=$6 LOOP=$7 \
    python3 gen_plan_proof.py $k $ns 1 0 > plans/gen_${k}_$1.log 2>&1
  echo "$2: $(grep 'control words' plans/gen_${k}_$1.log | cut -c1-160)"
}
gen body GenSB 258 "fun p => (p.1 == 3 && p.2 != $CNTQ) || (p.1 == 2 && decide (0 ≤ p.2) && decide (p.2 < 4))" "" "" 1
gen e GenSE "$(ctl0 plans/gen_${k}_body.log)" "fun p => p.1 == 3" "$CNTV:268" 0 ""
gen ex GenSX "" "fun _ => false" "" 0 ""
if [ "$8" = build ]; then
  P=${9:-4}
  for g in GenSE GenSX GenSB; do
    ./build_plan.sh $ns $g "$(ls Keccaktree/Kernels/$ns/$g/Slice*.lean | wc -l)" "$P"
    lake build Keccaktree.Kernels.$ns.$g.Seg 2>&1 | grep -E "error|Built Keccaktree.Kernels.$ns.$g.Seg"
  done
fi
