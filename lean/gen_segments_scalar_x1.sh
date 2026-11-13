#!/bin/bash
# Generate (and optionally build) the three segments of scalar_x1's all-count theorem
# (Keccaktree/Kernels/ScalarX1/All.lean):
#   GenSE1  steps [0,6)       entry: stp frame (x29/x30 pre-index, callee-saved)   (keeps x2)
#   GenSB   steps [7,2442)    loop body, one node, 25 slices, end cut = start cut (LOOP=1);
#                             the count goes x2 -> [sp+112] -> x2 (MOVE_CHAIN)
#   GenSX   steps [2444,2450) epilogue (ldp restores)
# The count-dependent instructions (cbz x2 at 6, subs x2 at 2442, b.ne at 2443, ret at 2450) are the
# concrete lemmas of Asm/ArmSteps.lean.  Usage: gen_segments_scalar_x1.sh [build P]
set -e
cd "$(dirname "$0")"
mkdir -p plans
python3 find_plan.py scalar_x1 1 0 > plans/scalar_x1_c1.json
python3 - <<'PY'
import json
p = json.load(open("plans/scalar_x1_c1.json"))
cuts = [t for t in p["cuts"] if 7 < t + 1 < 2442]
body = {"kernel": "scalar_x1", "count": 1, "lanes": 0, "entry": 7, "end": 2442, "cuts": cuts,
        "rounds": [[0]] + [[min(i + 1, 24)] for i in range(len(cuts))] + [[24]]}
json.dump(body, open("plans/scalar_x1_body.json", "w"))
for name, a, b, r in (("e1", 0, 6, 0), ("ex", 2444, 2450, 24)):
    json.dump({"kernel": "scalar_x1", "count": 1, "lanes": 0, "entry": a, "end": b, "cuts": [], "rounds": [[r], [r]]},
              open(f"plans/scalar_x1_{name}.json", "w"))
PY
ctl0() { python3 -c "
import sys, ast
l = [l for l in open(sys.argv[1]).read().splitlines() if l.startswith('control words')][0]
print(','.join(str(x) for x in ast.literal_eval(l.split(':', 1)[1].strip())[0]))" "$1"; }
gen() { # name gendir end_ctl write_ok moves data loop
  rm -rf Keccaktree/Kernels/ScalarX1/$2
  PLAN=plans/scalar_x1_$1.json OUTDIR=Keccaktree/Kernels/ScalarX1/$2 GEN=$2 NS=ScalarX1.$2 PROG_NS=ScalarX1 ISA=Arm BATCH=1 SEG=1 \
    END_CTL=$3 FORBID_CTL=258,2097411 WRITE_OK="$4" MOVES=$5 MOVE_CHAIN=1 FLAG_OBL=Arm.flagObl DATA=$6 LOOP=$7 \
    python3 gen_plan_proof.py scalar_x1 ScalarX1 1 0 > plans/gen_scalar_x1_$1.log 2>&1
  echo "$2: $(grep 'control words' plans/gen_scalar_x1_$1.log | cut -c1-160)"
  grep 'move paths' plans/gen_scalar_x1_$1.log | cut -c1-300 || true
}
gen body GenSB 287 "fun p => (p.1 == 3) || (p.1 == 2 && decide (0 ≤ p.2) && decide (p.2 < 4))" "258:258" "" 1
gen e1 GenSE1 "$(ctl0 plans/gen_scalar_x1_body.log)" "fun p => p.1 == 3" "258:258" 0 ""
gen ex GenSX "" "fun _ => false" "" 0 ""
if [ "$1" = build ]; then
  P=${2:-4}
  for g in GenSE1 GenSX GenSB; do
    ./build_plan.sh ScalarX1 $g "$(ls Keccaktree/Kernels/ScalarX1/$g/Slice*.lean | wc -l)" "$P"
    lake build Keccaktree.Kernels.ScalarX1.$g.Seg 2>&1 | grep -E "error|Built Keccaktree.Kernels.ScalarX1.$g.Seg"
  done
fi
