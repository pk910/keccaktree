#!/bin/bash
# Generate (and optionally build) the four segments of x86_x1's all-count theorem
# (Keccaktree/Kernels/X86X1/All.lean):
#   GenSE1  steps [0,7)      entry: pushes, frame          (keeps rdx)
#   GenSE3  steps [9,13)     spills of rdi/rsi/rdx, r15    (rdx -> count word [rsp+424])
#   GenSB   steps [13,4280)  loop body, one node, 25 slices, end cut = start cut (LOOP=1)
#   GenSX   steps [4282,4289) epilogue (add rsp, pops)
# The count-dependent instructions (test/je at 7/8, dec/jne at 600/601, ret at 609) are the
# concrete lemmas of Asm/X86Steps.lean.  Usage: gen_segments_x86_x1.sh [build P]
set -e
cd "$(dirname "$0")"
mkdir -p plans
python3 find_plan.py x86_x1 1 0 > plans/x86_x1_c1.json
python3 - <<'PY'
import json
p = json.load(open("plans/x86_x1_c1.json"))
cuts = [t for t in p["cuts"] if 13 < t + 1 < 4280]
body = {"kernel": "x86_x1", "count": 1, "lanes": 0, "entry": 13, "end": 4280, "cuts": cuts,
        "rounds": [[0]] + [[min(i + 1, 24)] for i in range(len(cuts))] + [[24]]}
json.dump(body, open("plans/x86_x1_body.json", "w"))
for name, a, b, r in (("e1", 0, 7, 0), ("e3", 9, 13, 0), ("ex", 4282, 4289, 24)):
    json.dump({"kernel": "x86_x1", "count": 1, "lanes": 0, "entry": a, "end": b, "cuts": [], "rounds": [[r], [r]]},
              open(f"plans/x86_x1_{name}.json", "w"))
PY
ctl0() { python3 -c "
import sys, ast
l = [l for l in open(sys.argv[1]).read().splitlines() if l.startswith('control words')][0]
print(','.join(str(x) for x in ast.literal_eval(l.split(':', 1)[1].strip())[0]))" "$1"; }
gen() { # name gendir end_ctl write_ok moves data loop
  rm -rf Keccaktree/Kernels/X86X1/$2
  PLAN=plans/x86_x1_$1.json OUTDIR=Keccaktree/Kernels/X86X1/$2 GEN=$2 NS=X86X1.$2 PROG_NS=X86X1 ISA=X86 BATCH=1 SEG=1 \
    END_CTL=$3 FORBID_CTL=258,2097315 WRITE_OK="$4" MOVES=$5 DATA=$6 LOOP=$7 \
    python3 gen_plan_proof.py x86_x1 X86X1 1 0 > plans/gen_x86_x1_$1.log 2>&1
  echo "$2: $(grep 'control words' plans/gen_x86_x1_$1.log | cut -c1-120)"
}
gen body GenSB 260 "fun p => (p.1 == 3 && p.2 != 131064) || (p.1 == 2 && decide (0 ≤ p.2) && decide (p.2 < 4))" "" "" 1
gen e3 GenSE3 "$(ctl0 plans/gen_x86_x1_body.log)" "fun p => p.1 == 3" "2097315:258" 0 ""
gen e1 GenSE1 "$(ctl0 plans/gen_x86_x1_e3.log)" "fun p => p.1 == 3 && p.2 != 131064" "258:258" 0 ""
gen ex GenSX "" "fun _ => false" "" 0 ""
if [ "$1" = build ]; then
  P=${2:-4}
  for g in GenSE1 GenSE3 GenSX GenSB; do
    ./build_plan.sh X86X1 $g "$(ls Keccaktree/Kernels/X86X1/$g/Slice*.lean | wc -l)" "$P"
    lake build Keccaktree.Kernels.X86X1.$g.Seg 2>&1 | grep -E "error|Built Keccaktree.Kernels.X86X1.$g.Seg"
  done
  lake build Keccaktree.Kernels.X86X1.All
fi
