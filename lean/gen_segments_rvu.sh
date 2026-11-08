#!/bin/bash
# Segments of a 1-node RISC-V scalar kernel's all-count theorem for any buffer alignment
# (Keccaktree/Kernels/<Ns>/AllU.lean; step positions of the count-1 runs, position 0 = the entry `bnez`):
#   GenSE  [1, 18)        frame stores; a0/a1/a2 spilled (moves), control: sp only
#   GenSI  [23, 31)       aligned input: the 8 loads of LOAD_STATE from the input node (t0 = the input pointer)
#   GenSJ  [410, 418)     misaligned input (run with the input at byte 1): the 8 loads from the bounce buffer
#   GenSC  [31, core_end) the constant lanes and the 24 rounds, registers to registers (spills only)
#   GenSX  [sx_a, sx_b)   the restores
# The loop head, the byte copies, the digest stores and the back edge are concrete steps (AllU.lean).
# No segment has a pointer or count spill as a control word (FORBID_CTL): they do not depend on the
# misalignment or the count.
# Usage: gen_segments_rvu.sh <kernel> <Ns> <core_end> <sx_start> <sx_end>
#   rv64_x1 Rv64X1 5377 5391 5405;  zbb_x1 ZbbX1 3446 3460 3474
set -e
cd "$(dirname "$0")"
k=$1; ns=$2; CE=$3; SX_A=$4; SX_B=$5
CNTV=2097155; INV=2097139; OUTV=2097123
mkdir -p plans
python3 find_plan.py $k 1 0 > plans/${k}_c1.json
K=$k CE=$CE SX_A=$SX_A SX_B=$SX_B python3 - <<'PY'
import json, os
k = os.environ['K']; ce, xa, xb = (int(os.environ[v]) for v in ('CE', 'SX_A', 'SX_B'))
p = json.load(open(f"plans/{k}_c1.json"))
cuts = [t for t in p["cuts"] if 31 < t + 1 < ce]
core = {"kernel": k, "count": 1, "lanes": 0, "entry": 31, "end": ce, "cuts": cuts,
        "rounds": [[0]] + [[min(i + 1, 24)] for i in range(len(cuts))] + [[24]]}
json.dump(core, open(f"plans/{k}_core.json", "w"))
for name, a, b, r in (("e", 1, 18, 0), ("in", 23, 31, 0), ("buf", 410, 418, 0), ("ex", xa, xb, 24)):
    json.dump({"kernel": k, "count": 1, "lanes": 0, "entry": a, "end": b, "cuts": [], "rounds": [[r], [r]]},
              open(f"plans/{k}_{name}.json", "w"))
PY
ctl0() { python3 -c "
import sys, ast
l = [l for l in open(sys.argv[1]).read().splitlines() if l.startswith('control words')][0]
print(','.join(str(x) for x in ast.literal_eval(l.split(':', 1)[1].strip())[0]))" "$1"; }
gen() { # name gendir end_ctl write_ok moves data inv0 invk mis
  rm -rf Keccaktree/Kernels/$ns/$2
  KT_MIS=$9 PLAN=plans/${k}_$1.json OUTDIR=Keccaktree/Kernels/$ns/$2 GEN=$2 NS=$ns.$2 PROG_NS=$ns ISA=Riscv \
    ISA_EXPR="(Riscv.isa 2)" BATCH=1 SEG=1 END_CTL=$3 FORBID_CTL=266,267,268,$CNTV,$INV,$OUTV WRITE_OK="$4" \
    MOVES=$5 DATA=$6 INV0=$7 INVK=$8 python3 gen_plan_proof.py $k $ns 1 0 > plans/gen_${k}_$1.log 2>&1
  echo "$2: $(grep 'control words' plans/gen_${k}_$1.log | cut -c1-160)"
}
gen core GenSC 258 "fun p => p.1 == 3 && decide (131055 ≤ p.2) && decide (p.2 ≤ 131058)" "" "" regs regs ""
C0=$(ctl0 plans/gen_${k}_core.log)
gen in GenSI "$C0" "fun _ => false" "" "" input regs ""
gen buf GenSJ "$C0" "fun _ => false" "" "" mem3 regs "1,0"
gen e GenSE 258 "fun p => p.1 == 3" "$CNTV:268,$INV:267,$OUTV:266" 0 input out ""
gen ex GenSX "" "fun _ => false" "" 0 input out ""
