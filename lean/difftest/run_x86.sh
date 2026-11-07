#!/bin/bash
# Differential tests, x86-64: generate, translate, build harness + difftool, run, compare.
#   run_x86.sh <work dir> <seed> [states_per_instr] [per_template]
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN=$(dirname "$HERE")
WD=$1; SEED=$2; NS=${3:-2}; NT=${4:-40}
SDE=${SDE:-/root/kt-diff/sde-external-9.48.0-2024-11-25-lin/sde64}
mkdir -p "$WD"
objdump -d -r --no-show-raw-insn -M intel ${KOBJ:-/root/kt-diff/kobj}/keccak256_{x86,avx}*.o > "$WD/kernels.dis"
python3 "$HERE/x86gen.py" "$WD/kernels.dis" "$WD" "$SEED" "$NS" "$NT"
for set in avx2 avx512; do
  D=$WD/$set
  gcc -c "$D/cases.S" -o "$D/cases.o"
  gcc -c "$D/table.S" -o "$D/table.o"
  if [ $set = avx2 ]; then M=X86Avx2; DEF=; else M=X86Avx512; DEF=-DAVX512; fi
  python3 "$HERE/mkcases.py" x86 "$D/cases.o" $M "$LEAN/Tools/DiffCases/$M.lean" "$D/instrs.json"
  gcc -O1 -no-pie $DEF "$HERE/harness.c" "$HERE/tramp_x86.S" "$D/cases.o" "$D/table.o" -o "$D/harness"
done
cd "$HERE" && python3 mkall.py ${EXTRA_SETS} x86-avx2=X86Avx2:x86 x86-avx512=X86Avx512:x86
cd "$LEAN" && systemd-run --scope -q -p MemoryMax=10G lake build difftool 2>&1 | tail -3
"$WD/avx2/harness" < "$WD/avx2/states.txt" > "$WD/avx2/hw.txt"
"$SDE" -spr -- "$WD/avx512/harness" < "$WD/avx512/states.txt" > "$WD/avx512/hw.txt"
for set in avx2 avx512; do
  "$LEAN/.lake/build/bin/difftool" x86-$set < "$WD/$set/states.txt" > "$WD/$set/model.txt"
done
python3 "$HERE/compare.py" x86 "$WD/avx2" 4 16
python3 "$HERE/compare.py" x86 "$WD/avx512" 8 32
