#!/bin/bash
# Differential tests, AArch64 (qemu-aarch64 -cpu max).   run_arm.sh <work dir> <seed> [states] [per_template]
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN=$(dirname "$HERE")
WD=$1; SEED=$2; NS=${3:-2}; NT=${4:-40}
mkdir -p "$WD"
aarch64-linux-gnu-objdump -d -r --no-show-raw-insn ${KOBJ:-/root/kt-diff/kobj}/keccak256_{neon,sha3,scalar}*.o > "$WD/kernels.dis"
python3 "$HERE/armgen.py" "$WD/kernels.dis" "$WD" "$SEED" "$NS" "$NT"
D=$WD/arm
aarch64-linux-gnu-gcc -c "$D/cases.S" -o "$D/cases.o"
aarch64-linux-gnu-gcc -c "$D/table.S" -o "$D/table.o"
python3 "$HERE/mkcases.py" arm "$D/cases.o" Arm "$LEAN/Tools/DiffCases/Arm.lean" "$D/instrs.json"
aarch64-linux-gnu-gcc -O1 -static "$HERE/harness.c" "$HERE/tramp_arm.S" "$D/cases.o" "$D/table.o" -o "$D/harness"
if [ -z "$NOBUILD" ]; then
  cd "$HERE" && python3 mkall.py ${SETS:-arm=Arm:arm}
  cd "$LEAN" && systemd-run --scope -q -p MemoryMax=10G lake build difftool 2>&1 | tail -3
fi
qemu-aarch64 -cpu max "$D/harness" < "$D/states.txt" > "$D/hw.txt"
"$LEAN/.lake/build/bin/difftool" arm < "$D/states.txt" > "$D/model.txt"
python3 "$HERE/compare.py" arm "$D" 2 32
