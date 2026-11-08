#!/bin/bash
# The RISC-V differential tests only (VLEN 128/256/512 under qemu): run_rv.sh <work dir> <seed> [states per
# kernel instruction] [instances per template].  KOBJ: the assembled RISC-V kernel objects.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN=$(dirname "$HERE")
WD=$1; SEED=$2; NS=${3:-2}; NT=${4:-40}
KOBJ=${KOBJ:-/root/kt-diff/kobj}
mkdir -p "$WD" "$LEAN/Tools/DiffCases"
for o in $KOBJ/keccak256_{rv64,zbb,rvv}*.o; do riscv64-linux-gnu-objdump -d -r --no-show-raw-insn $o; done > "$WD/rv.dis"
for v in 128 256 512; do
  python3 "$HERE/rvgen.py" "$WD/rv.dis" "$WD" "$SEED" $v "$NS" "$NT"
  D=$WD/rv$v
  riscv64-linux-gnu-gcc -c "$D/cases.S" -o "$D/cases.o"; riscv64-linux-gnu-gcc -c "$D/table.S" -o "$D/table.o"
  python3 "$HERE/mkcases.py" riscv "$D/cases.o" Rv$v "$LEAN/Tools/DiffCases/Rv$v.lean" "$D/instrs.json"
  riscv64-linux-gnu-gcc -O1 -static -mno-relax -Wl,--no-relax "$HERE/harness.c" "$HERE/tramp_rv.S" "$D/cases.o" "$D/table.o" -o "$D/harness"
done
cd "$HERE" && python3 mkall.py rv128=Rv128:riscv rv256=Rv256:riscv rv512=Rv512:riscv
cd "$LEAN" && lake build difftool 2>&1 | tail -2
T=$LEAN/.lake/build/bin/difftool
for v in 128 256 512; do
  ( qemu-riscv64 -cpu rv64,v=true,vlen=$v,zvkb=true,zbb=true "$WD/rv$v/harness" < "$WD/rv$v/states.txt" > "$WD/rv$v/hw.txt" ) &
  ( $T rv$v $((v / 64)) < "$WD/rv$v/states.txt" > "$WD/rv$v/model.txt" ) &
done
wait
for v in 128 256 512; do python3 "$HERE/compare.py" riscv "$WD/rv$v" $((v / 64)) 32; done
echo ALL DONE
