#!/bin/bash
# All differential tests: x86-64 (native + SDE), AArch64 (qemu), RISC-V VLEN 128/256/512 (qemu).
#   run_all.sh <work dir> <seed> [states per kernel instruction] [instances per template]
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN=$(dirname "$HERE")
WD=$1; SEED=$2; NS=${3:-2}; NT=${4:-40}
KOBJ=${KOBJ:-/root/kt-diff/kobj}
SDE=${SDE:-/root/kt-diff/sde-external-9.48.0-2024-11-25-lin/sde64}
mkdir -p "$WD"
# --- generate, assemble, translate
for o in $KOBJ/keccak256_{x86,avx}*.o; do objdump -d -r --no-show-raw-insn -M intel $o; done > "$WD/x86.dis"
python3 "$HERE/x86gen.py" "$WD/x86.dis" "$WD" "$SEED" "$NS" "$NT"
for set in avx2 avx512; do
  D=$WD/$set
  if [ $set = avx2 ]; then M=X86Avx2; DEF=; else M=X86Avx512; DEF=-DAVX512; fi
  gcc -c "$D/cases.S" -o "$D/cases.o"; gcc -c "$D/table.S" -o "$D/table.o"
  python3 "$HERE/mkcases.py" x86 "$D/cases.o" $M "$LEAN/Tools/DiffCases/$M.lean" "$D/instrs.json"
  gcc -O1 -no-pie $DEF "$HERE/harness.c" "$HERE/tramp_x86.S" "$D/cases.o" "$D/table.o" -o "$D/harness"
done
for o in $KOBJ/keccak256_{neon,sha3,scalar}*.o; do aarch64-linux-gnu-objdump -d -r --no-show-raw-insn $o; done > "$WD/arm.dis"
python3 "$HERE/armgen.py" "$WD/arm.dis" "$WD" "$SEED" "$NS" "$NT"
D=$WD/arm
aarch64-linux-gnu-gcc -c "$D/cases.S" -o "$D/cases.o"; aarch64-linux-gnu-gcc -c "$D/table.S" -o "$D/table.o"
python3 "$HERE/mkcases.py" arm "$D/cases.o" Arm "$LEAN/Tools/DiffCases/Arm.lean" "$D/instrs.json"
aarch64-linux-gnu-gcc -O1 -static "$HERE/harness.c" "$HERE/tramp_arm.S" "$D/cases.o" "$D/table.o" -o "$D/harness"
# one objdump per object: objdump keeps the first object's ISA subset for the following ones
for o in $KOBJ/keccak256_{rv64,zbb,rvv}*.o; do riscv64-linux-gnu-objdump -d -r --no-show-raw-insn $o; done > "$WD/rv.dis"
for v in 128 256 512; do
  python3 "$HERE/rvgen.py" "$WD/rv.dis" "$WD" "$SEED" $v "$NS" "$NT"
  D=$WD/rv$v
  riscv64-linux-gnu-gcc -c "$D/cases.S" -o "$D/cases.o"; riscv64-linux-gnu-gcc -c "$D/table.S" -o "$D/table.o"
  python3 "$HERE/mkcases.py" riscv "$D/cases.o" Rv$v "$LEAN/Tools/DiffCases/Rv$v.lean" "$D/instrs.json"
  riscv64-linux-gnu-gcc -O1 -static -mno-relax -Wl,--no-relax "$HERE/harness.c" "$HERE/tramp_rv.S" "$D/cases.o" "$D/table.o" -o "$D/harness"
done
cd "$HERE" && python3 mkall.py x86-avx2=X86Avx2:x86 x86-avx512=X86Avx512:x86 arm=Arm:arm \
  rv128=Rv128:riscv rv256=Rv256:riscv rv512=Rv512:riscv
cd "$LEAN" && systemd-run --scope -q -p MemoryMax=10G lake build difftool 2>&1 | tail -2
# --- run: hardware / emulators and the model, in parallel
T=$LEAN/.lake/build/bin/difftool
( "$WD/avx2/harness" < "$WD/avx2/states.txt" > "$WD/avx2/hw.txt" ) &
( "$SDE" -spr -- "$WD/avx512/harness" < "$WD/avx512/states.txt" > "$WD/avx512/hw.txt" ) &
( qemu-aarch64 -cpu max "$WD/arm/harness" < "$WD/arm/states.txt" > "$WD/arm/hw.txt" ) &
for v in 128 256 512; do
  ( qemu-riscv64 -cpu rv64,v=true,vlen=$v,zvkb=true,zbb=true "$WD/rv$v/harness" < "$WD/rv$v/states.txt" > "$WD/rv$v/hw.txt" ) &
done
( $T x86-avx2 < "$WD/avx2/states.txt" > "$WD/avx2/model.txt" ) &
( $T x86-avx512 < "$WD/avx512/states.txt" > "$WD/avx512/model.txt" ) &
( $T arm < "$WD/arm/states.txt" > "$WD/arm/model.txt" ) &
for v in 128 256 512; do ( $T rv$v $((v / 64)) < "$WD/rv$v/states.txt" > "$WD/rv$v/model.txt" ) & done
wait
python3 "$HERE/compare.py" x86 "$WD/avx2" 4 16
python3 "$HERE/compare.py" x86 "$WD/avx512" 8 32
python3 "$HERE/compare.py" arm "$WD/arm" 2 32
for v in 128 256 512; do python3 "$HERE/compare.py" riscv "$WD/rv$v" $((v / 64)) 32; done
echo ALL DONE
