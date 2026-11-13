#!/bin/bash
# kt-int build queue v3 (memory-gated): kt-int-queue3.sh <queuefile> <log>; lines as kt-int-queue2.sh:
#   gen <Ns> <P> <Gen...> | mod <Module...> | stopifdisk <GB> | axioms <Name> | prune_if_ok <Name> <N> <Ns...>
# every lean process (slice, module) starts only after /root/kt-int-gate.sh (MemAvailable >= 15 GB, kt-int RSS <= 20 GB)
export PATH=/root/.elan/bin:$PATH
cd /root/kt-int/lean
Q=$1; L=$2; n=0; G=/root/kt-int-gate.sh
echo "== queue start $Q $(date +%F\ %T)" >> $L
while true; do
  n=$((n+1)); line=$(sed -n "${n}p" $Q); [ -z "$line" ] && break
  set -- $line; cmd=$1; shift
  echo "== [$n] $line  $(date +%T) free=$(df -BG --output=avail / | tail -1)" >> $L
  case $cmd in
    gen) ns=$1; P=$2; shift 2
         for g in "$@"; do
           echo "== $ns/$g $(date +%T) P=$P" >> $L
           $G; lake build Keccaktree.Kernels.$ns.$g.Invs 2>&1 | grep -E "^error" | head -5 >> $L
           k=$(ls Keccaktree/Kernels/$ns/$g/Slice*.lean | wc -l)
           for i in $(seq 0 $((k-1))); do
             while [ $(jobs -rp | wc -l) -ge $P ]; do sleep 10; done
             $G
             ( lake build Keccaktree.Kernels.$ns.$g.Slice$i 2>&1 | grep -E "^error" | head -5 | sed "s/^/Slice$i: /" >> $L ) &
             sleep 30
           done
           wait
           $G; lake build Keccaktree.Kernels.$ns.$g.Seg 2>&1 | grep -E "^error|Built Keccaktree.Kernels.$ns.$g.Seg|Build completed" | cut -c1-300 >> $L
         done;;
    mod) $G; lake build "$@" > /root/kt-int-logs/mod_$(basename $Q)_$n.log 2>&1; rc=$?
         grep -E "^error" -A5 /root/kt-int-logs/mod_$(basename $Q)_$n.log | head -60 >> $L; tail -n 1 /root/kt-int-logs/mod_$(basename $Q)_$n.log >> $L; echo "rc=$rc" >> $L;;
    axioms) $G; lake env lean /root/kt-int/axioms/$1.lean > /root/kt-int/axioms/out_$1.txt 2>&1; echo "axioms $1 rc=$? lines=$(grep -c "depends on axioms" /root/kt-int/axioms/out_$1.txt) sorry=$(grep -c sorryAx /root/kt-int/axioms/out_$1.txt) err=$(grep -c error /root/kt-int/axioms/out_$1.txt)" >> $L;;
    prune_if_ok) a=/root/kt-int/axioms/out_$1.txt; want=$2; shift 2
         if [ "$(grep -c "depends on axioms" $a)" = "$want" ] && ! grep -q sorryAx $a && ! grep -q error $a; then
           for ns in "$@"; do rm -rf .lake/build/lib/lean/Keccaktree/Kernels/$ns/Gen* .lake/build/ir/Keccaktree/Kernels/$ns/Gen*; done
           echo "pruned Gen oleans of $* free=$(df -BG --output=avail / | tail -1)" >> $L
         else echo "STOP: axioms $a not clean/complete" >> $L; break; fi;;
    stopifdisk) a=$(df -BG --output=avail / | tail -1 | tr -dc 0-9); [ "$a" -lt "$1" ] && { echo "STOP: free ${a}G < $1G" >> $L; break; };;
  esac
done
echo "== queue end $(date +%F\ %T)" >> $L
