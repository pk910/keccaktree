#!/bin/bash
# Build generated segments: build_segs.sh <Ns> <P> <Gen...>  (Invs, the slices P at a time, Batch, Seg)
cd "$(dirname "$0")"
ns=$1; P=$2; shift 2
for g in "$@"; do
  ./build_plan.sh $ns $g "$(ls Keccaktree/Kernels/$ns/$g/Slice*.lean | wc -l)" "$P"
  lake build Keccaktree.Kernels.$ns.$g.Seg 2>&1 | grep -E "error|Built Keccaktree.Kernels.$ns.$g.Seg" | cut -c1-200
done
echo "segments done $(date +%H:%M:%S)"
