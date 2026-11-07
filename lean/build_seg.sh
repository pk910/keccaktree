#!/bin/bash
# Build generated segment modules: build_seg.sh <KernelDir> <P> <Gen>...   (run it inside a memory-capped scope)
cd "$(dirname "$0")"
d=$1; P=$2; shift 2
LAKE=${LAKE:-/root/.elan/bin/lake}
for g in "$@"; do
  K=$(ls Keccaktree/Kernels/$d/$g/Slice*.lean | wc -l)
  echo "== $d/$g $(date +%H:%M:%S) slices=$K P=$P"
  $LAKE build "Keccaktree.Kernels.$d.$g.Invs" 2>&1 | grep -E "^error|Build completed" | cut -c1-300
  seq 0 $((K-1)) | xargs -P "$P" -I{} bash -c "$LAKE build Keccaktree.Kernels.$d.$g.Slice{} 2>&1 | grep -E '^error|Built Keccaktree.Kernels.$d.$g.Slice{} ' | cut -c1-300"
  $LAKE build "Keccaktree.Kernels.$d.$g.Seg" 2>&1 | grep -E "^error|Build completed" | cut -c1-300
  echo "== $d/$g done $(date +%H:%M:%S)"
done
