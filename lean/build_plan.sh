#!/bin/bash
# Build the generated proofs of a plan: build_plan.sh <KernelDir> <GenDir> <K slices> [P]
cd "$(dirname "$0")"
d=$1; g=$2; K=$3; P=${4:-4}
echo "== $d/$g $(date +%H:%M:%S) P=$P"
lake build "Keccaktree.Kernels.$d.$g.Invs" 2>&1 | grep -E "error|Build completed" | cut -c1-200
seq 0 $((K-1)) | xargs -P "$P" -I{} bash -c "lake build Keccaktree.Kernels.$d.$g.Slice{} 2>&1 | grep -E 'error|Built Keccaktree.Kernels.$d.$g.Slice{} ' | cut -c1-200"
lake build "Keccaktree.Kernels.$d.$g.Final" 2>&1 | grep -E "error|Build completed|Built Keccaktree.Kernels.$d.$g.(Batch|Final)" | cut -c1-200
echo "== $d/$g done $(date +%H:%M:%S)"
