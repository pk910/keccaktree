#!/bin/bash
# Build a kernel's generated proofs with at most P lean processes (lake has no job limit; the
# 3- and 8-node kernels need several GB per slice).   Usage: build_bounded.sh <Ns> [P]
cd "$(dirname "$0")"
ns=$1; P=${2:-6}
echo "== $ns $(date +%H:%M:%S) P=$P"
lake build "Keccaktree.Kernels.$ns.Gen.Invs" 2>&1 | grep -E "error|Build completed" | cut -c1-200
seq 0 23 | xargs -P "$P" -I{} bash -c "lake build Keccaktree.Kernels.$ns.Gen.Slice{} 2>&1 | grep -E 'error|Built Keccaktree.Kernels.$ns.Gen.Slice{} ' | cut -c1-200"
lake build "Keccaktree.Kernels.$ns.Gen.Final" 2>&1 | grep -E "error|Build completed|Built Keccaktree.Kernels.$ns.Gen.(Batch|Final)" | cut -c1-200
echo "== $ns done $(date +%H:%M:%S)"
