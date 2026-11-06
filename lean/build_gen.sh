#!/bin/bash
# Compile the generated proofs of the given kernel namespaces (all slices, Batch, Final) with lake.
# Usage: build_gen.sh Ns1 Ns2 ...      e.g. build_gen.sh Avx2X4 ScalarX1   (lake parallelises the modules itself)
cd "$(dirname "$0")"
for ns in "$@"; do
  echo "== $ns $(date +%H:%M:%S)"
  lake build "Keccaktree.Kernels.$ns.Gen.Final" 2>&1 | grep -v "^trace" | grep -E "error|Built Keccaktree.Kernels.$ns.Gen|Build completed" | cut -c1-200
done
