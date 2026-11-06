#!/bin/bash
# Compile the generated proofs of the given kernel namespaces (all slices, Batch, Final) with lake.
# Usage: build_gen.sh [-j N] Ns1 Ns2 ...      e.g. build_gen.sh -j 4 Avx2X4 ScalarX1
cd "$(dirname "$0")"
J=4
if [ "$1" = "-j" ]; then J=$2; shift 2; fi
for ns in "$@"; do
  echo "== $ns $(date +%H:%M:%S)"
  lake build -j "$J" "Keccaktree.Kernels.$ns.Gen.Final" 2>&1 | grep -v "^trace" | grep -E "error|Built Keccaktree.Kernels.$ns.Gen|Build completed" | cut -c1-200
done
