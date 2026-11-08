#!/bin/bash
# Build generated segment modules: build_seg.sh <KernelDir> <P> <Gen>...   (run it inside a memory-capped scope)
cd "$(dirname "$0")"
d=$1; P=$2; shift 2
LAKE=${LAKE:-/root/.elan/bin/lake}
# P=auto: per segment, P = min(KX_MAX, (budget (file KX_BUDGET_FILE, else KX_BUDGET) - resident GB of this agent (KX_MEM script)) / KX_PER), at least 1
P0=$P
for g in "$@"; do
  if [ "$P0" = auto ]; then
    while :; do
      budget=$(cat "${KX_BUDGET_FILE:-/root/kx-budget}" 2>/dev/null || echo "${KX_BUDGET:-45}")
      mine=$(${KX_MEM:-/root/kx-mem.sh}); P=$(( (budget - mine) / ${KX_PER:-5} )); [ $P -gt ${KX_MAX:-6} ] && P=${KX_MAX:-6}
      [ $P -ge 1 ] && break; sleep 60
    done
  fi
  K=$(ls Keccaktree/Kernels/$d/$g/Slice*.lean | wc -l)
  echo "== $d/$g $(date +%H:%M:%S) slices=$K P=$P"
  $LAKE build "Keccaktree.Kernels.$d.$g.Invs" 2>&1 | grep -E "^error|Build completed" | cut -c1-300
  seq 0 $((K-1)) | xargs -P "$P" -I{} bash -c "$LAKE build Keccaktree.Kernels.$d.$g.Slice{} 2>&1 | grep -E '^error|Built Keccaktree.Kernels.$d.$g.Slice{} ' | cut -c1-300"
  $LAKE build "Keccaktree.Kernels.$d.$g.Seg" 2>&1 | grep -E "^error|Build completed" | cut -c1-300
  echo "== $d/$g done $(date +%H:%M:%S)"
done
