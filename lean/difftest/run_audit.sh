#!/bin/bash
# Aligned-move audit: every vmovdqa/vmovdqa64 the x86 kernel models execute (counts 0 .. 64 + 2 NODES)
# addresses the stack frame (or 32-byte aligned constants).
set -e
HERE=$(cd "$(dirname "$0")" && pwd); LEAN=$(dirname "$HERE")
python3 "$HERE/alignidx.py" ${KOBJ:-/root/kt-diff/kobj}
cd "$LEAN" && systemd-run --scope -q -p MemoryMax=10G lake build alignaudit 2>&1 | tail -2
"$LEAN/.lake/build/bin/alignaudit"
