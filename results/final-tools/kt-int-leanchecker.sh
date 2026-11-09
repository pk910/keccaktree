#!/bin/bash
# leanchecker (Lean 4.35.0 toolchain, `leanchecker <Module>`: replays the module's declarations through the
# kernel in the environment of its imports) over every Keccaktree module of the final tree, one module per
# process, at most P at a time, each launch memory-gated; resumable (skips modules already logged ok).
# Usage: kt-int-leanchecker.sh <module list> [P]   Log: /root/kt-int-logs/leanchecker.tsv  (module, rc, s, maxKB)
export PATH=/root/.elan/bin:$PATH
cd /root/kt-int/lean; LIST=$1; P=${2:-2}; T=/root/kt-int-logs/leanchecker.tsv; touch $T
# leanchecker finds its target oleans by walking the search path, which does not follow the symlinks of the
# offloaded olean trees (Kernels/<d> -> /mnt/kt-store/...): bind-mount them under /root/kt-lcroot, appended
# LAST to LEAN_PATH (imports still resolve through the main build dir; only the target lookup uses it)
R=/root/kt-lcroot/Keccaktree/Kernels
for l in .lake/build/lib/lean/Keccaktree/Kernels/*; do
  [ -L "$l" ] || continue; d=$(basename $l); mkdir -p $R/$d
  mountpoint -q $R/$d || mount --bind "$(readlink -f $l)" $R/$d
done
export LEAN_PATH="$(lake env printenv LEAN_PATH):/root/kt-lcroot"
run1() {
  m=$1; T=/root/kt-int-logs/leanchecker.tsv
  grep -q "^$m	0	" $T && return 0
  /root/kt-int-gate.sh
  s=$(date +%s.%N)
  f=/tmp/kt-int-lc.$$.t
  /usr/bin/time -f "%M" -o $f leanchecker $m > /root/kt-int-logs/lc_out.$m.txt 2>&1; rc=$?
  e=$(date +%s.%N); kb=$(tail -1 $f 2>/dev/null); rm -f $f
  printf "%s\t%s\t%.1f\t%s\n" $m $rc $(awk "BEGIN{print $e - $s}") "$kb" >> $T
  [ $rc = 0 ] && rm -f /root/kt-int-logs/lc_out.$m.txt
}
export -f run1
xargs -a $LIST -P $P -I{} bash -c 'run1 {}'
for d in $R/*; do mountpoint -q $d && umount $d; done
echo "done: $(awk -F'\t' '$2==0' $T | wc -l) ok, $(awk -F'\t' '$2!=0' $T | wc -l) failed of $(wc -l < $LIST)"
