#!/bin/bash
# Final leanchecker pass (after the scheduler): every module of lc_modules.txt not yet ok in leanchecker.tsv,
#  (a) leanchecker ALONE, in its own cgroup scope with MemoryMax=100G (row appended to leanchecker.tsv);
#  (b) modules that (a) OOM-kills: `lake env lean <file>` (re-elaboration from source) in a MemoryMax=60G scope,
#      rows in elab.tsv (module, rc, wall s, peak KB), their leanchecker peak at the kill in leanchecker_oom.tsv.
# A leanchecker rejection (rc != 0 and not an OOM kill) stops everything (lcfinal.log).
export PATH=/root/.elan/bin:$PATH
cd /root/kt-int/lean
LG=/root/kt-int-logs; T=$LG/leanchecker.tsv; E=$LG/elab.tsv; O=$LG/leanchecker_oom.tsv; L=$LG/lcfinal.log
while systemctl is-active -q kt-int-lc; do sleep 30; done
echo "== $(date +%F\ %T) final pass start" >> $L
R=/root/kt-lcroot/Keccaktree/Kernels
for l in .lake/build/lib/lean/Keccaktree/Kernels/*; do
  [ -L "$l" ] || continue; d=$(basename $l); mkdir -p $R/$d
  mountpoint -q $R/$d || mount --bind "$(readlink -f $l)" $R/$d
done
LP="$(lake env printenv LEAN_PATH):/root/kt-lcroot"
awk -F'\t' '$2==0{print $1}' $T | sort -u > /tmp/kt-int-ok.txt
grep -v -x -F -f /tmp/kt-int-ok.txt $LG/lc_modules.txt > $LG/lcfinal_todo.txt
echo "todo: $(wc -l < $LG/lcfinal_todo.txt) modules" >> $L
: > $LG/lcfinal_oom.txt
while read m; do
  s=$(date +%s.%N)
  systemd-run --scope -q -p MemoryMax=100G -p MemorySwapMax=0 env LEAN_PATH="$LP" /usr/bin/time -f "%M" -o /tmp/kt-int-lcf.t \
    leanchecker $m > $LG/lc_out.$m.txt 2>&1; rc=$?
  w=$(awk "BEGIN{print $(date +%s.%N) - $s}"); kb=$(tail -1 /tmp/kt-int-lcf.t 2>/dev/null)
  printf "%s\t%s\t%.1f\t%s\n" $m $rc $w "$kb" >> $T
  if [ $rc = 0 ]; then rm -f $LG/lc_out.$m.txt; echo "(a) ok $m ${w}s ${kb}KB" >> $L
  elif [ $rc -ge 128 ] || grep -qiE "out of memory|Killed" $LG/lc_out.$m.txt; then
    echo "$m" >> $LG/lcfinal_oom.txt; printf "%s\t%s\t%s\n" $m $rc "$kb" >> $O; echo "(a) OOM $m rc=$rc ${kb}KB" >> $L
  else echo "REJECTION (a) $m rc=$rc: $(head -c 500 $LG/lc_out.$m.txt)" >> $L; exit 1; fi
done < $LG/lcfinal_todo.txt
for d in $R/*; do mountpoint -q $d && umount $d; done
echo "== $(date +%F\ %T) (a) done; (b) for $(wc -l < $LG/lcfinal_oom.txt) modules" >> $L
while read m; do
  f=$(echo $m | tr . /).lean
  systemd-run --scope -q -p MemoryMax=60G -p MemorySwapMax=0 /usr/bin/time -f "%e %M %x" -o /tmp/kt-int-el.t \
    lake env lean $f > $LG/elab_out.$m.txt 2>&1; rc=$?
  read w kb x < /tmp/kt-int-el.t
  printf "%s\t%s\t%s\t%s\n" $m $rc $w $kb >> $E
  if [ $rc = 0 ] && ! grep -q "error" $LG/elab_out.$m.txt; then echo "(b) ok $m ${w}s ${kb}KB" >> $L; rm -f $LG/elab_out.$m.txt
  else echo "(b) FAILED $m rc=$rc: $(grep -m3 error $LG/elab_out.$m.txt)" >> $L; fi
done < $LG/lcfinal_oom.txt
echo "== $(date +%F\ %T) final pass end" >> $L
