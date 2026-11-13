#!/bin/bash
# kt-int-linkx86.sh <src lean> <tag> <Ns...>: copy Gen sources, closure check of <Ns>.Lib (+LibV), hard-link the
# modules not yet built in kt-int, placeholder .c where a recorded .c is missing, lake build --no-build over the closure
export PATH=/root/.elan/bin:$PATH
S=$1; tag=$2; shift 2; D=/root/kt-int/lean; L=/root/kt-int-logs/link_$tag.log
roots=""
for ns in "$@"; do
  rm -rf $D/Keccaktree/Kernels/$ns/Gen*
  cp -a $S/Keccaktree/Kernels/$ns/Gen* $D/Keccaktree/Kernels/$ns/
  for r in Lib LibV; do [ -f $D/Keccaktree/Kernels/$ns/$r.lean ] && roots="$roots Keccaktree.Kernels.$ns.$r"; done
done
echo "== $(date +%T) roots:$roots" > $L
OUT=/root/kt-int-logs/closure_$tag.txt python3 /root/kt-int-closure.py $D $S $roots >> $L 2>&1 || { echo "STOP: closure not reusable" >> $L; exit 1; }
python3 /root/kt-int-newmods.py $D /root/kt-int-logs/closure_$tag.txt > /root/kt-int-logs/new_$tag.txt
echo "new modules: $(wc -l < /root/kt-int-logs/new_$tag.txt)" >> $L
/root/kt-int-link.sh $S /root/kt-int-logs/new_$tag.txt >> $L
python3 /root/kt-int-placeholders.py $D /root/kt-int-logs/new_$tag.txt /root/kt-int-logs/placeholder_c_$tag.txt >> $L
cd $D
lake build --no-build $(cat /root/kt-int-logs/closure_$tag.txt) > /root/kt-int-logs/nobuild_$tag.log 2>&1; rc=$?
find .lake -name "*.nobuild" -delete
echo "no-build rc=$rc: $(tail -n 1 /root/kt-int-logs/nobuild_$tag.log)" >> $L
grep "^✖" /root/kt-int-logs/nobuild_$tag.log | head -5 >> $L
