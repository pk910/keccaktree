#!/bin/bash
# kt-int-link.sh <src lean dir> <module list>: hard-link the build outputs (lib/lean and ir) of the listed modules
src=$1; list=$2; dst=/root/kt-int/lean; n=0
while read m; do p=${m//.//}
  for sub in lib/lean ir; do d=$(dirname $dst/.lake/build/$sub/$p); 
    for f in $src/.lake/build/$sub/$p.*; do [ -f "$f" ] || continue; mkdir -p $d; [ -e $d/$(basename $f) ] && continue; ln $f $d/$(basename $f) && n=$((n+1)); done
  done
done < $list
echo "linked $n files"
