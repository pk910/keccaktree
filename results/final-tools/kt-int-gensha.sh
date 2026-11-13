#!/bin/bash
# sha256 of each Gen dir: deterministic tar of its files in sorted order (paths relative to Keccaktree/Kernels)
#   tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner --mode=a=r,u+w,a+X --format=gnu -cf - <Ns>/<Gen> | sha256sum
# usage: kt-int-gensha.sh <lean dir> <Ns...>
cd $1/Keccaktree/Kernels; shift
for ns in "$@"; do for g in $ns/Gen*; do
  [ -d $g ] || continue
  h=$(tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner --mode=a=r,u+w,a+X --format=gnu -cf - $g | sha256sum | cut -c1-64)
  echo "$g $(ls $g | wc -l) $h"
done; done
