#!/bin/bash
# In place (out == in) for an x86 kernel with an X86K every-count proof (x86b's x86_glue.py):
#   inplace_x86k.sh <Dir> <kernel> [lake module prefix runner]
# Run in the lean/ directory after the kernel's Gen*/ segments and All/Lib are built (and before their
# oleans are removed).  Steps:
#   1. footprint summaries of every segment (`gen_inplace.py --eval --split`: InPlace/Gen*.lean, InPlace/Gen*/S<k>.lean);
#   2. the access proof and in-place kernel (`x86_glue_al.py`: InPlaceAll.lean);
#   3. sequential builds: X86AccFr, X86AnnAl, each slice summary S<k> (one lean process each), each
#      segment summary module, then InPlaceAll.
# lake has no job limit: the modules are built one at a time.
set -e
D=$1; K=$2
segs=$(cd Keccaktree/Kernels/$D && ls -d Gen* | tr '\n' ' ')
python3 gen_inplace.py $D $segs --eval --split
python3 x86_glue_al.py $K
lake build Keccaktree.Asm.X86AccFr Keccaktree.Asm.X86AnnAl
for g in $segs; do
  n=$(ls Keccaktree/Kernels/$D/InPlace/$g/S*.lean | wc -l)
  for k in $(seq 0 $((n - 1))); do lake build Keccaktree.Kernels.$D.InPlace.$g.S$k; done
  lake build Keccaktree.Kernels.$D.InPlace.$g
done
lake build Keccaktree.Kernels.$D.InPlaceAll
