#!/usr/bin/env python3
"""In place: emit Keccaktree/Kernels/<Ns>/InPlaceAll.lean for a 1-node RISC-V scalar kernel with the rv64_x1
frame, from Kernels/Rv64X1/InPlaceAll.lean (the template), as gen_all_rvu.py does for AllU: the instruction
indices and step counts >= 5346 shift by a constant, the names differ.

    gen_inplace_rv1.py <kernel> <Ns> <shift>        zbb_x1 ZbbX1 -1931

The segment summaries come from `gen_inplace.py <Ns> GenSE GenSI GenSJ GenSC GenSX --eval --split`."""
import os, re, sys
kernel, ns, d = sys.argv[1], sys.argv[2], int(sys.argv[3])
root = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(root, 'Keccaktree/Kernels/Rv64X1/InPlaceAll.lean')).read()
out = re.sub(r'\b(5[0-9]{3})\b', lambda m: str(int(m.group(1)) + d), src)
out = out.replace('Rv64X1', ns).replace('rv64_x1', kernel)
if kernel == 'zbb_x1':
    out = out.replace('RvVl.entries.1', 'RvVl.entries.2.1')
open(os.path.join(root, f'Keccaktree/Kernels/{ns}/InPlaceAll.lean'), 'w').write(out)
print('written', ns)
