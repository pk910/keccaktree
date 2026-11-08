#!/usr/bin/env python3
"""Emit Keccaktree/Kernels/<Ns>/{AllUIn,AllU,All}.lean for a 1-node RISC-V scalar kernel with the rv64_x1
frame (any buffer alignment), from the Rv64X1 files (the templates): only the instruction indices of the
digest stores / back edge / exit / ret (all ≥ 5346 in the template: shifted by a constant), the length
of the rounds segment, the per-iteration step count and the names differ.

    gen_all_rvu.py <kernel> <Ns> <shift>        zbb_x1 ZbbX1 -1931
(rv64_x1: rounds [31, 5377), back edge 5410; zbb_x1: [31, 3446), back edge 3479.)
"""
import os, re, sys
kernel, ns, d = sys.argv[1], sys.argv[2], int(sys.argv[3])
root = os.path.dirname(os.path.abspath(__file__))
for f in ('AllUIn.lean', 'AllU.lean', 'All.lean'):
    src = open(os.path.join(root, 'Keccaktree/Kernels/Rv64X1', f)).read()
    out = re.sub(r'\b(5[0-9]{3})\b', lambda m: str(int(m.group(1)) + d), src)
    out = out.replace('Rv64X1', ns).replace('rv64_x1', kernel)
    if kernel == 'zbb_x1':
        out = out.replace('RvVl.entries.1', 'RvVl.entries.2.1')
    open(os.path.join(root, f'Keccaktree/Kernels/{ns}/{f}'), 'w').write(out)
