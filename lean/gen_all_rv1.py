#!/usr/bin/env python3
"""Emit Keccaktree/Kernels/<Ns>/All.lean for a 1-node RISC-V kernel with the rv64_x1 frame, from
Kernels/Rv64X1/All.lean (the template): only the instruction indices of the back edge / exit / ret,
the body length and the names differ.

    gen_all_rv1.py <kernel> <Ns> <back_edge_index> <ret_index> <body_len>
      rv64_x1: 5410 5429 5369;  zbb_x1: 3479 3498 3438
"""
import os, re, sys
kernel, ns, be, ret, L = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
root = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(root, 'Keccaktree/Kernels/Rv64X1/All.lean')).read()
T = {5410: be, 5411: be + 1, 5412: be + 2, 5413: be + 3, 5414: be + 4, 5415: be + 5, 5429: ret,
     5369: L, 5374: L + 5, 5373: L + 4}
out = re.sub(r'\b(5410|5411|5412|5413|5414|5415|5429|5369|5374|5373)\b', lambda m: str(T[int(m.group(1))]), src)
out = out.replace('Rv64X1', ns).replace('rv64_x1', kernel)
if kernel == 'zbb_x1':
    out = out.replace('RvVl.entries.1', 'RvVl.entries.2.1')
open(os.path.join(root, f'Keccaktree/Kernels/{ns}/All.lean'), 'w').write(out)
