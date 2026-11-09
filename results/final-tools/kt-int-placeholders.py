#!/usr/bin/env python3
"""kt-int-placeholders.py <lean dir> <module list> <out list>: for each (linked) module whose trace records a .c output
missing under ir/: a fresh empty ir/<m>.c and ir/<m>.c.hash holding the recorded hash.  Asserts that the .olean.hash
equals the olean hash recorded in the trace."""
import json, os, sys
D, mods, outf = sys.argv[1], sys.argv[2], sys.argv[3]
os.chdir(os.path.join(D, '.lake/build'))
out, have = [], 0
for m in open(mods):
    m = m.strip()
    if not m:
        continue
    p = m.replace('.', '/')
    o = json.load(open(f'lib/lean/{p}.trace'))['outputs']
    ol = (o['o'][0] if isinstance(o['o'], list) else o['o']).split('.')[0]
    assert open(f'lib/lean/{p}.olean.hash').read().strip() == ol, m
    c = o.get('c')
    if not c:
        continue
    if os.path.exists(f'ir/{p}.c'):
        have += 1
        continue
    h = c.split('.')[0]
    os.makedirs(os.path.dirname(f'ir/{p}.c'), exist_ok=True)
    open(f'ir/{p}.c', 'w').close()
    open(f'ir/{p}.c.hash', 'w').write(h)
    out.append(f'{m} c={h} olean={ol}')
open(outf, 'w').write('\n'.join(out) + ('\n' if out else ''))
print(len(out), 'placeholders,', have, 'real .c')
