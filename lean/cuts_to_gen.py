#!/usr/bin/env python3
"""Rewrite the gen_all.sh entries of the kernels listed in a find_cuts log (`== name count lanes …` lines
followed by the `0 end_t cuts…` line).  Usage: cuts_to_gen.py <cuts.log>"""
import re, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
log = open(sys.argv[1]).read().splitlines()
entries = {}
for i, ln in enumerate(log):
    m = re.match(r'^== (\w+) (\d+) (\d+) ', ln)
    if m and i + 1 < len(log) and re.match(r'^0 \d+( \d+){23}$', log[i + 1]):
        entries[m.group(1)] = (int(m.group(2)), int(m.group(3)), log[i + 1])
ns = lambda k: ''.join(p.capitalize() for p in k.split('_'))
isa = lambda k: 'X86' if k.startswith(('avx', 'x86')) else 'Arm'
p = os.path.join(HERE, 'gen_all.sh'); s = open(p).read().splitlines()
out = []; seen = set()
for ln in s:
    m = re.match(r'^K=(\w+);\s*want "\$@" && ISA=(X86|Arm) gen ', ln)
    if m and m.group(1) in entries:
        k = m.group(1); count, lanes, nums = entries[k]; seen.add(k)
        out.append(f'K={k};{" " * max(1, 13 - len(k))}want "$@" && ISA={isa(k)} gen {k} {ns(k)} {count} {lanes} {nums}')
    else:
        out.append(ln)
# new kernels: after the last x86 / arm entry respectively
for k, (count, lanes, nums) in entries.items():
    if k in seen:
        continue
    line = f'K={k};{" " * max(1, 13 - len(k))}want "$@" && ISA={isa(k)} gen {k} {ns(k)} {count} {lanes} {nums}'
    anchor = max(i for i, ln in enumerate(out) if re.match(r'^K=\w+;\s*want "\$@" && ISA=%s ' % isa(k), ln))
    out.insert(anchor + 1, line)
open(p, 'w').write('\n'.join(out) + '\n')
print('updated', sorted(entries))
