#!/usr/bin/env python3
"""kt-int-modlist.py <lean dir> <root module...>: the Keccaktree modules in the import closure of the roots,
in dependency order (imports before importers)"""
import os, re, sys
D, roots = sys.argv[1], sys.argv[2:]
order, seen = [], set()
def visit(m):
    if m in seen or not m.startswith('Keccaktree'):
        return
    seen.add(m)
    p = os.path.join(D, *m.split('.')) + '.lean'
    for i in re.findall(r'^import\s+(\S+)', open(p).read(), re.M):
        visit(i)
    order.append(m)
sys.setrecursionlimit(100000)
for r in roots:
    visit(r)
print('\n'.join(order))
