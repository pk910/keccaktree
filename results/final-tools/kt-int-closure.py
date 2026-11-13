#!/usr/bin/env python3
"""closure.py <dst lean dir> <src lean dir> <root module...>: import closure of the roots in dst's sources;
for each module: source identical in src? built in src? (prints a table; exit 1 if any differs/missing)"""
import hashlib, os, re, sys
dst, src, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
def path(base, m): return os.path.join(base, *m.split('.')) + '.lean'
def imports(base, m):
    t = open(path(base, m)).read()
    return re.findall(r'^import\s+(\S+)', t, re.M)
seen, todo = set(), list(roots)
while todo:
    m = todo.pop()
    if m in seen or not m.startswith(('Keccaktree', 'Tools')): continue
    seen.add(m)
    if not os.path.exists(path(dst, m)):
        print('MISSING-IN-DST', m); continue
    todo += imports(dst, m)
bad = 0
for m in sorted(seen):
    a, b = path(dst, m), path(src, m)
    same = os.path.exists(b) and open(a, 'rb').read() == open(b, 'rb').read()
    built = os.path.exists(os.path.join(src, '.lake/build/lib/lean', *m.split('.')) + '.olean')
    if not (same and built):
        bad += 1; print('DIFF' if not same else 'UNBUILT', m)
print(f'{len(seen)} modules, {bad} not reusable', file=sys.stderr)
with open(os.environ.get('OUT', '/dev/null'), 'w') as f:
    f.write('\n'.join(sorted(seen)) + '\n')
sys.exit(1 if bad else 0)
