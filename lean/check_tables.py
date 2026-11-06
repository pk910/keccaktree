#!/usr/bin/env python3
"""Cross-check that the RC / RHO / PI tables of the Lean model
(lean/Keccaktree/Generic.lean) are literally the tables of
src/keccak256_generic.c and keccak256_1_generic.go."""
import re, sys, pathlib
repo = pathlib.Path(sys.argv[1])
def nums(text, name, start_pat):
    m = re.search(start_pat, text, re.S)
    assert m, name
    body = text[m.end():]
    body = body[:body.index('}')]
    return [int(x, 0) for x in re.findall(r'0x[0-9a-fA-F]+|\d+', body)]
c = (repo / 'src/keccak256_generic.c').read_text()
g = (repo / 'keccak256_1_generic.go').read_text()
l = (repo / 'lean/Keccaktree/Generic.lean').read_text()
tabs = {}
tabs['C'] = dict(RC=nums(c, 'RC', r'RC\[24\] = \{'), RHO=nums(c, 'RHO', r'RHO\[24\] = \{'), PI=nums(c, 'PI', r'PI\[24\] = \{'))
tabs['Go'] = dict(RC=nums(g, 'RC', r'keccakRC = \[24\]uint64\{'), RHO=nums(g, 'RHO', r'keccakRho = \[24\]int\{'), PI=nums(g, 'PI', r'keccakPi = \[24\]int\{'))
def lean_tab(name, w):
    m = re.search(r'def %s \(\w+ : Nat\) : \w+ :=\s*match \w+ with(.*?)\| _' % name, l, re.S)
    assert m, name
    pairs = re.findall(r'\|\s*(\d+)\s*=>\s*(0x[0-9a-fA-F]+|\d+)', m.group(1))
    d = {int(i): int(v, 0) for i, v in pairs}
    return [d[i] for i in range(24)]
tabs['Lean'] = dict(RC=lean_tab('RC', 64), RHO=lean_tab('RHO', 0), PI=lean_tab('PI', 0))
ok = True
for t in ('RC', 'RHO', 'PI'):
    for src in ('C', 'Go'):
        same = tabs[src][t] == tabs['Lean'][t]
        ok &= same
        print('%-3s %-4s vs Lean: %s (%d entries)' % (t, src, 'same' if same else 'DIFFER', len(tabs[src][t])))
    # the C unused-value sanity: 24 entries each
    assert len(tabs['Lean'][t]) == 24
print('ALL TABLES MATCH' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
