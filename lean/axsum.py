#!/usr/bin/env python3
"""Summarize `#print axioms` outputs: one row per theorem with its bv_decide certificate
count; fails unless every theorem depends only on propext, Classical.choice, Quot.sound and
`<decl>._native.bv_decide.ax_*` certificate axioms, and no file has an error or sorryAx.
Usage: python3 lean/axsum.py <ax output files...>"""
import re, sys, pathlib
STD = {'propext', 'Classical.choice', 'Quot.sound'}
CERT = re.compile(r'\._native\.bv_decide\.ax_[\d_]+$')
bad_any = False
rows = []
for p in sys.argv[1:]:
    t = pathlib.Path(p).read_text()
    for m in re.finditer(r"'([^']+)' (depends on axioms: \[(.*?)\]|does not depend on any axioms)", t, re.S):
        name = m.group(1)
        axs = [a.strip() for a in (m.group(3) or '').replace('\n', ' ').split(',') if a.strip()]
        certs = [a for a in axs if CERT.search(a)]
        other = [a for a in axs if a not in STD and not CERT.search(a)]
        bad = bool(other)
        bad_any |= bad
        rows.append((pathlib.Path(p).name, name, len(certs), 'OK' if not bad else 'BAD: ' + ' '.join(other)))
    errs = [l for l in t.split('\n') if re.search(r'\berror\b', l)]
    if errs or 'sorryAx' in t:
        bad_any = True
        rows.append((pathlib.Path(p).name, '<file>', 0, 'BAD: errors/sorry'))
w = max(len(r[1]) for r in rows)
for f, n, c, s in rows:
    print('%-28s %-*s %6d certs  %s' % (f, w, n, c, s))
print('theorems: %d   all clean: %s' % (len(rows), not bad_any))
sys.exit(1 if bad_any else 0)
