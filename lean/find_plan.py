#!/usr/bin/env python3
"""A plan (cuts + per-node round schedule) for a kernel run on `count` nodes, from a `kttool scan`:
for every node the first step at which each of its rounds 1..23 is complete (25 lanes) and at which
its digest (round 24, lanes 0..3) is in place; the cuts are the union of these steps.
Usage: find_plan.py <kernel> <count> <lanes> [fuel]   → prints the plan JSON."""
import json, re, subprocess, sys, os
k, count, lanes = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
fuel = int(sys.argv[4]) if len(sys.argv) > 4 else 200000
KT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '.lake/build/bin/kttool')
out = subprocess.run([KT, 'scan', k, str(count), str(fuel), str(lanes)], capture_output=True, text=True, check=True).stdout
starts = {n: {} for n in range(count)}   # node -> round -> first scan line where complete
nlines = 0
for ln in out.splitlines():
    m = re.match(r'^(\d+) (\d+)(.*)$', ln)
    if not m:
        continue
    nlines += 1
    t = int(m.group(1))
    for n_s, parts in re.findall(r'n(\d+):\[(.*?)\]', m.group(3)):
        n = int(n_s)
        for r_s, l_s in re.findall(r'r(\d+):(\d+)L', parts):
            r, l = int(r_s), int(l_s)
            if r == 0:
                continue
            if (r < 24 and l == 25) or (r == 24 and l >= 4):
                if r not in starts[n] or starts[n][r] > t:
                    # first occurrence only (lines are in order)
                    starts[n].setdefault(r, t)
cuts = sorted(set(t for n in starts for t in starts[n].values()))
def round_at(n, t):   # rounds of node n complete at scan line t (steps t+1)
    return max([r for r, s in starts[n].items() if s <= t] + [0])
rounds = [[0] * count] + [[round_at(n, t) for n in range(count)] for t in cuts] + [[round_at(n, nlines) for n in range(count)]]
# sanity: every node advances by at most one round per slice, in order
for c in range(len(rounds) - 1):
    for n in range(count):
        assert rounds[c + 1][n] in (rounds[c][n], rounds[c][n] + 1), (c, n, rounds[c][n], rounds[c + 1][n])
plan = {'kernel': k, 'count': count, 'lanes': lanes, 'entry': 0, 'end': nlines, 'cuts': cuts, 'rounds': rounds}
print(json.dumps(plan))
print(f'{len(cuts)} cuts, {nlines} steps, final rounds {rounds[-1]}', file=sys.stderr)
