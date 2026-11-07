#!/usr/bin/env python3
"""Find the cut steps of a kernel's batch from a `kttool scan`: for every round r = 1..23 the
midpoint of the first window of steps at which every node's complete round-r state (25 lanes)
is present somewhere (registers / stack / memory), and the step count to the final `ret`.
Usage: find_cuts.py <kernel> <count> <lanes> [fuel]   → prints "<entry=0> <end_t> <23 cuts>"."""
import re, subprocess, sys, os
k, count, lanes = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
fuel = int(sys.argv[4]) if len(sys.argv) > 4 else 40000
KT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '.lake/build/bin/kttool')
out = subprocess.run([KT, 'scan', k, str(count), str(fuel), str(lanes)], capture_output=True, text=True, check=True).stdout
lines = out.splitlines()
steps = []  # per t: set of rounds complete on all nodes
for ln in lines:
    m = re.match(r'^(\d+) (\d+)(.*)$', ln)
    if not m:
        continue
    t = int(m.group(1))
    nodes = re.findall(r'n(\d+):\[(.*?)\]', m.group(3))
    complete = None
    for n, parts in nodes:
        rs = set(int(r) for r, l in re.findall(r'r(\d+):(\d+)L', parts) if int(l) == 25)
        complete = rs if complete is None else (complete & rs)
    steps.append((t, complete or set()))
end_t = len(steps)  # the last line is the final `ret`; the batch ends after it
cuts = []
for r in range(1, 24):
    ts = [t for t, c in steps if r in c]
    if not ts:
        print(f'round {r}: never complete on all nodes', file=sys.stderr); sys.exit(1)
    # first maximal window
    lo = ts[0]; hi = lo
    for t in ts[1:]:
        if t == hi + 1: hi = t
        else: break
    cuts.append((lo + hi) // 2)
    print(f'round {r}: window [{lo}, {hi}] -> cut {cuts[-1]}', file=sys.stderr)
print(' '.join(str(x) for x in [0, end_t] + cuts))
