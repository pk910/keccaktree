#!/usr/bin/env python3
"""leanchecker over the final module closure, one global longest-first queue with admission by estimated peak RSS.

    kt-int-lcsched.py <module list> [tsv]

* Estimates per module from its .olean size (MB) and its family's measured ratios (sample of 2026-11-10:
  Avx2X10 slice 14.1 s/MB, 0.118 GB/MB; NeonX3 slice 3.0 s/MB, 0.065 GB/MB; Avx512X9 slice 1.1 s/MB, 0.030 GB/MB;
  RvvV8 slice 1.0 s/MB, 0.028 GB/MB); non-slice modules: a floor by kind (library tables import everything).
* Admission: sum of running estimates <= 95 GB, MemAvailable > 20 GB, at most 12 jobs.
* Resource failures (killed by a signal, out of memory) are requeued once at the end to run alone; a leanchecker
  rejection stops admission (running jobs finish) and is reported in lc_sched.log.
* Resumable: modules with rc 0 in the TSV are skipped.  TSV line: module, rc, wall s, peak KB.
* Offloaded olean trees (symlinks into the read-only archive image) are bind-mounted under /root/kt-lcroot, appended
  last to LEAN_PATH (leanchecker's target lookup walks the search path and does not follow symlinked dirs).
"""
import os, re, subprocess, sys, time
LEAN = '/root/kt-int/lean'
LIST = sys.argv[1]
TSV = sys.argv[2] if len(sys.argv) > 2 else '/root/kt-int-logs/leanchecker.tsv'
LOG = '/root/kt-int-logs/lc_sched.log'
MAXP, MAXP_LIGHT, LIGHT, BUDGET, MINAVAIL, MAXSWAP = 16, 16, 4.0, 85.0, 25.0, 8.0
BIG, MEDIUM = 30.0, 12.0     # a job estimated >= BIG runs only while nothing else >= MEDIUM runs (and vice versa)
os.chdir(LEAN)
try:
    open('/proc/self/oom_score_adj', 'w').write('-1000')
except OSError:
    pass

def log(msg):
    with open(LOG, 'a') as f:
        f.write(time.strftime('%m-%d %H:%M:%S ') + msg + '\n')

# family ratios: (s per MB, GB RSS per MB)
def family(m):
    k = m.split('.')[2] if m.startswith('Keccaktree.Kernels.') and len(m.split('.')) > 3 else 'core'
    if k in ('Avx2X9', 'Avx2X10'): return k, 14.1, 0.118
    if k.startswith('Avx2') : return k, 5.0, 0.10
    if k.startswith('Avx512') or k == 'X86X1': return k, 1.1, 0.030
    if k in ('ScalarX1', 'Sha3X2', 'NeonX2', 'Sha3X3', 'Sha3X3r', 'NeonX3'): return k, 3.0, 0.065
    if k.startswith('Rv') or k in ('ZbbX1',): return k, 1.0, 0.028
    return k, 1.0, 0.03

def est(m):
    p = os.path.realpath(os.path.join('.lake/build/lib/lean', *m.split('.')) + '.olean')
    mb = os.path.getsize(p) / 2**20
    fam, spm, gpm = family(m)
    gpm = max(gpm, MEASURED.get(fam, 0.0))
    if CPUR.get(fam):
        spm = max(spm, sum(CPUR[fam]) / len(CPUR[fam]))
    cpu, rss = mb * spm, mb * gpm + 0.8
    if fam in PEAK:          # the ratio is a family max; never estimate above the largest measured slice peak (+15 %)
        rss = min(rss, PEAK[fam] * 1.15)
    leaf = m.split('.')[-1]
    if not re.match(r'(Slice\d+|S\d+)$', leaf):          # modules importing whole kernels / libraries
        rss = max(rss, 4.0)
        if leaf in ('All', 'AllV', 'AllU', 'AllUM', 'Lib', 'LibV', 'InPlaceAll', 'InPlaceAllV') or m.count('.') == 2:
            rss = max(rss, 12.0)
        if m.split('.')[-1] in ('ArmLib', 'ArmLibInPlace', 'X86Lib', 'X86LibInPlace', 'RvLib', 'RvLibUV', 'RvLibU',
                                'RvLibInPlace', 'RvLib2', 'RvLib4', 'RvLib8', 'RvLibUV2', 'RvLibUV4', 'RvLibUV8', 'Dispatch'):
            rss = max(rss, 26.0)
    tables = ('ArmLib', 'ArmLibInPlace', 'X86Lib', 'X86LibInPlace', 'RvLib', 'RvLibUV', 'RvLibU', 'RvLibInPlace',
              'RvLib2', 'RvLib4', 'RvLib8', 'RvLibUV2', 'RvLibUV4', 'RvLibUV8', 'Dispatch')
    if mb < 2:                             # small module: cost is loading its imports (mean 29 s, up to ~30 GB)
        cpu = max(cpu, 30.0)
        if m not in MODPEAK:
            rss = max(rss, FAMSMALL.get(fam, 8.0) * 1.1)
    if m in MODPEAK:                       # measured (also killed jobs: at least that, +25 %)
        rss = max(rss, MODPEAK[m] * 1.25)
    elif not re.match(r'(Slice\d+|S\d+)$', leaf) and (leaf in tables or leaf.startswith(('Lib', 'All', 'InPlaceAll'))
                                                        or 'Lib' in leaf):
        rss = max(rss, 40.0)               # unmeasured library / All / InPlaceAll modules (one Lib reached 38.7 GB)
    return fam, cpu, min(rss, 60.0)

FAMSMALL = {}       # family -> max measured peak GB of its small (< 2 MB olean) modules
MODPEAK = {}        # module -> measured peak GB (any rc; a killed job's peak is a lower bound)
PEAK, CPUR = {}, {}  # family -> max measured peak GB of a slice; measured s per MB of the slices
MEASURED = {}       # family -> max measured GB per MB of olean (from the TSV), overrides the sample ratio when larger
def calibrate(tsv):
    if not os.path.exists(tsv):
        return
    for l in open(tsv):
        p = l.rstrip('\n').split('\t')
        if len(p) < 4 or not p[3].strip().isdigit():
            continue
        m, kb = p[0], int(p[3])
        MODPEAK[m] = max(MODPEAK.get(m, 0.0), kb / 2**20)
        try:
            mb = os.path.getsize(os.path.realpath(os.path.join('.lake/build/lib/lean', *m.split('.')) + '.olean')) / 2**20
        except OSError:
            continue
        if mb < 2:          # small modules: memory is the imported environment, not the module itself
            f0 = family(m)[0]
            FAMSMALL[f0] = max(FAMSMALL.get(f0, 0.0), kb / 2**20)
        if mb < 20 or not re.match(r'(Slice\d+|S\d+)$', m.split('.')[-1]):   # slices only (the ratio is applied to slices;
            continue                                                        # other modules get the floors below)
        fam = family(m)[0]
        MEASURED[fam] = max(MEASURED.get(fam, 0.0), (kb / 2**20) / mb)
        PEAK[fam] = max(PEAK.get(fam, 0.0), kb / 2**20)
        CPUR.setdefault(fam, []).append(float(p[2]) / mb)

def swap_used():
    t = f = 0
    for l in open('/proc/meminfo'):
        if l.startswith('SwapTotal'): t = int(l.split()[1])
        if l.startswith('SwapFree'): f = int(l.split()[1])
    return (t - f) / 2**20

def mem_available():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'):
            return int(l.split()[1]) / 2**20
    return 0.0

# bind mounts for the offloaded trees
R = '/root/kt-lcroot/Keccaktree/Kernels'
kd = '.lake/build/lib/lean/Keccaktree/Kernels'
for d in ([] if '--dry' in sys.argv else sorted(os.listdir(kd))):
    l = os.path.join(kd, d)
    if os.path.islink(l):
        t = os.path.join(R, d); os.makedirs(t, exist_ok=True)
        if subprocess.run(['mountpoint', '-q', t]).returncode != 0:
            subprocess.run(['mount', '--bind', os.path.realpath(l), t], check=True)
lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True, text=True, check=True).stdout.strip()
env = dict(os.environ, LEAN_PATH=lp + ':/root/kt-lcroot')

done = set()
if os.path.exists(TSV):
    for l in open(TSV):
        p = l.split('\t')
        if len(p) > 1 and p[1] == '0':
            done.add(p[0])
calibrate(TSV)
log('measured GB/MB, peak GB per family: ' + ', '.join(f'{k} {v:.3f}/{PEAK[k]:.1f}' for k, v in sorted(MEASURED.items())))
mods = [l.strip() for l in open(LIST) if l.strip()]
queue = []
for m in mods:
    if m in done:
        continue
    fam, cpu, rss = est(m)
    queue.append((cpu, rss, m, fam))
queue.sort(key=lambda x: -x[0])
total_cpu = sum(q[0] for q in queue)
if '--dry' in sys.argv:
    # simulate the admission policy with the estimates (no memory pressure from outside)
    t, run, q, fin = 0.0, [], list(queue), []
    while q or run:
        while q and len(run) < MAXP_LIGHT:
            u = sum(r[1] for r in run)
            i = next((j for j, x in enumerate(q) if (not run or u + x[1] <= BUDGET) and (len(run) < MAXP or x[1] <= LIGHT)), None)
            if i is None: break
            c, r, m, f = q.pop(i); run.append((t + c, r, m))
        run.sort(); e = run.pop(0); t = e[0]
    import collections
    fam = collections.defaultdict(lambda: [0, 0.0])
    for c, r, m, f in queue: fam[f][0] += 1; fam[f][1] += c
    for f, (n, c) in sorted(fam.items(), key=lambda x: -x[1][1])[:12]: print(f'{f:12s} {n:5d} modules {c/3600:7.1f} CPU-h')
    print(f'queued {len(queue)}, est {total_cpu/3600:.0f} CPU-h, simulated wall {t/3600:.1f} h, max est rss {max(q[1] for q in queue):.1f} GB')
    sys.exit(0)
log(f'start: {len(mods)} modules, {len(done)} already ok, {len(queue)} queued, est {total_cpu/3600:.0f} CPU-h')
running = {}          # pid -> (proc, m, rss, t0, timefile, alone)
requeue, stop, alone_q = [], False, []
while queue or running or alone_q:
    # reap
    for pid in list(running):
        proc, m, rss, t0, tf, alone = running[pid]
        rc = proc.poll()
        if rc is None:
            continue
        wall = time.time() - t0
        kb = ''
        try:
            kb = open(tf).read().strip().split('\n')[-1]
            os.remove(tf)
        except Exception:
            pass
        out = f'/root/kt-int-logs/lc_out.{m}.txt'
        txt = open(out).read() if os.path.exists(out) else ''
        with open(TSV, 'a') as f:
            f.write(f'{m}\t{rc}\t{wall:.1f}\t{kb}\n')
        del running[pid]
        if rc == 0:
            os.remove(out) if os.path.exists(out) else None
        elif rc < 0 or rc >= 128 or 'out of memory' in txt.lower() or 'Killed' in txt or 'std::bad_alloc' in txt:
            if alone:
                log(f'FAILED again alone (resource): {m} rc={rc}; stopping')
                stop = True
            else:
                log(f'resource failure: {m} rc={rc}; requeued to run alone')
                alone_q.append((0, rss, m, 'alone'))
        else:
            log(f'LEANCHECKER REJECTION: {m} rc={rc}: {txt.strip()[:500]}; stopping admission')
            stop = True
    if stop and not running:
        break
    # admit
    if not stop:
        while queue and len(running) < MAXP_LIGHT:
            used = sum(r[2] for r in running.values())
            if running and (mem_available() < MINAVAIL or swap_used() > MAXSWAP):
                break
            # longest first among the jobs that fit (backfill: a big head job does not block smaller ones);
            # up to MAXP jobs of any size, up to MAXP_LIGHT when the extra ones are light (est <= LIGHT GB)
            heavy_ok = len(running) < MAXP
            big_running = any(r[2] >= BIG for r in running.values())
            med_running = any(r[2] >= MEDIUM for r in running.values())
            def fits(q):
                if running and used + q[1] > BUDGET: return False
                if not (heavy_ok or q[1] <= LIGHT): return False
                if q[1] >= BIG and med_running: return False
                if big_running and q[1] >= MEDIUM: return False
                return True
            i = next((j for j, q in enumerate(queue) if fits(q)), None)
            if i is None:
                break
            cpu, rss, m, fam = queue.pop(i)
            tf = f'/tmp/kt-int-lc.{m}.t'
            out = open(f'/root/kt-int-logs/lc_out.{m}.txt', 'w')
            adj = -500 if (fam in ('Avx2X9', 'Avx2X10') and '.Gen' in m) or cpu > 1000 else 500
            p = subprocess.Popen(['bash', '-c', f'echo {adj} > /proc/self/oom_score_adj; exec /usr/bin/time -f %M -o {tf} leanchecker {m}'], stdout=out, stderr=subprocess.STDOUT, env=env)
            running[p.pid] = (p, m, rss, time.time(), tf, False)
        if not queue and not running and alone_q:
            cpu, rss, m, fam = alone_q.pop(0)
            tf = f'/tmp/kt-int-lc.{m}.t'
            out = open(f'/root/kt-int-logs/lc_out.{m}.txt', 'w')
            adj = -500 if (fam in ('Avx2X9', 'Avx2X10') and '.Gen' in m) or cpu > 1000 else 500
            p = subprocess.Popen(['bash', '-c', f'echo {adj} > /proc/self/oom_score_adj; exec /usr/bin/time -f %M -o {tf} leanchecker {m}'], stdout=out, stderr=subprocess.STDOUT, env=env)
            running[p.pid] = (p, m, rss, time.time(), tf, True)
    time.sleep(5)
for d in os.listdir(R):
    t = os.path.join(R, d)
    if subprocess.run(['mountpoint', '-q', t]).returncode == 0:
        subprocess.run(['umount', t])
ok = sum(1 for l in open(TSV) if l.split('\t')[1:2] == ['0'])
log(f'end: {ok} modules ok in {TSV}; stop={stop}')
