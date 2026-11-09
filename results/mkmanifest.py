#!/usr/bin/env python3
"""results/manifest.txt for the final tree.

    mkmanifest.py <repo> <gen_sha256.txt> <axioms outputs dir> [<leanchecker.tsv>] > results/manifest.txt

gen_sha256.txt: "<Ns>/<Gen> <files> <sha256>" lines from /root/kt-int-gensha.sh (deterministic tar of each Gen dir).
axioms outputs: the `#print axioms` outputs of the final combined check (out_Final_*.txt).
leanchecker.tsv: "<module> <rc> <seconds> <maxKB>" lines from /root/kt-int-leanchecker.sh.
"""
import hashlib, os, re, subprocess, sys
repo, gensha, axdir = sys.argv[1:4]
lctsv = sys.argv[4] if len(sys.argv) > 4 else None
git = lambda *a: subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True, check=True).stdout.strip()
def sha(p):
    return hashlib.sha256(open(os.path.join(repo, p), 'rb').read()).hexdigest()
def exists(p):
    return os.path.exists(os.path.join(repo, p))
KN = 'Keccaktree.Kernels.'

gens = {}
for l in open(gensha):
    if l.strip():
        d, n, h = l.split()
        gens.setdefault(d.split('/')[0], []).append((d.split('/')[1], n, h))
ax = {}
for f in sorted(os.listdir(axdir)):
    if not f.startswith('out_'):
        continue
    t = open(os.path.join(axdir, f)).read()
    for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", t, re.S):
        names = [x.strip() for x in m.group(2).replace('\n', ' ').split(',') if x.strip()]
        std = [x for x in names if x in ('propext', 'Classical.choice', 'Quot.sound')]
        cert = [x for x in names if re.search(r'\._native\.bv_decide\.ax_[\d_]+$', x)]
        bad = [x for x in names if x not in std and x not in cert]
        ax[m.group(1)] = '%s + %d bv_decide certificates%s' % (', '.join(std), len(cert), ('; OTHER: ' + ', '.join(bad)) if bad else '')
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", t):
        ax[m.group(1)] = 'none'
lc = {}
if lctsv:
    for l in open(lctsv):
        p = l.rstrip('\n').split('\t')
        if len(p) >= 3:
            lc[p[0]] = (int(p[1]), float(p[2]), p[3] if len(p) > 3 else '')
def lc_line(prefixes):
    mods = [m for m in lc if any(m == p or m.startswith(p + '.') for p in prefixes)]
    if not mods:
        return 'not run'
    ok = sum(1 for m in mods if lc[m][0] == 0)
    secs = sum(lc[m][1] for m in mods)
    return '%d/%d modules ok, %.0f s' % (ok, len(mods), secs)
def axl(t):
    return ax.get(KN + t if not t.startswith('Keccaktree.') else t, 'NOT CHECKED')

# (kernel, ISA, Ns, program dir, object, theorem suffixes, extra modules for leanchecker)
X86 = [('x86_x1', 'X86X1'), ('avx2_x2', 'Avx2X2'), ('avx2_x4', 'Avx2X4'), ('avx2_x5', 'Avx2X5'), ('avx2_x6', 'Avx2X6'),
       ('avx2_x8', 'Avx2X8'), ('avx2_x9', 'Avx2X9'), ('avx2_x10', 'Avx2X10'), ('avx512vl_x4', 'Avx512vlX4'),
       ('avx512vl_x4d', 'Avx512vlX4d'), ('avx512_x8', 'Avx512X8'), ('avx512_x8d', 'Avx512X8d'), ('avx512_x9', 'Avx512X9'),
       ('avx512_x9d', 'Avx512X9d')]
ARM = [('scalar_x1', 'ScalarX1'), ('sha3_x2', 'Sha3X2'), ('neon_x2', 'NeonX2'), ('sha3_x3', 'Sha3X3'), ('sha3_x3r', 'Sha3X3r'),
       ('neon_x3', 'NeonX3')]
K = []
for k, ns in X86:
    th = (['X86X1.All.x86_x1_all', 'X86X1.Lib.norm_thm'] if ns == 'X86X1' else [ns + '.All.norm_thm']) + \
         [ns + '.Lib.kernel', ns + '.InPlaceAll.access_thm', ns + '.InPlaceAll.kernelAl']
    if ns in ('Avx2X4', 'Avx2X10'):
        th += [ns + '.AllV.norm_thm', ns + '.LibV.kernel', ns + '.InPlaceAllV.access_thm', ns + '.InPlaceAllV.kernelAl']
    K.append((k, 'x86-64', ns, ns, k, th))
for k, ns in ARM:
    th = (['ScalarX1.All.scalar_x1_all'] if ns == 'ScalarX1' else [ns + '.All.all']) + \
         [ns + '.All.norm_thm', ns + '.All.kernel', ns + '.InPlaceAll.access_thm', ns + '.InPlaceAll.kernelAl']
    K.append((k, 'AArch64', ns, ns, k, th))
for k, ns in (('rv64_x1', 'Rv64X1'), ('zbb_x1', 'ZbbX1')):
    th = [ns + '.All.' + k + '_all', ns + '.All.kernel', ns + '.All.kernel_ch', ns + '.AllU.' + k + '_allU', ns + '.AllU.kernelU',
          ns + '.AllU.kernelU_ch', ns + '.InPlaceAll.access_thm', ns + '.InPlaceAll.kernelAl']
    K.append((k, 'RISC-V', ns, ns, k, th))
for k, pns in (('rvv', 'Rvv'), ('rvv_zvkb', 'RvvZvkb')):
    for V in (2, 4, 8):
        ns = '%sV%d' % (pns, V)
        th = [ns + '.All.' + t for t in ('all', 'all_ch', 'norm_thm', 'kernel', 'kernel_ch')] + \
             [ns + '.AllUM.norm_thmU', ns + '.AllUM.kernelU', ns + '.InPlaceAll.access_thm', ns + '.InPlaceAll.kernelAl']
        K.append(('%s_v%d' % (k, V), 'RISC-V VLEN %d' % (64 * V), ns, pns, k, th))
LIBS = [('AArch64 library', 'ArmLib', ['ArmLib.lib_arm_all']),
        ('AArch64 library, in place', 'ArmLibInPlace', ['ArmLibInPlace.lib_inplace_arm_all']),
        ('x86-64 library (every threshold configuration)', 'X86Lib', ['X86Lib.lib_x86_all']),
        ('x86-64 library, in place', 'X86LibInPlace', ['X86LibInPlace.lib_inplace_x86_all']),
        ('RISC-V library (VLEN 128/256/512, any vl choice)', 'RvLib',
         ['RvLib.lib2', 'RvLib.lib2ch', 'RvLib.lib4', 'RvLib.lib4ch', 'RvLib.lib8', 'RvLib.lib8ch']),
        ('RISC-V scalar library, any buffer alignment', 'RvLibU', ['RvLibU.libU', 'RvLibU.libU_ch']),
        ('RISC-V library, any buffer alignment', 'RvLibUV', ['RvLibUV.lib2U', 'RvLibUV.lib4U', 'RvLibUV.lib8U']),
        ('RISC-V library, in place', 'RvLibInPlace', ['RvLibInPlace.lib_inplace2', 'RvLibInPlace.lib_inplace4', 'RvLibInPlace.lib_inplace8'])]
CORE = ['Keccaktree.Asm.LibTable.lib_x86', 'Keccaktree.Asm.LibTable.lib_arm', 'Keccaktree.Asm.LibTable.lib_rv',
        'Keccaktree.Dispatch.hash_x86', 'Keccaktree.Dispatch.hash_x86_reachable', 'Keccaktree.Dispatch.hash_arm',
        'Keccaktree.Dispatch.hash_rv']

head = git('rev-parse', '--short', 'HEAD')
out = []
w = out.append
w('# keccaktree Lean verification: manifest of the proved kernels (final tree, frozen base)')
w('# regenerate: python3 results/mkmanifest.py . results/gen_sha256.txt <axioms outputs> <leanchecker.tsv>')
w(f'# tree: {head}; base freeze e43c5ea (Iter {git("rev-parse", "--short=7", "e43c5ea:lean/Keccaktree/Asm/Iter.lean")}); '
  f'src/ tree {git("rev-parse", "HEAD:src")}')
w('# program : lean/Keccaktree/Kernels/<P>/Program.lean (lean/asm2lean.py of the object file), sha256, last commit')
w('# object  : keccak256_<k>.o assembled from src/keccak256_<k>.S at the src/ tree above; last commit of the .S')
w('# files   : the committed proof files of the kernel (All/Lib/AllU/AllUM/InPlace*), sha256')
w('# gen     : generated segment dirs (not committed), <dir> <files> <sha256 of a deterministic tar>:')
w('#           tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner --mode=a=r,u+w,a+X --format=gnu -cf - <Ns>/<Gen> | sha256sum')
w('# axioms  : #print axioms on the frozen base (kt-int, final combined check): the standard axioms + the number of')
w('#           bv_decide certificate axioms (`<decl>._native.bv_decide.ax_*`); anything else would be listed as OTHER')
w('# checker : leanchecker (Lean 4.35.0) over the kernel\'s modules: modules ok / checked, summed wall time')
w('')
for (k, isa, ns, pns, obj, th) in K:
    w(f'[{k}] {isa}')
    pp = f'lean/Keccaktree/Kernels/{pns}/Program.lean'
    w(f'  program   {pp} sha256 {sha(pp)} commit {git("log", "-1", "--format=%h", "--", pp)}')
    w(f'  object    keccak256_{obj}.o from src/keccak256_{obj}.S commit {git("log", "-1", "--format=%h", "--", f"src/keccak256_{obj}.S")}')
    kd = f'lean/Keccaktree/Kernels/{ns}'
    for f in ('All.lean', 'AllV.lean', 'AllU.lean', 'AllUIn.lean', 'AllUM.lean', 'Lib.lean', 'LibV.lean', 'InPlaceAll.lean', 'InPlaceAllV.lean'):
        if exists(f'{kd}/{f}'):
            w(f'  file      {kd}/{f} sha256 {sha(kd + "/" + f)}')
    if exists(f'{kd}/InPlace'):
        n = sum(len(fs) for _, _, fs in os.walk(os.path.join(repo, kd, 'InPlace')))
        tree = git('rev-parse', f'HEAD:{kd}/InPlace')
        w(f'  inplace   {kd}/InPlace {n} files, git tree {tree}')
    for (g, n, h) in sorted(gens.get(ns, [])):
        w(f'  gen       {ns}/{g} {n} {h}')
    for t in th:
        w(f'  theorem   {KN}{t}')
        w(f'    axioms  {axl(t)}')
    w(f'  checker   {lc_line([KN + ns])}')
    w('')
for (name, mod, th) in LIBS:
    p = f'lean/Keccaktree/Kernels/{mod}.lean'
    w(f'[{name}] {p} sha256 {sha(p) if exists(p) else "MISSING"}')
    for t in th:
        w(f'  theorem   {KN}{t}')
        w(f'    axioms  {axl(t)}')
    w(f'  checker   {lc_line([KN + mod])}')
    w('')
w('[core] lean/Keccaktree/Asm/LibTable.lean, lean/Keccaktree/Dispatch.lean')
for t in CORE:
    w(f'  theorem   {t}')
    w(f'    axioms  {axl(t)}')
w(f'  checker   {lc_line(["Keccaktree.Asm", "Keccaktree.Dispatch", "Keccaktree.Spec", "Keccaktree.Proof", "Keccaktree.Generic"])}')
w('')
if lc:
    ok = sum(1 for v in lc.values() if v[0] == 0)
    w(f'[leanchecker total] {ok}/{len(lc)} modules ok, {sum(v[1] for v in lc.values()):.0f} s summed wall time')
    w('')
w('[build notes] see notes/int.md: x86 kernels replayed by hard links (closure sources identical, `lake build --no-build`')
w('  up to date); placeholder / truncated compiled-C lists (results/x86b_replay_placeholder_c.txt and the')
w('  truncation lists); offloaded olean trees (symlinks to the archive disk); regeneration notes.')
sys.stdout.write('\n'.join(out) + '\n')
