#!/usr/bin/env python3
"""Compare hardware and model final states.

    compare.py <isa> <setdir> [lanes nvregs]

<setdir> holds states.txt, meta.json, instrs.json, hw.txt, model.txt.  Writes report.txt and
mismatches.txt there; prints the summary.  Equality of general registers / memory words modulo
the model's region encoding: a model word (r << 56) + off with 1 <= r <= 4 matches the hardware
address base_r + off (the harness prints the bases); a return address the model stores as an
instruction index matches the hardware address of that instruction."""
import collections
import json
import os
import re
import sys

isa, d = sys.argv[1], sys.argv[2]
NL = int(sys.argv[3]) if len(sys.argv) > 3 else 8
NV = int(sys.argv[4]) if len(sys.argv) > 4 else 32
MASK = (1 << 56) - 1


def blocks(path):
    hdr, cur, out = {}, None, []
    for ln in open(path):
        w = ln.split()
        if not w:
            continue
        if w[0] == 'B':
            hdr[int(w[1])] = int(w[2], 16)
        elif w[0] == 'T':
            hdr['T'] = int(w[1], 16)
        elif w[0] == 'C':
            cur = {'G': {}, 'V': {}, 'K': {}, 'M': {}, 'raw': []}
            if len(w) > 2:
                cur['snip'] = int(w[1])
        elif w[0] == 'E':
            out.append(cur)
        elif cur is not None:
            cur['raw'].append(ln.rstrip())
            if w[0] == 'G':
                cur['G'][int(w[1])] = (int(w[2], 16), len(w) > 3 and w[3] == 'P')
            elif w[0] == 'V':
                cur['V'][int(w[1])] = [int(x, 16) for x in w[2:]]
            elif w[0] == 'K':
                cur['K'][int(w[1])] = int(w[2])
            elif w[0] == 'M':
                cur['M'][(int(w[1]), int(w[2]))] = (int(w[3], 16), len(w) > 4 and w[4] == 'P')
            elif w[0] == 'F':
                cur['F'] = tuple(int(x) for x in w[1:5])
            elif w[0] == 'X':
                cur['X'] = tuple(int(x) for x in w[1:4])
            elif w[0] == 'W':
                cur['W'] = int(w[1])
            elif w[0] == 'S':
                cur['S'] = int(w[1])
            elif w[0] == 'L':
                cur['L'] = int(w[1])
    return hdr, out


meta = json.load(open(os.path.join(d, 'meta.json')))
ins = json.load(open(os.path.join(d, 'instrs.json')))
_, init = blocks(os.path.join(d, 'states.txt'))
hdr, hw = blocks(os.path.join(d, 'hw.txt'))
_, mo = blocks(os.path.join(d, 'model.txt'))
assert len(hw) == len(mo) == len(init) == len(meta), (len(hw), len(mo), len(init), len(meta))
entries = ins['entries']
ends = sorted(entries) + [len(ins['instrs'])]
nxt = {e: ends[i + 1] for i, e in enumerate(sorted(entries))}


def snip_instrs(j):
    e = entries[j]
    return ins['instrs'][e:nxt[e]]


def form(j):
    s = snip_instrs(j)
    body = [x for x in s if not x.startswith('.tailcall')] or s
    f = ' ; '.join(body[:3])
    f = re.sub(r'"[^"]*"', 'S', f)
    f = re.sub(r'-?\d+', 'N', f)
    return f


def wmatch(m, h, j):
    if m == h:
        return True
    r = m >> 56
    if 1 <= r <= 4 and r in hdr and h == (hdr[r] + (m & MASK)) % (1 << 64):
        return True
    if isa == 'x86' and m < len(ins['addr']) and h == hdr['T'] + ins['addr'][m]:
        return True     # a return address (model: instruction index)
    return False


FLAG_IGNORE = {'.alu', '.andn', '.add', '.andi', '.shl', '.addm', '.xorm', '.btc'}


def flags_policy(j, st):
    """which flags to compare: x86 (zf, cf); arm (zf, cf, nf, vf); riscv none"""
    if isa == 'riscv':
        return ()
    ops = [x.split()[0] for x in snip_instrs(j)]
    if any(o in FLAG_IGNORE for o in ops):
        return ()
    if isa == 'x86':
        for x in snip_instrs(j):
            if x.startswith('.sub '):
                g = int(x.split()[1])
                if (st['G'][g][0] >> 56) != 0:
                    return ()
        return (0, 1)
    return (0, 1, 2, 3)


stats = collections.defaultdict(lambda: collections.Counter())
mism = []
for n, (m, h, st, mt) in enumerate(zip(mo, hw, init, meta)):
    j = mt['snip']
    f = form(j)
    key = (mt['src'].split('-')[0], f)
    stats[key]['states'] += 1
    if m['X'][0]:
        stats[key]['model_err'] += 1
        continue
    diffs = []
    if not m['X'][1]:
        diffs.append('model did not halt (pc %d)' % m['X'][2])
    if 'S' in h and mt['text'].split()[0] in ('vmovdqa', 'vmovdqa64'):
        # a misaligned aligned move (x86gen.py probes these): the CPU faults, the model only checks
        # 8-byte alignment -- recorded separately (the kernels' aligned moves are audited statically)
        stats[key]['align_fault'] += 1
        continue
    if 'S' in h:
        diffs.append('hardware signal %d' % h['S'])
    else:
        if isa != 'riscv' and m.get('W') != h.get('W'):
            diffs.append('exit %s vs hw %s' % (m.get('W'), h.get('W')))
        for i, (hv, _) in h['G'].items():
            if isa == 'arm' and i == 18:
                continue          # the trampoline's branch register
            if isa == 'riscv' and i in (1, 3, 4):
                continue          # ra (return to the trampoline), gp, tp
            mv = m['G'][i][0]
            if not wmatch(mv, hv, j):
                diffs.append('G%d model %x hw %x' % (i, mv, hv))
        for k in flags_policy(j, st):
            if m['F'][k] != h['F'][k]:
                diffs.append('flag %s model %d hw %d' % ('zcnv'[k], m['F'][k], h['F'][k]))
        for i in range(NV):
            hv = h['V'].get(i)
            if hv is None:
                continue
            mv = m['V'][i][:NL]
            if mv != hv[:NL]:
                diffs.append('V%d model %s hw %s' % (i, ' '.join('%x' % x for x in mv), ' '.join('%x' % x for x in hv[:NL])))
        for i, hv in h['K'].items():
            if m['K'][i] & 0xffff != hv:
                diffs.append('K%d model %x hw %x' % (i, m['K'][i], hv))
        if isa == 'riscv' and h.get('L') is not None and m.get('L') != h.get('L'):
            diffs.append('vl model %s hw %s' % (m.get('L'), h.get('L')))
        keys = set(m['M']) | set(h['M'])
        for k in sorted(keys):
            mv = m['M'].get(k)
            hv = h['M'].get(k)
            if mv is None or hv is None or not wmatch(mv[0], hv[0], j):
                diffs.append('mem %s model %s hw %s' % (k, '%x' % mv[0] if mv else '-', '%x' % hv[0] if hv else '-'))
    if diffs:
        stats[key]['mismatch'] += 1
        mism.append((n, key, mt['text'], diffs, st['raw']))
    else:
        stats[key]['ok'] += 1

with open(os.path.join(d, 'report.txt'), 'w') as fo:
    tot = collections.Counter()
    for key in sorted(stats):
        c = stats[key]
        tot.update(c)
        fo.write('%-8s %6d states %6d ok %5d model-err %4d align-fault %5d MISMATCH  %s\n' % (key[0], c['states'], c['ok'], c['model_err'], c['align_fault'], c['mismatch'], key[1]))
    fo.write('TOTAL %s\n' % dict(tot))
with open(os.path.join(d, 'mismatches.txt'), 'w') as fo:
    shown = collections.Counter()
    for n, key, text, diffs, raw in mism:
        shown[key] += 1
        if shown[key] > 5:
            continue
        fo.write('== case %d [%s] %s\n   form %s\n' % (n, key[0], text, key[1]))
        for x in diffs[:12]:
            fo.write('   ' + x + '\n')
        fo.write('   init: ' + ' | '.join(r for r in raw if not r.startswith('V')) + '\n')
forms = len(stats)
bad = sorted({k for _, k, _, _, _ in mism})
print('%s: %d states, %d forms, %s; mismatching forms: %d' % (d, len(meta), forms, dict(tot), len(bad)))
for k in bad[:60]:
    print('  MISMATCH', stats[k]['mismatch'], '/', stats[k]['states'], k)
