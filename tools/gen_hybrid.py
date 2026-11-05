#!/usr/bin/env python3
"""Generate a hybrid keccak256 core: N SIMD streams (type V, the macros of
tools/gen_core.py) interleaved round by round with M scalar uint64_t streams,
so the scalar ALUs work while the vector pipes are busy.

  gen_hybrid.py --vec N --scal M [--ternlog] [--lazy] [--rc-table]

Streams are named v<i>_ (vector) and s<j>_ (scalar): inputs <p>a0..a7,
outputs <p>o0..o3, all declared by the including file.

--lazy emits the scalar streams with lazy rotations (for AArch64, whose
logical instructions take a rotated second operand for free): every lane is
held as R with true value rotl(R, off), off being known at generation time,
so rho costs nothing and each EOR/BIC absorbs the one rotation it needs. The
only rotations left are the four on the output words. Iota then needs the
round constant pre-rotated by the lane's offset: the including file provides
`const uint64_t* lrc` pointing at KT_LAZY_RC (--rc-table prints it).

Without --lazy the scalar streams use gen_core's emitter with S-prefixed
macros (SXOR, SROL, SCHI, ...), defined by the including file.
"""
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
import gen_core

RHO = gen_core.RHO
M64 = (1 << 64) - 1
RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
      0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
      0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
      0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
      0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]


def rotl(x, n):
    n %= 64
    return ((x << n) | (x >> (64 - n))) & M64 if n else x


def rx(name, k):
    """name rotated left by k (mod 64), as C"""
    k %= 64
    return 'SROL(%s, %d)' % (name, k) if k else name


def lazy(vp, rounds, rc_out=None):
    """Scalar stream with lazy rotations; per-round line lists to rounds."""
    st = [('%sa%d' % (vp, i), 0) for i in range(8)] + [None] * 17
    st[8] = ('0x0000000000000001ULL', 0)
    st[16] = ('0x8000000000000000ULL', 0)
    T = 'uint64_t'
    for r in range(24):
        L = []
        w = L.append
        last = r == 23
        p = '%sr%d_' % (vp, r)
        C = []
        for x in range(5):
            terms = [st[x + 5 * y] for y in range(5) if st[x + 5 * y] is not None]
            base, ob = terms[0]
            cn = '%sc%d' % (p, x)
            w('    %s %s = %s;\n' % (T, cn, base))
            # one EOR per term, kept in this order: SBAR stops the compiler
            # from reassociating two rotated terms into one EOR (which costs
            # a separate ROR)
            for k, (n, o) in enumerate(terms[1:]):
                if k:
                    w('    SBAR(%s);\n' % cn)
                w('    %s ^= %s;\n' % (cn, rx(n, o - ob)))
            C.append(('%sc%d' % (p, x), ob))
        D = []
        for x in range(5):
            (np_, op), (nn, on) = C[(x + 4) % 5], C[(x + 1) % 5]
            w('    %s %sd%d = %s ^ %s;\n' % (T, p, x, np_, rx(nn, on + 1 - op)))
            D.append(('%sd%d' % (p, x), op))
        rows = [0] if last else range(5)
        nst = [None] * 25
        for Y in rows:
            b = []
            for X in range(5):
                xs = (3 * Y + X) % 5
                i = xs + 5 * X
                dn, od = D[xs]
                if st[i] is None:
                    b.append((dn, od + RHO[i]))
                    continue
                an, oa = st[i]
                bn = '%sb%d_%d' % (p, Y, X)
                w('    %s %s = %s ^ %s;\n' % (T, bn, an, rx(dn, od - oa)))
                b.append((bn, oa + RHO[i]))
            for X in (range(4) if last else range(5)):
                (n0, o0), (n1, o1), (n2, o2) = b[X], b[(X + 1) % 5], b[(X + 2) % 5]
                t = '(%s & ~%s)' % (n2, rx(n1, o1 - o2))
                e = '%s ^ %s' % (n0, rx(t, o2 - o0))
                if X == 0 and Y == 0:
                    if rc_out is not None:
                        rc_out.append(rotl(RC[r], -o0))
                    # iota after a barrier, so the constant is not paired
                    # with the rotated term
                    nn = '%sr%d_i' % (vp, r)
                    w('    %s %s = %s;\n    SBAR(%s);\n' % (T, nn, e, nn))
                    e = '%s ^ lrc[%d]' % (nn, r)
                if last:
                    w('    %so%d = %s;\n' % (vp, X, rx('(%s)' % e, o0)))
                else:
                    nn = '%ss%d_%d' % (vp, r, X + 5 * Y)
                    w('    %s %s = %s;\n' % (T, nn, e))
                    nst[X + 5 * Y] = (nn, o0 % 64)
        st = nst
        rounds.append(L)


def interleave(streams):
    """Merge equal-round line lists, spreading each stream evenly."""
    out = []
    for r in range(24):
        ls = [s[r] for s in streams]
        tot = sum(len(l) for l in ls)
        pos = [0] * len(ls)
        for k in range(tot):
            # pick the stream that is furthest behind its proportional share
            j = min((i for i in range(len(ls)) if pos[i] < len(ls[i])),
                    key=lambda i: (pos[i] + 1) / len(ls[i]))
            out.append(ls[j][pos[j]])
            pos[j] += 1
    return out


def main(argv):
    nv = int(argv[argv.index('--vec') + 1]) if '--vec' in argv else 1
    ns = int(argv[argv.index('--scal') + 1]) if '--scal' in argv else 1
    tl = '--ternlog' in argv
    lz = '--lazy' in argv
    o = sys.stdout
    if '--rc-table' in argv:
        rc = []
        lazy('x_', [], rc)
        o.write('/* GENERATED by tools/gen_hybrid.py --rc-table - do not edit.\n'
                ' * Round constants pre-rotated for the lazy-rotation scalar stream. */\n')
        o.write('static const uint64_t KT_LAZY_RC[24] __attribute__((aligned(64))) = {\n')
        for i in range(0, 24, 4):
            o.write('    ' + ' '.join('0x%016xULL,' % v for v in rc[i:i + 4]) + '\n')
        o.write('};\n')
        return
    streams = []
    for i in range(nv):
        rs = []
        gen_core.emit(None, tl, vp='v%d_' % i, rounds=rs)
        streams.append(rs)
    for j in range(ns):
        rs = []
        if lz:
            lazy('s%d_' % j, rs)
        else:
            gen_core.emit(None, False, vp='s%d_' % j, mp='S', typ='uint64_t', rounds=rs)
        streams.append(rs)
    o.write('/* GENERATED by tools/gen_hybrid.py %s - do not edit. */\n' % ' '.join(argv))
    o.write(''.join(interleave(streams)))


if __name__ == '__main__':
    main(sys.argv[1:])
