#!/usr/bin/env python3
"""Generates keccak256_avx512d.inc: the "D-form" Keccak-f[1600] rounds for the
AVX-512 kernels, with all 25 lanes in registers.

The rounds of keccak256_avx512.inc keep theta's C[0..4] and E[0..4] =
rotl(C, 1) in ten registers and fold both into every lane with one
vpternlogq (A ^ C[x-1] ^ E[x+1]); that leaves room for only 20 lanes, so
five lanes live in memory (5 stores, 10 loads per round). Here theta
computes D[x] = C[x-1] ^ rotl(C[x+1], 1) once per column (5 more xors),
needs five registers instead of ten, and every lane stays in a register:
25 lanes + 5 D + 2 chi temporaries = 32. Per round: 95 vector ALU ops
(10 + 25 + 25 vpternlogq/vpxorq, 29 rotations, 1 iota, 5 D xors), 15
register copies, no memory access: 110 macro-ops against 115. That is a
loss for a core bound by its vector ALU pipes (Zen 4, Ice Lake: +5 ALU
ops) and a gain for one bound by the number of macro-ops it can rename or
retire (Zen 5: avx512_x8 and avx512vl_x4 take the same time per round
there, although the ymm round has half the ALU work); the dispatcher's
timing picks.

The including file defines the same names as for keccak256_avx512.inc
(VR, VREG, RC, RCL, RCP, LOOP_CNT, K1, K63, ROT8, ROT56, OUTPUT, and
optionally VHOOK / RHOOK_BEGIN / RHOOK_END).

usage: gen_avx512d.py > keccak256_avx512d.inc
"""
import sys

RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
RC_LANES = lambda y: [((x + 3 * y) % 5) + 5 * x for x in range(5)]  # B[x] of row y comes from lane

out = []
def e(s=""):
    out.append(s)
def ins(op, *args):
    out.append("\t%s\t%s" % (op, ", ".join(args)))
def V(n):
    return "VREG(%d)" % n

def rot(dst, src, r):
    """dst = rotl(src, r)"""
    if r == 8:
        ins("vpshufb", V(dst), V(src), "ROT8")
    elif r == 56:
        ins("vpshufb", V(dst), V(src), "ROT56")
    elif r:
        ins("vprolq", V(dst), V(src), str(r))
    elif dst != src:
        ins("vmovdqa64", V(dst), V(src))

def theta(pos, free):
    """C[x] into free[0..4], D[0..4] derived in place; returns (D regs, free temps)"""
    c = free[:5]
    t0, t1 = free[5], free[6]
    for x in range(5):
        ins("vmovdqa64", V(c[x]), V(pos[x]))
        ins("vpternlogq", V(c[x]), V(pos[x + 5]), V(pos[x + 10]), "0x96")
        ins("vpternlogq", V(c[x]), V(pos[x + 15]), V(pos[x + 20]), "0x96")
        e("\tVHOOK\t\tt")
    # D0 = C4 ^ rotl(C1)  -> t0
    ins("vprolq", V(t0), V(c[1]), "1")
    ins("vpxorq", V(t0), V(t0), V(c[4]))
    # D1 = C0 ^ rotl(C2)  -> t1
    ins("vprolq", V(t1), V(c[2]), "1")
    ins("vpxorq", V(t1), V(t1), V(c[0]))
    e("\tVHOOK\t\tt")
    # D4 = C3 ^ rotl(C0)  -> c0 (C0 no longer needed)
    ins("vprolq", V(c[0]), V(c[0]), "1")
    ins("vpxorq", V(c[0]), V(c[0]), V(c[3]))
    # D2 = C1 ^ rotl(C3)  -> c3
    ins("vprolq", V(c[3]), V(c[3]), "1")
    ins("vpxorq", V(c[3]), V(c[3]), V(c[1]))
    e("\tVHOOK\t\tt")
    # D3 = C2 ^ rotl(C4)  -> c4
    ins("vprolq", V(c[4]), V(c[4]), "1")
    ins("vpxorq", V(c[4]), V(c[4]), V(c[2]))
    e("\tVHOOK\t\tt")
    D = [t0, t1, c[3], c[4], c[0]]
    return D, [c[1], c[2]]

def chi(pos, newpos, y, temps, rc):
    """chi of row y; B[x] in pos[L(y,x)]; outputs to lanes 5y+x; returns the new temps"""
    L = RC_LANES(y)
    b = [pos[i] for i in L]
    t0, t1 = temps
    ins("vmovdqa64", V(t0), V(b[0]))
    ins("vpternlogq", V(t0), V(b[1]), V(b[2]), "0xD2")
    if y == 0:
        e(".if LOOP_RC")
        ins("vpxorq", V(t0), V(t0), "RCL(%s - 1)" % rc)
        e(".else")
        ins("vpxorq", V(t0), V(t0), "RC(%s)" % rc)
        e(".endif")
    e("\tVHOOK\t\tc")
    ins("vmovdqa64", V(t1), V(b[1]))
    ins("vpternlogq", V(t1), V(b[2]), V(b[3]), "0xD2")
    e("\tVHOOK\t\tc")
    ins("vpternlogq", V(b[2]), V(b[3]), V(b[4]), "0xD2")
    e("\tVHOOK\t\tc")
    ins("vpternlogq", V(b[3]), V(b[4]), V(b[0]), "0xD2")
    e("\tVHOOK\t\tc")
    ins("vpternlogq", V(b[4]), V(b[0]), V(b[1]), "0xD2")
    e("\tVHOOK\t\tc")
    newpos[5 * y + 0] = t0
    newpos[5 * y + 1] = t1
    newpos[5 * y + 2] = b[2]
    newpos[5 * y + 3] = b[3]
    newpos[5 * y + 4] = b[4]
    return [b[0], b[1]]

def round_(r, pos, free):
    """one full round r (1..22) on the placement pos / free; returns the new placement"""
    e("\t/* round %d: lanes in %s, free %s */" % (r, " ".join(map(str, pos)), " ".join(map(str, free))))
    D, temps = theta(pos, free)
    newpos = [None] * 25
    for y in range(5):
        L = RC_LANES(y)
        for i in L:
            ins("vpxorq", V(pos[i]), V(pos[i]), V(D[i % 5]))
            rot(pos[i], pos[i], RHO[i])
            e("\tVHOOK\t\tr")
        temps = chi(pos, newpos, y, temps, "%d" % r)
    return newpos, temps + D

def round0():
    """round 0: lanes 0..7 in registers 0..7, lane 8 = K1, lane 16 = K63, the rest zero"""
    e("\t/* round 0 */")
    C0, C1, C2, C3 = 22, 23, 24, 25
    D = [27, 28, 29, 30, 31]
    ins("vpxorq", V(C0), V(0), V(5))
    ins("vpxorq", V(C1), V(1), V(6))
    ins("vpxorq", V(C1), V(C1), "K63")
    ins("vpxorq", V(C2), V(2), V(7))
    ins("vpxorq", V(C3), V(3), "K1")  # C4 is lane 4 itself
    ins("vprolq", V(D[0]), V(C1), "1")
    e("\tVHOOK\t\tt")
    ins("vpxorq", V(D[0]), V(D[0]), V(4))  # D0 = C4 ^ rotl(C1)
    ins("vprolq", V(D[1]), V(C2), "1")
    e("\tVHOOK\t\tt")
    ins("vpxorq", V(D[1]), V(D[1]), V(C0))  # D1 = C0 ^ rotl(C2)
    ins("vprolq", V(D[2]), V(C3), "1")
    e("\tVHOOK\t\tt")
    ins("vpxorq", V(D[2]), V(D[2]), V(C1))  # D2 = C1 ^ rotl(C3)
    ins("vprolq", V(D[3]), V(4), "1")
    ins("vpxorq", V(D[3]), V(D[3]), V(C2))  # D3 = C2 ^ rotl(C4)
    ins("vprolq", V(D[4]), V(C0), "1")
    e("\tVHOOK\t\tt")
    ins("vpxorq", V(D[4]), V(D[4]), V(C3))  # D4 = C3 ^ rotl(C0)
    pos = [None] * 25
    for i in range(8):
        pos[i] = i
    free = list(range(8, 27))  # 8..26 (C0..C3 are dead now)
    newpos = [None] * 25
    for y in range(5):
        L = RC_LANES(y)
        for i in L:
            x = i % 5
            if i < 8:
                ins("vpxorq", V(i), V(i), V(D[x]))
                rot(i, i, RHO[i])
            else:
                f = free.pop(0)
                pos[i] = f
                if i == 8:
                    ins("vpxorq", V(f), V(D[x]), "K1")
                    rot(f, f, RHO[i])
                elif i == 16:
                    ins("vpxorq", V(f), V(D[x]), "K63")
                    rot(f, f, RHO[i])
                else:
                    rot(f, D[x], RHO[i])
            e("\tVHOOK\t\tr")
        temps = [free.pop(0), free.pop(0)]
        back = chi(pos, newpos, y, temps, "0")
        free += back
    assert len(free) == 2, free
    return newpos, free + D

def last_round(pos, free):
    e("\t/* round 23: theta, then row 0, x = 0..3 */")
    D, temps = theta(pos, free)
    L = RC_LANES(0)
    for i in L:
        ins("vpxorq", V(pos[i]), V(pos[i]), V(D[i % 5]))
        rot(pos[i], pos[i], RHO[i])
        e("\tVHOOK\t\tr")
    b = [pos[i] for i in L]
    t1 = temps[1]
    ins("vmovdqa64", V(t1), V(b[0]))
    ins("vpternlogq", V(t1), V(b[1]), V(b[2]), "0xD2")
    ins("vpxorq", V(t1), V(t1), "RC(23)")
    ins("vpternlogq", V(b[1]), V(b[2]), V(b[3]), "0xD2")
    ins("vpternlogq", V(b[2]), V(b[3]), V(b[4]), "0xD2")
    ins("vpternlogq", V(b[3]), V(b[4]), V(b[0]), "0xD2")
    # the digest words to registers 0..3: OUTPUT uses the high registers
    # as scratch (every other register is free now)
    outs = [t1, b[1], b[2], b[3]]
    parallel_move({k: outs[k] for k in range(4)}, [r for r in range(32) if r not in outs])
    e("\tOUTPUT\t\t0, 1, 2, 3")

def parallel_move(src_of, free):
    """emit copies so that register dst receives the value in src_of[dst]
    (dst over the lane registers); free: scratch registers not among the
    sources. Returns the number of copies."""
    pending = dict(src_of)  # dst -> src
    pending = {d: s for d, s in pending.items() if d != s}
    dsts = set(pending)
    n = 0
    while pending:
        # a destination that is not the source of another pending move
        srcs = set(pending.values())
        ready = [d for d in pending if d not in srcs]
        if ready:
            d = ready[0]
            ins("vmovdqa64", V(d), V(pending[d]))
            n += 1
            del pending[d]
            continue
        # only cycles left: break one with a scratch register
        d = next(iter(pending))
        srcs = set(pending.values())
        t = [f for f in free if f not in srcs and f not in dsts][0]
        ins("vmovdqa64", V(t), V(d))  # save the value of d
        n += 1
        # whoever wanted d's value now takes it from t
        for k in pending:
            if pending[k] == d:
                pending[k] = t
    return n

def main():
    e("/* Generated by gen_avx512d.py: do not edit. See that file for the design. */")
    e("#ifndef VHOOK_DEFINED")
    e(".macro VHOOK kind")
    e(".endm")
    e("#endif")
    e("#ifndef RHOOK_DEFINED")
    e(".macro RHOOK_BEGIN k")
    e(".endm")
    e(".macro RHOOK_END")
    e(".endm")
    e("#endif")
    e(".set LOOP_RC, 0")
    e()
    # unrolled
    e("/* the whole permutation, unrolled */")
    e(".macro KECCAK_F_D")
    e("\tRHOOK_BEGIN\t0")
    pos, free = round0()
    e("\tRHOOK_END")
    for r in range(1, 23):
        e("\tRHOOK_BEGIN\t%d" % r)
        pos, free = round_(r, pos, free)
        e("\tRHOOK_END")
    e("\tRHOOK_BEGIN\t23")
    last_round(pos, free)
    e("\tRHOOK_END")
    e(".endm")
    e()
    # loop: round 0, then 5 x (rounds 1..4 body + restore), rounds 21, 22, 23
    e("/* the same with rounds 1..20 as five iterations of a four-round body;")
    e(" * the copies after the body restore the lane placement of its start */")
    e(".macro KECCAK_F_D_LOOP")
    e("\tlea\t\tRCP, [rip + .LKECCAK_RC]")
    e("\tRHOOK_BEGIN\t0")
    pos, free = round0()
    e("\tRHOOK_END")
    e("\tadd\t\tRCP, 8")
    e("\tmov\t\tqword ptr [LOOP_CNT], 5")
    e("\t.set\t\tLOOP_RC, 1")
    e("#ifdef KT_LOOP_ALIGN")
    e(".p2align 6")
    e("#endif")
    e("1:")
    entry_pos, entry_free = list(pos), list(free)
    for k in range(1, 5):
        e("\tRHOOK_BEGIN\t%d" % k)
        pos, free = round_(k, pos, free)
        e("\tRHOOK_END")
    # restore: lane i is in pos[i], must go to entry_pos[i]
    src_of = {entry_pos[i]: pos[i] for i in range(25)}
    e("\t/* restore the entry placement */")
    n = parallel_move(src_of, free)
    e("\t/* %d copies */" % n)
    pos, free = entry_pos, entry_free
    e("\tadd\t\tRCP, 32")
    e("\tdec\t\tqword ptr [LOOP_CNT]")
    e("\tjnz\t\t1b")
    e("\t.set\t\tLOOP_RC, 0")
    for r in (21, 22):
        e("\tRHOOK_BEGIN\t%d" % r)
        pos, free = round_(r, pos, free)
        e("\tRHOOK_END")
    e("\tRHOOK_BEGIN\t23")
    last_round(pos, free)
    e("\tRHOOK_END")
    e(".endm")
    sys.stdout.write("\n".join(out) + "\n")

main()
