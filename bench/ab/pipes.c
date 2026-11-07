/* Vector-pipe microbenchmarks for the AVX-512 kernels (throwaway, bench
 * branch only): measures the core clock (dependent add chain), the
 * throughput of the round's instructions alone and in the round's mix,
 * and the cycles per round of the kernels, to compare against the
 * uops.info pipe model (Zen 4: zmm ops double-pumped on 4 pipes, vprolq on
 * FP0/1 only).
 *   build: cc -O2 -mavx512f -mavx512vl -mavx512bw -mbmi -mbmi2 pipes.c -Isrc -lkeccaktree
 *   run:   pipes            (needs AVX-512F + VL)
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include "keccaktree.h"

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

/* AT&T syntax: op src2, src1, dst */
#define TL(V, d, a, b)   "vpternlogq $0x96, %%" V #b ", %%" V #a ", %%" V #d "\n\t"
#define TLD(V, d, a, b)  "vpternlogq $0xD2, %%" V #b ", %%" V #a ", %%" V #d "\n\t"
#define TLM(V, d, a, off) "vpternlogq $0x96, " #off "(%1), %%" V #a ", %%" V #d "\n\t"
#define XOR(V, d, a, b)  "vpxorq %%" V #b ", %%" V #a ", %%" V #d "\n\t"
#define ANDN(V, d, a, b) "vpandnq %%" V #b ", %%" V #a ", %%" V #d "\n\t"
#define ROL(V, d, a, r)  "vprolq $" #r ", %%" V #a ", %%" V #d "\n\t"
#define SHUF(V, d, a, c) "vpshufb %%" V #c ", %%" V #a ", %%" V #d "\n\t"
#define MSH(V, d, c, a)  "vpmultishiftqb %%" V #a ", %%" V #c ", %%" V #d "\n\t"
#define MOV(V, d, a)     "vmovdqa64 %%" V #a ", %%" V #d "\n\t"
#define LD(V, d, off)    "vmovdqa64 " #off "(%1), %%" V #d "\n\t"
#define ST(V, off, a)    "vmovdqa64 %%" V #a ", " #off "(%1)\n\t"

#define X24(M, V) M(V, 0) M(V, 1) M(V, 2) M(V, 3) M(V, 4) M(V, 5) M(V, 6) M(V, 7) M(V, 8) M(V, 9) M(V, 10) M(V, 11) \
    M(V, 12) M(V, 13) M(V, 14) M(V, 15) M(V, 16) M(V, 17) M(V, 18) M(V, 19) M(V, 20) M(V, 21) M(V, 22) M(V, 23)
#define M_TL(V, i) TL(V, i, 24, 25)
#define M_TLD(V, i) TLD(V, i, 24, 25)
#define M_TLM(V, i) TLM(V, i, 24, 64)
#define M_XOR(V, i) XOR(V, i, i, 24)
#define M_ANDN(V, i) ANDN(V, i, 24, 25)
#define M_ROL(V, i) ROL(V, i, i, 7)
#define M_SHUF(V, i) SHUF(V, i, i, 24)
#define M_MSH(V, i) MSH(V, i, 24, i)
#define M_MOV(V, i) MOV(V, i, 24)
#define M_LD(V, i) LD(V, i, 0)
#define M_ST(V, i) ST(V, 0, i)

/* scalar hooks (hybrid test): GA/GB/GC map a lane index to general registers
 * so that no long dependency chain forms */
#define G_0 "%%r8"
#define G_1 "%%r9"
#define G_2 "%%r10"
#define G_3 "%%r11"
#define G_4 "%%r12"
#define G_5 "%%r13"
#define G_6 "%%r14"
#define G_7 "%%r15"
#define G_8 "%%rax"
#define G_9 "%%rbx"
#define G_10 "%%rcx"
#define G_11 "%%rdx"
#define G_12 "%%rcx"
#define G_13 "%%rdx"
#define G_14 "%%r8"
#define G_15 "%%r9"
#define G_16 "%%r10"
#define G_17 "%%r11"
#define G_18 "%%r12"
#define G_19 "%%r13"
#define G_20 "%%r14"
#define G_21 "%%r15"
#define G_22 "%%rax"
#define G_23 "%%rbx"
#define G_24 "%%rcx"
#define G_25 "%%rdx"
#define G_26 "%%rcx"
#define G_27 "%%rdx"
#define G_28 "%%r8"
#define G_29 "%%r9"
#define GA(d) G_##d
#define GB_(d) G_##d
#define GB(d) GB2(d)
/* a second mapping: shifted by 5 */
#define GB2(d) GBX_##d
#define GBX_0 G_5
#define GBX_1 G_6
#define GBX_2 G_7
#define GBX_3 G_8
#define GBX_4 G_9
#define GBX_5 G_10
#define GBX_6 G_11
#define GBX_7 G_12
#define GBX_8 G_13
#define GBX_9 G_0
#define GBX_10 G_1
#define GBX_11 G_2
#define GBX_12 G_3
#define GBX_13 G_4
#define GBX_14 G_5
#define GBX_15 G_6
#define GBX_16 G_7
#define GBX_17 G_8
#define GBX_18 G_9
#define GBX_19 G_10
#define GBX_20 G_11
#define GBX_21 G_12
#define GBX_22 G_13
#define GBX_23 G_0
#define GBX_24 G_1
#define GBX_25 G_2
#define GBX_26 G_3
#define GBX_27 G_4
#define GBX_28 G_5
#define GBX_29 G_6
/* scalar snippets: SA = rorx from memory + xor (2 ALU), SB = andn + store,
 * SR = load-xor (1 macro-op) */
#define SA(d) "rorx $63, 16(%1), " GA(d) "\n\txorq " GB(d) ", " GA(d) "\n\t"
#define SB(d) "andn " GA(d) ", " GB(d) ", " GB(d) "\n\tmovq " GB(d) ", 256(%1)\n\t"
#define SR(d) "xorq 24(%1), " GB(d) "\n\t"
#define N1(d)
#define N2(d)

/* the round's 90 ALU ops in the kernel's order, independent across
 * registers (dests 0..21, sources 22..31); HT/HC/HR: hooks after a theta/rho
 * ternlog, a chi ternlog, a rotation */
#define THETA_C(V, d, HT, HR) TL(V, d, 22, 23) HT(d) TL(V, d, 24, 25) HT(d) ROL(V, d, d, 1) HR(d)
#define RHO(V, d, r, HT, HR) TL(V, d, 26, 27) HT(d) ROL(V, d, d, r) HR(d)
#define RHOS(V, d, c, HT, HR) TL(V, d, 26, 27) HT(d) SHUF(V, d, d, c) HR(d)
#define CHI5(V, a, b, c, d, e, HC) TLD(V, a, b, c) HC(a) TLD(V, b, c, d) HC(b) TLD(V, c, d, e) HC(c) TLD(V, d, e, a) HC(d) TLD(V, e, a, b) HC(e)
/* chi with the kernel's two copies into temporaries 28, 29 */
#define CHI5M(V, a, b, c, d, e, HC) MOV(V, 28, a) TLD(V, 28, b, c) HC(a) MOV(V, 29, b) TLD(V, 29, c, d) HC(b) \
    TLD(V, c, d, e) HC(c) TLD(V, d, e, a) HC(d) TLD(V, e, a, b) HC(e)
#define MIX(V, CHI, LDM, STM, HT, HC, HR) \
    LDM(V, 0, 0) THETA_C(V, 0, HT, HR) LDM(V, 1, 64) THETA_C(V, 1, HT, HR) LDM(V, 2, 128) THETA_C(V, 2, HT, HR) \
    LDM(V, 3, 192) THETA_C(V, 3, HT, HR) LDM(V, 4, 256) THETA_C(V, 4, HT, HR) \
    LDM(V, 5, 320) TL(V, 5, 0, 1) HT(5) RHO(V, 6, 44, HT, HR) RHO(V, 7, 43, HT, HR) RHO(V, 8, 21, HT, HR) RHO(V, 9, 14, HT, HR) \
    CHI(V, 5, 6, 7, 8, 9, HC) STM(V, 0, 5) STM(V, 64, 6) STM(V, 128, 7) STM(V, 192, 8) STM(V, 256, 9) \
    LDM(V, 10, 384) RHO(V, 10, 28, HT, HR) RHO(V, 11, 20, HT, HR) RHO(V, 12, 3, HT, HR) RHO(V, 13, 45, HT, HR) RHO(V, 14, 61, HT, HR) \
    CHI(V, 10, 11, 12, 13, 14, HC) \
    LDM(V, 15, 448) RHO(V, 15, 1, HT, HR) RHO(V, 16, 6, HT, HR) RHO(V, 17, 25, HT, HR) RHOS(V, 18, 30, HT, HR) RHO(V, 19, 18, HT, HR) \
    CHI(V, 15, 16, 17, 18, 19, HC) \
    LDM(V, 20, 512) RHO(V, 20, 27, HT, HR) RHO(V, 21, 36, HT, HR) RHO(V, 0, 10, HT, HR) RHO(V, 1, 15, HT, HR) RHOS(V, 2, 31, HT, HR) \
    CHI(V, 20, 21, 0, 1, 2, HC) \
    LDM(V, 3, 576) RHO(V, 3, 62, HT, HR) RHO(V, 4, 55, HT, HR) RHO(V, 5, 39, HT, HR) RHO(V, 6, 41, HT, HR) RHO(V, 7, 2, HT, HR) \
    CHI(V, 3, 4, 5, 6, 7, HC) \
    XOR(V, 8, 8, 30)
#define NOLD(V, d, off)
#define NOST(V, off, a)

#define CLOBBER_V "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", \
    "xmm12", "xmm13", "xmm14", "xmm15", "xmm16", "xmm17", "xmm18", "xmm19", "xmm20", "xmm21", "xmm22", "xmm23", \
    "xmm24", "xmm25", "xmm26", "xmm27", "xmm28", "xmm29", "xmm30", "xmm31"
#define CLOBBER_G "rax", "rbx", "rcx", "rdx", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"

#define DEF(name, ops, body) \
    static void name##_f(long n, void* buf) { \
        __asm__ volatile("1:\n\t" body "dec %0\n\tjnz 1b" : "+r"(n) : "r"(buf) : "memory", "cc", CLOBBER_V, CLOBBER_G); \
    } \
    static const int name##_ops = ops;

/* clock: a dependent imul chain is 3 cycles per imul on Zen 3/4/5 and on
 * Intel (a dependent add-immediate chain is collapsed by recent cores) */
DEF(clk, 32, "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t"
    "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t"
    "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t"
    "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t"
    "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t"
    "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t"
    "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t"
    "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t" "imulq %%rax, %%rax\n\t")
DEF(tl_z, 24, X24(M_TL, "zmm"))
DEF(tl_y, 24, X24(M_TL, "ymm"))
DEF(tld_z, 24, X24(M_TLD, "zmm"))
DEF(tlm_z, 24, X24(M_TLM, "zmm"))
DEF(xor_z, 24, X24(M_XOR, "zmm"))
DEF(xor_y, 24, X24(M_XOR, "ymm"))
DEF(andn_z, 24, X24(M_ANDN, "zmm"))
DEF(rol_z, 24, X24(M_ROL, "zmm"))
DEF(rol_y, 24, X24(M_ROL, "ymm"))
DEF(shuf_z, 24, X24(M_SHUF, "zmm"))
DEF(shuf_y, 24, X24(M_SHUF, "ymm"))
DEF(msh_z, 24, X24(M_MSH, "zmm"))
DEF(mov_z, 24, X24(M_MOV, "zmm"))
DEF(ld_z, 24, X24(M_LD, "zmm"))
DEF(st_z, 24, X24(M_ST, "zmm"))
/* 2 ternlog : 1 rotate, the round's ratio, alternating */
DEF(tlrol_z, 24, TL("zmm", 0, 24, 25) TL("zmm", 1, 24, 25) ROL("zmm", 2, 2, 7) TL("zmm", 3, 24, 25) TL("zmm", 4, 24, 25) ROL("zmm", 5, 5, 7)
    TL("zmm", 6, 24, 25) TL("zmm", 7, 24, 25) ROL("zmm", 8, 8, 7) TL("zmm", 9, 24, 25) TL("zmm", 10, 24, 25) ROL("zmm", 11, 11, 7)
    TL("zmm", 12, 24, 25) TL("zmm", 13, 24, 25) ROL("zmm", 14, 14, 7) TL("zmm", 15, 24, 25) TL("zmm", 16, 24, 25) ROL("zmm", 17, 17, 7)
    TL("zmm", 18, 24, 25) TL("zmm", 19, 24, 25) ROL("zmm", 20, 20, 7) TL("zmm", 21, 24, 25) TL("zmm", 22, 24, 25) ROL("zmm", 23, 23, 7))
DEF(xorrol_z, 24, XOR("zmm", 0, 0, 25) XOR("zmm", 1, 1, 25) ROL("zmm", 2, 2, 7) XOR("zmm", 3, 3, 25) XOR("zmm", 4, 4, 25) ROL("zmm", 5, 5, 7)
    XOR("zmm", 6, 6, 25) XOR("zmm", 7, 7, 25) ROL("zmm", 8, 8, 7) XOR("zmm", 9, 9, 25) XOR("zmm", 10, 10, 25) ROL("zmm", 11, 11, 7)
    XOR("zmm", 12, 12, 25) XOR("zmm", 13, 13, 25) ROL("zmm", 14, 14, 7) XOR("zmm", 15, 15, 25) XOR("zmm", 16, 16, 25) ROL("zmm", 17, 17, 7)
    XOR("zmm", 18, 18, 25) XOR("zmm", 19, 19, 25) ROL("zmm", 20, 20, 7) XOR("zmm", 21, 21, 25) XOR("zmm", 22, 22, 25) ROL("zmm", 23, 23, 7))
/* the round: 90 ALU ops (mix), + 10 copies + 10 loads + 5 stores (mixm),
 * + ~150 scalar macro-ops (hyb), + ~150 scalar ops at ymm width */
DEF(mix_z, 90, MIX("zmm", CHI5, NOLD, NOST, N1, N1, N1))
DEF(mixm_z, 115, MIX("zmm", CHI5M, LD, ST, N1, N1, N1))
DEF(mix_y, 90, MIX("ymm", CHI5, NOLD, NOST, N1, N1, N1))
DEF(mixm_y, 115, MIX("ymm", CHI5M, LD, ST, N1, N1, N1))
/* hooks: 35 theta/rho ternlogs x SA (2 ops) + 25 chi x SB (2) + 29 rotations x SR (1) = 149 scalar macro-ops */
DEF(hyb_z, 264, MIX("zmm", CHI5M, LD, ST, SA, SB, SR))
DEF(hyb_y, 264, MIX("ymm", CHI5M, LD, ST, SA, SB, SR))
/* the scalar ops alone, with a trivial vector op in between (the hooks need a lane index) */
#define NOP_V(V, d, a, b)
DEF(sc, 149, SA(0) SA(1) SA(2) SA(3) SA(4) SA(5) SA(6) SA(7) SA(8) SA(9) SA(10) SA(11) SA(12) SA(13) SA(14) SA(15) SA(16) SA(17)
    SA(18) SA(19) SA(20) SA(21) SA(22) SA(23) SA(24) SA(25) SA(26) SA(27) SA(28) SA(29) SA(0) SA(1) SA(2) SA(3) SA(4)
    SB(5) SB(6) SB(7) SB(8) SB(9) SB(10) SB(11) SB(12) SB(13) SB(14) SB(15) SB(16) SB(17) SB(18) SB(19) SB(20) SB(21) SB(22)
    SB(23) SB(24) SB(25) SB(26) SB(27) SB(28) SB(29)
    SR(0) SR(1) SR(2) SR(3) SR(4) SR(5) SR(6) SR(7) SR(8) SR(9) SR(10) SR(11) SR(12) SR(13) SR(14) SR(15) SR(16) SR(17) SR(18)
    SR(19) SR(20) SR(21) SR(22) SR(23) SR(24) SR(25) SR(26) SR(27) SR(28) SR(29))


/* the same 90 ops, batched by five: a row's five theta/rho ternlogs, then
 * its five rotations (dependent at distance 5), then chi */
#define THETA5(V) TL(V, 0, 22, 23) TL(V, 1, 22, 23) TL(V, 2, 22, 23) TL(V, 3, 22, 23) TL(V, 4, 22, 23) \
    TL(V, 0, 24, 25) TL(V, 1, 24, 25) TL(V, 2, 24, 25) TL(V, 3, 24, 25) TL(V, 4, 24, 25) \
    ROL(V, 0, 0, 1) ROL(V, 1, 1, 1) ROL(V, 2, 2, 1) ROL(V, 3, 3, 1) ROL(V, 4, 4, 1)
#define ROW5(V, a, b, c, d, e, ra, rb, rc, rd, re) TL(V, a, 26, 27) TL(V, b, 26, 27) TL(V, c, 26, 27) TL(V, d, 26, 27) TL(V, e, 26, 27) \
    ROL(V, a, a, ra) ROL(V, b, b, rb) ROL(V, c, c, rc) ROL(V, d, d, rd) ROL(V, e, e, re) CHI5(V, a, b, c, d, e, N1)
#define ROW5S(V, a, b, c, d, e, ra, rb, rc, rd, sh) TL(V, a, 26, 27) TL(V, b, 26, 27) TL(V, c, 26, 27) TL(V, d, 26, 27) TL(V, e, 26, 27) \
    ROL(V, a, a, ra) ROL(V, b, b, rb) ROL(V, c, c, rc) ROL(V, d, d, rd) SHUF(V, e, e, sh) CHI5(V, a, b, c, d, e, N1)
#define MIX_B5(V) THETA5(V) TL(V, 5, 0, 1) TL(V, 6, 26, 27) TL(V, 7, 26, 27) TL(V, 8, 26, 27) TL(V, 9, 26, 27) \
    ROL(V, 6, 6, 44) ROL(V, 7, 7, 43) ROL(V, 8, 8, 21) ROL(V, 9, 9, 14) CHI5(V, 5, 6, 7, 8, 9, N1) \
    ROW5(V, 10, 11, 12, 13, 14, 28, 20, 3, 45, 61) ROW5S(V, 15, 16, 17, 18, 19, 1, 6, 25, 18, 30) \
    ROW5S(V, 20, 21, 0, 1, 2, 27, 36, 10, 15, 31) ROW5(V, 3, 4, 5, 6, 7, 62, 55, 39, 41, 2) XOR(V, 8, 8, 30)
DEF(mixb5_z, 90, MIX_B5("zmm"))
DEF(mixb5_y, 90, MIX_B5("ymm"))
/* all theta/rho ternlogs of the round first, then the 24 rotations, then
 * the five chi rows */
#define MIX_ALL(V) TL(V, 0, 22, 23) TL(V, 1, 22, 23) TL(V, 2, 22, 23) TL(V, 3, 22, 23) TL(V, 4, 22, 23) \
    TL(V, 0, 24, 25) TL(V, 1, 24, 25) TL(V, 2, 24, 25) TL(V, 3, 24, 25) TL(V, 4, 24, 25) \
    ROL(V, 0, 0, 1) ROL(V, 1, 1, 1) ROL(V, 2, 2, 1) ROL(V, 3, 3, 1) ROL(V, 4, 4, 1) \
    TL(V, 5, 0, 1) TL(V, 6, 26, 27) TL(V, 7, 26, 27) TL(V, 8, 26, 27) TL(V, 9, 26, 27) \
    TL(V, 10, 26, 27) TL(V, 11, 26, 27) TL(V, 12, 26, 27) TL(V, 13, 26, 27) TL(V, 14, 26, 27) \
    TL(V, 15, 26, 27) TL(V, 16, 26, 27) TL(V, 17, 26, 27) TL(V, 18, 26, 27) TL(V, 19, 26, 27) \
    TL(V, 20, 26, 27) TL(V, 21, 26, 27) TL(V, 0, 26, 27) TL(V, 1, 26, 27) TL(V, 2, 26, 27) \
    ROL(V, 6, 6, 44) ROL(V, 7, 7, 43) ROL(V, 8, 8, 21) ROL(V, 9, 9, 14) \
    ROL(V, 10, 10, 28) ROL(V, 11, 11, 20) ROL(V, 12, 12, 3) ROL(V, 13, 13, 45) ROL(V, 14, 14, 61) \
    ROL(V, 15, 15, 1) ROL(V, 16, 16, 6) ROL(V, 17, 17, 25) SHUF(V, 18, 18, 30) ROL(V, 19, 19, 18) \
    ROL(V, 20, 20, 27) ROL(V, 21, 21, 36) ROL(V, 0, 0, 10) ROL(V, 1, 1, 15) SHUF(V, 2, 2, 31) \
    CHI5(V, 5, 6, 7, 8, 9, N1) CHI5(V, 10, 11, 12, 13, 14, N1) CHI5(V, 15, 16, 17, 18, 19, N1) CHI5(V, 20, 21, 0, 1, 2, N1) \
    TL(V, 3, 26, 27) TL(V, 4, 26, 27) TL(V, 5, 26, 27) TL(V, 6, 26, 27) TL(V, 7, 26, 27) \
    ROL(V, 3, 3, 62) ROL(V, 4, 4, 55) ROL(V, 5, 5, 39) ROL(V, 6, 6, 41) ROL(V, 7, 7, 2) \
    CHI5(V, 3, 4, 5, 6, 7, N1) XOR(V, 8, 8, 30)
DEF(mixall_z, 90, MIX_ALL("zmm"))
DEF(mixall_y, 90, MIX_ALL("ymm"))
/* the kernel order with every rotation independent of the ternlog before
 * it (source register 29) */
#define ROLI(V, d, a, r) ROL(V, d, 29, r)
#define SHUFI(V, d, a, c) SHUF(V, d, 29, c)
#define RHOI(V, d, r, HT, HR) TL(V, d, 26, 27) ROLI(V, d, d, r)
#define RHOSI(V, d, c, HT, HR) TL(V, d, 26, 27) SHUFI(V, d, d, c)
#define THETA_CI(V, d, HT, HR) TL(V, d, 22, 23) TL(V, d, 24, 25) ROLI(V, d, d, 1)
#define MIX_IND(V) \
    THETA_CI(V, 0, N1, N1) THETA_CI(V, 1, N1, N1) THETA_CI(V, 2, N1, N1) THETA_CI(V, 3, N1, N1) THETA_CI(V, 4, N1, N1) \
    TL(V, 5, 0, 1) RHOI(V, 6, 44, N1, N1) RHOI(V, 7, 43, N1, N1) RHOI(V, 8, 21, N1, N1) RHOI(V, 9, 14, N1, N1) CHI5(V, 5, 6, 7, 8, 9, N1) \
    RHOI(V, 10, 28, N1, N1) RHOI(V, 11, 20, N1, N1) RHOI(V, 12, 3, N1, N1) RHOI(V, 13, 45, N1, N1) RHOI(V, 14, 61, N1, N1) CHI5(V, 10, 11, 12, 13, 14, N1) \
    RHOI(V, 15, 1, N1, N1) RHOI(V, 16, 6, N1, N1) RHOI(V, 17, 25, N1, N1) RHOSI(V, 18, 30, N1, N1) RHOI(V, 19, 18, N1, N1) CHI5(V, 15, 16, 17, 18, 19, N1) \
    RHOI(V, 20, 27, N1, N1) RHOI(V, 21, 36, N1, N1) RHOI(V, 0, 10, N1, N1) RHOI(V, 1, 15, N1, N1) RHOSI(V, 2, 31, N1, N1) CHI5(V, 20, 21, 0, 1, 2, N1) \
    RHOI(V, 3, 62, N1, N1) RHOI(V, 4, 55, N1, N1) RHOI(V, 5, 39, N1, N1) RHOI(V, 6, 41, N1, N1) RHOI(V, 7, 2, N1, N1) CHI5(V, 3, 4, 5, 6, 7, N1) \
    XOR(V, 8, 8, 30)
DEF(mixind_z, 90, MIX_IND("zmm"))
/* the kernel order with 2-source xors in place of the ternlogs */
#define TLX(V, d, a, b) XOR(V, d, d, a)
#define TLDX(V, d, a, b) XOR(V, d, d, a)
#define THETA_CX(V, d, HT, HR) TLX(V, d, 22, 23) TLX(V, d, 24, 25) ROL(V, d, d, 1)
#define RHOX(V, d, r, HT, HR) TLX(V, d, 26, 27) ROL(V, d, d, r)
#define RHOSX(V, d, c, HT, HR) TLX(V, d, 26, 27) SHUF(V, d, d, c)
#define CHI5X(V, a, b, c, d, e, HC) TLDX(V, a, b, c) TLDX(V, b, c, d) TLDX(V, c, d, e) TLDX(V, d, e, a) TLDX(V, e, a, b)
#define MIX_X(V) \
    THETA_CX(V, 0, N1, N1) THETA_CX(V, 1, N1, N1) THETA_CX(V, 2, N1, N1) THETA_CX(V, 3, N1, N1) THETA_CX(V, 4, N1, N1) \
    TLX(V, 5, 0, 1) RHOX(V, 6, 44, N1, N1) RHOX(V, 7, 43, N1, N1) RHOX(V, 8, 21, N1, N1) RHOX(V, 9, 14, N1, N1) CHI5X(V, 5, 6, 7, 8, 9, N1) \
    RHOX(V, 10, 28, N1, N1) RHOX(V, 11, 20, N1, N1) RHOX(V, 12, 3, N1, N1) RHOX(V, 13, 45, N1, N1) RHOX(V, 14, 61, N1, N1) CHI5X(V, 10, 11, 12, 13, 14, N1) \
    RHOX(V, 15, 1, N1, N1) RHOX(V, 16, 6, N1, N1) RHOX(V, 17, 25, N1, N1) RHOSX(V, 18, 30, N1, N1) RHOX(V, 19, 18, N1, N1) CHI5X(V, 15, 16, 17, 18, 19, N1) \
    RHOX(V, 20, 27, N1, N1) RHOX(V, 21, 36, N1, N1) RHOX(V, 0, 10, N1, N1) RHOX(V, 1, 15, N1, N1) RHOSX(V, 2, 31, N1, N1) CHI5X(V, 20, 21, 0, 1, 2, N1) \
    RHOX(V, 3, 62, N1, N1) RHOX(V, 4, 55, N1, N1) RHOX(V, 5, 39, N1, N1) RHOX(V, 6, 41, N1, N1) RHOX(V, 7, 2, N1, N1) CHI5X(V, 3, 4, 5, 6, 7, N1) \
    XOR(V, 8, 8, 30)
DEF(mixx_z, 90, MIX_X("zmm"))
/* dependent ternlog -> rotate pairs at the 2:1 ratio, and 1:1 */
DEF(tlroldep_z, 24, TL("zmm", 0, 24, 25) TL("zmm", 1, 24, 25) ROL("zmm", 1, 1, 7) TL("zmm", 2, 24, 25) TL("zmm", 3, 24, 25) ROL("zmm", 3, 3, 7)
    TL("zmm", 4, 24, 25) TL("zmm", 5, 24, 25) ROL("zmm", 5, 5, 7) TL("zmm", 6, 24, 25) TL("zmm", 7, 24, 25) ROL("zmm", 7, 7, 7)
    TL("zmm", 8, 24, 25) TL("zmm", 9, 24, 25) ROL("zmm", 9, 9, 7) TL("zmm", 10, 24, 25) TL("zmm", 11, 24, 25) ROL("zmm", 11, 11, 7)
    TL("zmm", 12, 24, 25) TL("zmm", 13, 24, 25) ROL("zmm", 13, 13, 7) TL("zmm", 14, 24, 25) TL("zmm", 15, 24, 25) ROL("zmm", 15, 15, 7))
DEF(tlrol11_z, 24, TL("zmm", 0, 24, 25) ROL("zmm", 1, 1, 7) TL("zmm", 2, 24, 25) ROL("zmm", 3, 3, 7) TL("zmm", 4, 24, 25) ROL("zmm", 5, 5, 7)
    TL("zmm", 6, 24, 25) ROL("zmm", 7, 7, 7) TL("zmm", 8, 24, 25) ROL("zmm", 9, 9, 7) TL("zmm", 10, 24, 25) ROL("zmm", 11, 11, 7)
    TL("zmm", 12, 24, 25) ROL("zmm", 13, 13, 7) TL("zmm", 14, 24, 25) ROL("zmm", 15, 15, 7) TL("zmm", 16, 24, 25) ROL("zmm", 17, 17, 7)
    TL("zmm", 18, 24, 25) ROL("zmm", 19, 19, 7) TL("zmm", 20, 24, 25) ROL("zmm", 21, 21, 7) TL("zmm", 22, 24, 25) ROL("zmm", 23, 23, 7))
DEF(tlrol11dep_z, 24, TL("zmm", 0, 24, 25) ROL("zmm", 0, 0, 7) TL("zmm", 2, 24, 25) ROL("zmm", 2, 2, 7) TL("zmm", 4, 24, 25) ROL("zmm", 4, 4, 7)
    TL("zmm", 6, 24, 25) ROL("zmm", 6, 6, 7) TL("zmm", 8, 24, 25) ROL("zmm", 8, 8, 7) TL("zmm", 10, 24, 25) ROL("zmm", 10, 10, 7)
    TL("zmm", 12, 24, 25) ROL("zmm", 12, 12, 7) TL("zmm", 14, 24, 25) ROL("zmm", 14, 14, 7) TL("zmm", 16, 24, 25) ROL("zmm", 16, 16, 7)
    TL("zmm", 18, 24, 25) ROL("zmm", 18, 18, 7) TL("zmm", 20, 24, 25) ROL("zmm", 20, 20, 7) TL("zmm", 22, 24, 25) ROL("zmm", 22, 22, 7))
/* chi alone: five rows of five dependent ternlogs */
DEF(chi_z, 25, CHI5("zmm", 0, 1, 2, 3, 4, N1) CHI5("zmm", 5, 6, 7, 8, 9, N1) CHI5("zmm", 10, 11, 12, 13, 14, N1) CHI5("zmm", 15, 16, 17, 18, 19, N1) CHI5("zmm", 20, 21, 22, 23, 24, N1))

/* shifts: on Zen 4 vpsllq/vpsrlq zmm run on FP2/3 (uops.info) while vprolq
 * runs on FP0/1: a rotate as sll + srl + or moves work off FP0/1 */
#define SLL(V, d, a, r) "vpsllq $" #r ", %%" V #a ", %%" V #d "\n\t"
#define SRL(V, d, a, r) "vpsrlq $" #r ", %%" V #a ", %%" V #d "\n\t"
#define OR(V, d, a, b)  "vporq %%" V #b ", %%" V #a ", %%" V #d "\n\t"
#define M_SLL(V, i) SLL(V, i, i, 7)
#define M_SRL(V, i) SRL(V, i, i, 7)
DEF(sll_z, 24, X24(M_SLL, "zmm"))
DEF(srl_z, 24, X24(M_SRL, "zmm"))
DEF(rolsll_z, 24, ROL("zmm", 0, 0, 7) SLL("zmm", 1, 1, 7) ROL("zmm", 2, 2, 7) SLL("zmm", 3, 3, 7) ROL("zmm", 4, 4, 7) SLL("zmm", 5, 5, 7)
    ROL("zmm", 6, 6, 7) SLL("zmm", 7, 7, 7) ROL("zmm", 8, 8, 7) SLL("zmm", 9, 9, 7) ROL("zmm", 10, 10, 7) SLL("zmm", 11, 11, 7)
    ROL("zmm", 12, 12, 7) SLL("zmm", 13, 13, 7) ROL("zmm", 14, 14, 7) SLL("zmm", 15, 15, 7) ROL("zmm", 16, 16, 7) SLL("zmm", 17, 17, 7)
    ROL("zmm", 18, 18, 7) SLL("zmm", 19, 19, 7) ROL("zmm", 20, 20, 7) SLL("zmm", 21, 21, 7) ROL("zmm", 22, 22, 7) SLL("zmm", 23, 23, 7))
/* rotate as shifts: t = a >> (64-r); a <<= r; a |= t  (t: register 28/29) */
#define ROLS(V, d, a, r, rr, t) SRL(V, t, a, rr) SLL(V, d, a, r) OR(V, d, d, t)
/* the kernel mix with the five theta rotations and four rho rotations (one
 * per row 1..4) as shift pairs: 18 vprolq + 2 vpshufb stay on FP0/1 */
#define THETA_CS(V, d, t) TL(V, d, 22, 23) TL(V, d, 24, 25) ROLS(V, d, d, 1, 63, t)
#define RHOS2(V, d, r, rr, t) TL(V, d, 26, 27) ROLS(V, d, d, r, rr, t)
#define MIX_S(V) \
    THETA_CS(V, 0, 28) THETA_CS(V, 1, 29) THETA_CS(V, 2, 28) THETA_CS(V, 3, 29) THETA_CS(V, 4, 28) \
    TL(V, 5, 0, 1) RHO(V, 6, 44, N1, N1) RHO(V, 7, 43, N1, N1) RHO(V, 8, 21, N1, N1) RHO(V, 9, 14, N1, N1) CHI5(V, 5, 6, 7, 8, 9, N1) \
    RHOS2(V, 10, 28, 36, 29) RHO(V, 11, 20, N1, N1) RHO(V, 12, 3, N1, N1) RHO(V, 13, 45, N1, N1) RHO(V, 14, 61, N1, N1) CHI5(V, 10, 11, 12, 13, 14, N1) \
    RHOS2(V, 15, 1, 63, 28) RHO(V, 16, 6, N1, N1) RHO(V, 17, 25, N1, N1) RHOS(V, 18, 30, N1, N1) RHO(V, 19, 18, N1, N1) CHI5(V, 15, 16, 17, 18, 19, N1) \
    RHOS2(V, 20, 27, 37, 29) RHO(V, 21, 36, N1, N1) RHO(V, 0, 10, N1, N1) RHO(V, 1, 15, N1, N1) RHOS(V, 2, 31, N1, N1) CHI5(V, 20, 21, 0, 1, 2, N1) \
    RHOS2(V, 3, 62, 2, 28) RHO(V, 4, 55, N1, N1) RHO(V, 5, 39, N1, N1) RHO(V, 6, 41, N1, N1) RHO(V, 7, 2, N1, N1) CHI5(V, 3, 4, 5, 6, 7, N1) \
    XOR(V, 8, 8, 30)
DEF(mixs_z, 108, MIX_S("zmm"))

/* ternlog dependency tests: latency chain, source written by the previous
 * op (distance 1), 2, 4, 8 ops earlier, two fresh sources, xor equivalents */
#define Y(V, i) "%%" V #i
DEF(tl_lat, 24, TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25)
    TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25)
    TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25)
    TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25) TL("zmm", 0, 24, 25))
DEF(tl_lat_y, 24, TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25)
    TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25)
    TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25)
    TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25) TL("ymm", 0, 24, 25))
DEF(xor_lat, 24, XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24)
    XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24)
    XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24)
    XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24) XOR("zmm", 0, 0, 24))
DEF(rol_lat, 24, ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7)
    ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7)
    ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7)
    ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7) ROL("zmm", 0, 0, 7))
/* source 2 = the destination of the op k before (12 independent chains of
 * such pairs for k = 1; register i reads i-k) */
#define TLP(V, i, k) TL(V, i, k, 25)
DEF(tl_d1, 24, TL("zmm", 0, 23, 25) TL("zmm", 1, 0, 25) TL("zmm", 2, 1, 25) TL("zmm", 3, 2, 25) TL("zmm", 4, 3, 25) TL("zmm", 5, 4, 25)
    TL("zmm", 6, 5, 25) TL("zmm", 7, 6, 25) TL("zmm", 8, 7, 25) TL("zmm", 9, 8, 25) TL("zmm", 10, 9, 25) TL("zmm", 11, 10, 25)
    TL("zmm", 12, 11, 25) TL("zmm", 13, 12, 25) TL("zmm", 14, 13, 25) TL("zmm", 15, 14, 25) TL("zmm", 16, 15, 25) TL("zmm", 17, 16, 25)
    TL("zmm", 18, 17, 25) TL("zmm", 19, 18, 25) TL("zmm", 20, 19, 25) TL("zmm", 21, 20, 25) TL("zmm", 22, 21, 25) TL("zmm", 23, 22, 25))
DEF(tl_d2, 24, TL("zmm", 0, 22, 25) TL("zmm", 1, 23, 25) TL("zmm", 2, 0, 25) TL("zmm", 3, 1, 25) TL("zmm", 4, 2, 25) TL("zmm", 5, 3, 25)
    TL("zmm", 6, 4, 25) TL("zmm", 7, 5, 25) TL("zmm", 8, 6, 25) TL("zmm", 9, 7, 25) TL("zmm", 10, 8, 25) TL("zmm", 11, 9, 25)
    TL("zmm", 12, 10, 25) TL("zmm", 13, 11, 25) TL("zmm", 14, 12, 25) TL("zmm", 15, 13, 25) TL("zmm", 16, 14, 25) TL("zmm", 17, 15, 25)
    TL("zmm", 18, 16, 25) TL("zmm", 19, 17, 25) TL("zmm", 20, 18, 25) TL("zmm", 21, 19, 25) TL("zmm", 22, 20, 25) TL("zmm", 23, 21, 25))
DEF(tl_d4, 24, TL("zmm", 0, 20, 25) TL("zmm", 1, 21, 25) TL("zmm", 2, 22, 25) TL("zmm", 3, 23, 25) TL("zmm", 4, 0, 25) TL("zmm", 5, 1, 25)
    TL("zmm", 6, 2, 25) TL("zmm", 7, 3, 25) TL("zmm", 8, 4, 25) TL("zmm", 9, 5, 25) TL("zmm", 10, 6, 25) TL("zmm", 11, 7, 25)
    TL("zmm", 12, 8, 25) TL("zmm", 13, 9, 25) TL("zmm", 14, 10, 25) TL("zmm", 15, 11, 25) TL("zmm", 16, 12, 25) TL("zmm", 17, 13, 25)
    TL("zmm", 18, 14, 25) TL("zmm", 19, 15, 25) TL("zmm", 20, 16, 25) TL("zmm", 21, 17, 25) TL("zmm", 22, 18, 25) TL("zmm", 23, 19, 25))
DEF(tl_d8, 24, TL("zmm", 0, 16, 25) TL("zmm", 1, 17, 25) TL("zmm", 2, 18, 25) TL("zmm", 3, 19, 25) TL("zmm", 4, 20, 25) TL("zmm", 5, 21, 25)
    TL("zmm", 6, 22, 25) TL("zmm", 7, 23, 25) TL("zmm", 8, 0, 25) TL("zmm", 9, 1, 25) TL("zmm", 10, 2, 25) TL("zmm", 11, 3, 25)
    TL("zmm", 12, 4, 25) TL("zmm", 13, 5, 25) TL("zmm", 14, 6, 25) TL("zmm", 15, 7, 25) TL("zmm", 16, 8, 25) TL("zmm", 17, 9, 25)
    TL("zmm", 18, 10, 25) TL("zmm", 19, 11, 25) TL("zmm", 20, 12, 25) TL("zmm", 21, 13, 25) TL("zmm", 22, 14, 25) TL("zmm", 23, 15, 25))
/* two fresh sources (written 1 and 2 ops earlier) */
DEF(tl_2f, 24, TL("zmm", 0, 23, 22) TL("zmm", 1, 0, 23) TL("zmm", 2, 1, 0) TL("zmm", 3, 2, 1) TL("zmm", 4, 3, 2) TL("zmm", 5, 4, 3)
    TL("zmm", 6, 5, 4) TL("zmm", 7, 6, 5) TL("zmm", 8, 7, 6) TL("zmm", 9, 8, 7) TL("zmm", 10, 9, 8) TL("zmm", 11, 10, 9)
    TL("zmm", 12, 11, 10) TL("zmm", 13, 12, 11) TL("zmm", 14, 13, 12) TL("zmm", 15, 14, 13) TL("zmm", 16, 15, 14) TL("zmm", 17, 16, 15)
    TL("zmm", 18, 17, 16) TL("zmm", 19, 18, 17) TL("zmm", 20, 19, 18) TL("zmm", 21, 20, 19) TL("zmm", 22, 21, 20) TL("zmm", 23, 22, 21))
/* the xor equivalent of tl_d1 */
DEF(xor_d1, 24, XOR("zmm", 0, 0, 23) XOR("zmm", 1, 1, 0) XOR("zmm", 2, 2, 1) XOR("zmm", 3, 3, 2) XOR("zmm", 4, 4, 3) XOR("zmm", 5, 5, 4)
    XOR("zmm", 6, 6, 5) XOR("zmm", 7, 7, 6) XOR("zmm", 8, 8, 7) XOR("zmm", 9, 9, 8) XOR("zmm", 10, 10, 9) XOR("zmm", 11, 11, 10)
    XOR("zmm", 12, 12, 11) XOR("zmm", 13, 13, 12) XOR("zmm", 14, 14, 13) XOR("zmm", 15, 15, 14) XOR("zmm", 16, 16, 15) XOR("zmm", 17, 17, 16)
    XOR("zmm", 18, 18, 17) XOR("zmm", 19, 19, 18) XOR("zmm", 20, 20, 19) XOR("zmm", 21, 21, 20) XOR("zmm", 22, 22, 21) XOR("zmm", 23, 23, 22))
/* ymm chi, chi as andn + xor, chi with the dependent ops of all rows last */
DEF(chi_y, 25, CHI5("ymm", 0, 1, 2, 3, 4, N1) CHI5("ymm", 5, 6, 7, 8, 9, N1) CHI5("ymm", 10, 11, 12, 13, 14, N1) CHI5("ymm", 15, 16, 17, 18, 19, N1) CHI5("ymm", 20, 21, 22, 23, 24, N1))
#define AX(V, a, b, c, t) ANDN(V, t, b, c) XOR(V, a, a, t)
#define CHI5AX(V, a, b, c, d, e) AX(V, a, b, c, 25) AX(V, b, c, d, 26) AX(V, c, d, e, 27) AX(V, d, e, a, 28) AX(V, e, a, b, 29)
DEF(chi_ax, 50, CHI5AX("zmm", 0, 1, 2, 3, 4) CHI5AX("zmm", 5, 6, 7, 8, 9) CHI5AX("zmm", 10, 11, 12, 13, 14) CHI5AX("zmm", 15, 16, 17, 18, 19) CHI5AX("zmm", 20, 21, 22, 23, 24))
#define CHI3(V, a, b, c, d, e) TLD(V, a, b, c) TLD(V, b, c, d) TLD(V, c, d, e)
#define CHI2(V, a, b, c, d, e) TLD(V, d, e, a) TLD(V, e, a, b)
DEF(chi_r, 25, CHI3("zmm", 0, 1, 2, 3, 4) CHI3("zmm", 5, 6, 7, 8, 9) CHI3("zmm", 10, 11, 12, 13, 14) CHI3("zmm", 15, 16, 17, 18, 19) CHI3("zmm", 20, 21, 22, 23, 24)
    CHI2("zmm", 0, 1, 2, 3, 4) CHI2("zmm", 5, 6, 7, 8, 9) CHI2("zmm", 10, 11, 12, 13, 14) CHI2("zmm", 15, 16, 17, 18, 19) CHI2("zmm", 20, 21, 22, 23, 24))
/* chi where the inputs come from rotates (as in the round): 5 rotates then chi, per row */
DEF(rolchi_z, 50, ROL("zmm", 0, 0, 3) ROL("zmm", 1, 1, 3) ROL("zmm", 2, 2, 3) ROL("zmm", 3, 3, 3) ROL("zmm", 4, 4, 3) CHI5("zmm", 0, 1, 2, 3, 4, N1)
    ROL("zmm", 5, 5, 3) ROL("zmm", 6, 6, 3) ROL("zmm", 7, 7, 3) ROL("zmm", 8, 8, 3) ROL("zmm", 9, 9, 3) CHI5("zmm", 5, 6, 7, 8, 9, N1)
    ROL("zmm", 10, 10, 3) ROL("zmm", 11, 11, 3) ROL("zmm", 12, 12, 3) ROL("zmm", 13, 13, 3) ROL("zmm", 14, 14, 3) CHI5("zmm", 10, 11, 12, 13, 14, N1)
    ROL("zmm", 15, 15, 3) ROL("zmm", 16, 16, 3) ROL("zmm", 17, 17, 3) ROL("zmm", 18, 18, 3) ROL("zmm", 19, 19, 3) CHI5("zmm", 15, 16, 17, 18, 19, N1)
    ROL("zmm", 20, 20, 3) ROL("zmm", 21, 21, 3) ROL("zmm", 22, 22, 3) ROL("zmm", 23, 23, 3) ROL("zmm", 24, 24, 3) CHI5("zmm", 20, 21, 22, 23, 24, N1))

struct t { const char* name; void (*f)(long, void*); int ops; };
#define T(n) {#n, n##_f, n##_ops}

static double ns_per_iter(void (*f)(long, void*), void* buf) {
    long n = 2000;
    for (;;) {
        double t0 = now();
        f(n, buf);
        double dt = now() - t0;
        if (dt > 0.02) {
            double best = dt;
            for (int i = 0; i < 7; i++) {
                t0 = now();
                f(n, buf);
                dt = now() - t0;
                if (dt < best) best = dt;
            }
            return best * 1e9 / n;
        }
        n *= 2;
    }
}

typedef void (*kfn)(unsigned char*, const unsigned char*, uint64_t);
static double kernel_ns_per_node(kfn f, unsigned char* out, const unsigned char* in, uint64_t nodes) {
    double best = 1e18;
    uint64_t reps = 1;
    for (;;) {
        double t0 = now();
        for (uint64_t r = 0; r < reps; r++) f(out, in, nodes);
        double dt = now() - t0;
        if (dt > 0.02) break;
        reps *= 2;
    }
    for (int i = 0; i < 9; i++) {
        double t0 = now();
        for (uint64_t r = 0; r < reps; r++) f(out, in, nodes);
        double dt = now() - t0;
        if (dt < best) best = dt;
    }
    return best * 1e9 / (double)(reps * nodes);
}

int main(int argc, char** argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    int verbose = argc > 1;
    void* buf = aligned_alloc(64, 8192);
    memset(buf, 0, 8192);
    struct t tests[] = {T(tl_z), T(tl_y), T(tld_z), T(tlm_z), T(xor_z), T(xor_y), T(andn_z), T(rol_z), T(rol_y), T(shuf_z),
                        T(shuf_y), T(msh_z), T(mov_z), T(ld_z), T(st_z), T(tlrol_z), T(xorrol_z), T(mix_z), T(mixm_z),
                        T(mix_y), T(mixm_y), T(hyb_z), T(hyb_y), T(sc), T(mixb5_z), T(mixb5_y), T(mixall_z), T(mixall_y), T(mixind_z), T(mixx_z), T(tlroldep_z), T(tlrol11_z), T(tlrol11dep_z), T(chi_z), T(sll_z), T(srl_z), T(rolsll_z), T(mixs_z), T(tl_lat), T(tl_lat_y), T(xor_lat), T(rol_lat), T(tl_d1), T(tl_d2), T(tl_d4), T(tl_d8), T(tl_2f), T(xor_d1), T(chi_y), T(chi_ax), T(chi_r), T(rolchi_z)};
    /* clock: a dependent add chain runs one add per cycle */
    double ghz = 0;
    for (int i = 0; i < 3; i++) {
        double ns = ns_per_iter(clk_f, buf) / clk_ops / 3.0;
        if (1.0 / ns > ghz) ghz = 1.0 / ns;
    }
    printf("clock (dependent imul chain, 3 cycles each): %.3f GHz\n", ghz);
    printf("%-10s %6s %10s %10s %12s\n", "test", "ops", "ns/op", "cyc/op", "cyc/block");
    for (size_t i = 0; i < sizeof tests / sizeof tests[0]; i++) {
        if (verbose) fprintf(stderr, "running %s\n", tests[i].name);
        double ns = ns_per_iter(tests[i].f, buf);
        printf("%-10s %6d %10.3f %10.3f %12.1f\n", tests[i].name, tests[i].ops, ns / tests[i].ops, ns / tests[i].ops * ghz,
               ns * ghz);
    }
    /* the kernels: cycles per round (24 rounds per batch) */
    uint64_t nodes = 1152; /* multiple of 8, 9, 4 */
    unsigned char* in = aligned_alloc(64, nodes * 64);
    unsigned char* out = aligned_alloc(64, nodes * 32);
    for (size_t i = 0; i < nodes * 64; i++) in[i] = (unsigned char)(i * 131 + 7);
    struct { const char* name; kfn f; int batch; } ks[] = {
        {"avx512_x8", keccaktree_keccak256_avx512_x8, 8},
        {"avx512_x9", keccaktree_keccak256_avx512_x9, 9},
        {"avx512vl_x4", keccaktree_keccak256_avx512vl_x4, 4},
        {"x86_x1", keccaktree_keccak256_x86_x1, 1},
        {"avx2_x8", keccaktree_keccak256_avx2_x8, 8},
    };
    printf("%-12s %10s %12s %14s\n", "kernel", "ns/node", "ns/round", "cycles/round");
    for (size_t i = 0; i < sizeof ks / sizeof ks[0]; i++) {
        if (verbose) fprintf(stderr, "running kernel %s\n", ks[i].name);
        double ns = kernel_ns_per_node(ks[i].f, out, in, nodes);
        double nsr = ns * ks[i].batch / 24.0;
        printf("%-12s %10.2f %12.2f %14.1f\n", ks[i].name, ns, nsr, nsr * ghz);
    }
    double ghz2 = 1.0 / (ns_per_iter(clk_f, buf) / clk_ops / 3.0);
    printf("clock at end: %.3f GHz\n", ghz2);
    return 0;
}
