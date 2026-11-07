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
#define G_26 "%%rsi"
#define G_27 "%%rdi"
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

DEF(clk, 32, "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t"
    "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t"
    "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t"
    "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t"
    "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t"
    "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t" "addq $1, %%rax\n\t"
    "addq $1, %%rax\n\t" "addq $1, %%rax\n\t")
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

int main(void) {
    void* buf = aligned_alloc(64, 4096);
    memset(buf, 0, 4096);
    struct t tests[] = {T(tl_z), T(tl_y), T(tld_z), T(tlm_z), T(xor_z), T(xor_y), T(andn_z), T(rol_z), T(rol_y), T(shuf_z),
                        T(shuf_y), T(msh_z), T(mov_z), T(ld_z), T(st_z), T(tlrol_z), T(xorrol_z), T(mix_z), T(mixm_z),
                        T(mix_y), T(mixm_y), T(hyb_z), T(hyb_y), T(sc)};
    /* clock: a dependent add chain runs one add per cycle */
    double ghz = 0;
    for (int i = 0; i < 3; i++) {
        double ns = ns_per_iter(clk_f, buf) / clk_ops;
        if (1.0 / ns > ghz) ghz = 1.0 / ns;
    }
    printf("clock (dependent add chain): %.3f GHz\n", ghz);
    printf("%-10s %6s %10s %10s %12s\n", "test", "ops", "ns/op", "cyc/op", "cyc/block");
    for (size_t i = 0; i < sizeof tests / sizeof tests[0]; i++) {
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
        double ns = kernel_ns_per_node(ks[i].f, out, in, nodes);
        double nsr = ns * ks[i].batch / 24.0;
        printf("%-12s %10.2f %12.2f %14.1f\n", ks[i].name, ns, nsr, nsr * ghz);
    }
    double ghz2 = 1.0 / (ns_per_iter(clk_f, buf) / clk_ops);
    printf("clock at end: %.3f GHz\n", ghz2);
    return 0;
}
