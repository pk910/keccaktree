/* Interleaved A/B benchmark: baseline kernels (prefixed base_, built from the
 * untouched main commit) vs candidate kernels from the working tree.
 *
 * Why: this VM's vCPUs float between host P-cores and E-cores, so absolute
 * ns/node numbers drift by 2.4x between runs. Interleaving base and
 * candidate per sample and reporting the ratio makes a comparison valid on
 * whichever core the process happens to run. Each sample is min-of-N.
 *
 * CI copy (bench/ab): the base library is main built with every public
 * symbol renamed base_* by -D (bench/ab/build.sh), so no objcopy is needed.
 *
 * usage: ab [-n rounds] [-s size,size,...] kernel[,kernel...]
 *   kernel: avx2_x4 avx2_x8 generic auto  (auto = keccaktree_hash dispatch)
 *   also: cand-only names via "new:<name>" compared against base avx2_x4
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include "keccaktree.h"

typedef void (*fn)(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_keccak256_generic(unsigned char*, const unsigned char*, uint64_t);
#ifdef __x86_64__
void base_keccaktree_keccak256_avx2_x4(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_keccak256_avx2_x8(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_keccak256_avx512_x8(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_keccak256_avx512vl_x4(unsigned char*, const unsigned char*, uint64_t);
#endif
#ifdef __aarch64__
void base_keccaktree_keccak256_neon_x2(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_keccak256_scalar_x1(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_keccak256_sha3_x2(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_keccak256_sha3_x3(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_keccak256_sha3_x3r(unsigned char*, const unsigned char*, uint64_t);
#endif
void base_keccaktree_hash(unsigned char*, const unsigned char*, uint64_t);
void base_keccaktree_init(fn);
/* base kernels that only exist when the baseline is built from a newer tree
 * (AB_BASE=<dir> with build_ab.sh): resolved weakly, usable as "cand:base" */
#define WEAKB(n) void base_##n(unsigned char*, const unsigned char*, uint64_t) __attribute__((weak));
WEAKB(keccaktree_keccak256_avx2_x10)
WEAKB(keccaktree_keccak256_avx2_x9)
WEAKB(keccaktree_keccak256_avx2_x5)
WEAKB(keccaktree_keccak256_avx2_x2)
WEAKB(keccaktree_keccak256_x86_x1)
WEAKB(keccaktree_keccak256_neon_x3)
/* candidate kernels that may not exist in the header yet are resolved weakly
 * (per architecture, so the Mach-O link has no stray undefined references) */
#ifdef __APPLE__
#define WEAK(n) void n(unsigned char*, const unsigned char*, uint64_t) __attribute__((weak_import));
#else
#define WEAK(n) void n(unsigned char*, const unsigned char*, uint64_t) __attribute__((weak));
#endif
#ifdef __aarch64__
WEAK(keccaktree_keccak256_scalar_x1)
WEAK(keccaktree_keccak256_neon_x2)
WEAK(keccaktree_keccak256_neon_x3)
WEAK(keccaktree_keccak256_sha3_x2)
WEAK(keccaktree_keccak256_sha3_x3)
WEAK(keccaktree_keccak256_sha3_x3r)
WEAK(keccaktree_keccak256_sha3_x4)
WEAK(keccaktree_keccak256_sha3_x3b)
#ifndef __APPLE__
WEAK(keccaktree_keccak256_scalar_x2)
WEAK(keccaktree_keccak256_scalar_x1r)
WEAK(keccaktree_keccak256_neon_x2b)
WEAK(keccaktree_keccak256_neon_x4)
WEAK(keccaktree_keccak256_neon_x1)
#endif
#else
#define keccaktree_keccak256_scalar_x1 NULL
#define keccaktree_keccak256_neon_x2 NULL
#define keccaktree_keccak256_neon_x3 NULL
#define keccaktree_keccak256_sha3_x2 NULL
#define keccaktree_keccak256_sha3_x3 NULL
#define keccaktree_keccak256_sha3_x3r NULL
#define keccaktree_keccak256_sha3_x4 NULL
#define keccaktree_keccak256_sha3_x3b NULL
#endif
#if !defined(__aarch64__) || defined(__APPLE__)
#define keccaktree_keccak256_scalar_x2 NULL
#define keccaktree_keccak256_scalar_x1r NULL
#define keccaktree_keccak256_neon_x2b NULL
#define keccaktree_keccak256_neon_x4 NULL
#define keccaktree_keccak256_neon_x1 NULL
#endif
#ifdef __x86_64__
WEAK(keccaktree_keccak256_avx2_x4)
WEAK(keccaktree_keccak256_avx2_x8)
WEAK(keccaktree_keccak256_avx2_x6)
WEAK(keccaktree_keccak256_avx2_x3)
WEAK(keccaktree_keccak256_avx2_x1)
WEAK(keccaktree_keccak256_bmi2_x1)
WEAK(keccaktree_keccak256_avx2_x5)
WEAK(keccaktree_keccak256_avx2_x2)
WEAK(keccaktree_keccak256_avx2_x12)
WEAK(keccaktree_keccak256_avx2_x16)
WEAK(keccaktree_keccak256_sse2_x2)
WEAK(keccaktree_keccak256_generic_x1)
WEAK(keccaktree_keccak256_x86_x1)
WEAK(keccaktree_keccak256_avx2_x9)
WEAK(keccaktree_keccak256_avx2_x10)
WEAK(keccaktree_keccak256_avx512_x8)
WEAK(keccaktree_keccak256_avx512vl_x4)
WEAK(keccaktree_keccak256_avx512_x9)
WEAK(keccaktree_keccak256_avx512_x10)
WEAK(keccaktree_keccak256_avx512vl_x5)
WEAK(keccaktree_keccak256_avx512_x16)
#else
#define keccaktree_keccak256_avx2_x4 NULL
#define keccaktree_keccak256_avx2_x8 NULL
#define keccaktree_keccak256_avx2_x6 NULL
#define keccaktree_keccak256_avx2_x3 NULL
#define keccaktree_keccak256_avx2_x1 NULL
#define keccaktree_keccak256_bmi2_x1 NULL
#define keccaktree_keccak256_avx2_x5 NULL
#define keccaktree_keccak256_avx2_x2 NULL
#define keccaktree_keccak256_avx2_x12 NULL
#define keccaktree_keccak256_avx2_x16 NULL
#define keccaktree_keccak256_sse2_x2 NULL
#define keccaktree_keccak256_generic_x1 NULL
#define keccaktree_keccak256_x86_x1 NULL
#define keccaktree_keccak256_avx2_x9 NULL
#define keccaktree_keccak256_avx2_x10 NULL
#define keccaktree_keccak256_avx512_x8 NULL
#define keccaktree_keccak256_avx512vl_x4 NULL
#define keccaktree_keccak256_avx512_x9 NULL
#define keccaktree_keccak256_avx512_x10 NULL
#define keccaktree_keccak256_avx512vl_x5 NULL
#define keccaktree_keccak256_avx512_x16 NULL
#endif

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static unsigned char *in, *out;
#define MAXN 65536

/* time f on `nodes` nodes, repeated until >= ~target seconds; returns ns/node */
static double sample(fn f, uint64_t nodes, uint64_t reps) {
    double t0 = now();
    for (uint64_t r = 0; r < reps; r++) f(out, in, nodes);
    return (now() - t0) * 1e9 / (double)(reps * nodes);
}

static uint64_t calib_reps(fn f, uint64_t nodes, double target) {
    uint64_t reps = 1;
    for (;;) {
        double t0 = now();
        for (uint64_t r = 0; r < reps; r++) f(out, in, nodes);
        if (now() - t0 > target) return reps;
        reps *= 2;
    }
}

static int cmpd(const void* a, const void* b) {
    double x = *(const double*)a, y = *(const double*)b;
    return x < y ? -1 : x > y;
}

struct k { const char* name; fn base; fn cand; };

static fn lookup_cand(const char* n) {
    if (!strcmp(n, "generic")) return keccaktree_keccak256_generic;
    if (!strcmp(n, "avx2_x4")) return keccaktree_keccak256_avx2_x4;
    if (!strcmp(n, "avx2_x8")) return keccaktree_keccak256_avx2_x8;
    if (!strcmp(n, "auto")) return keccaktree_hash;
    if (!strcmp(n, "scalar_x1")) return keccaktree_keccak256_scalar_x1;
    if (!strcmp(n, "scalar_x2")) return keccaktree_keccak256_scalar_x2;
    if (!strcmp(n, "scalar_x1r")) return keccaktree_keccak256_scalar_x1r;
    if (!strcmp(n, "neon_x2b")) return keccaktree_keccak256_neon_x2b;
    if (!strcmp(n, "neon_x1")) return keccaktree_keccak256_neon_x1;
    if (!strcmp(n, "neon_x2")) return keccaktree_keccak256_neon_x2;
    if (!strcmp(n, "neon_x3")) return keccaktree_keccak256_neon_x3;
    if (!strcmp(n, "neon_x4")) return keccaktree_keccak256_neon_x4;
    if (!strcmp(n, "sha3_x2")) return keccaktree_keccak256_sha3_x2;
    if (!strcmp(n, "sha3_x3")) return keccaktree_keccak256_sha3_x3;
    if (!strcmp(n, "sha3_x3r")) return keccaktree_keccak256_sha3_x3r;
    if (!strcmp(n, "avx2_x6")) return keccaktree_keccak256_avx2_x6;
    if (!strcmp(n, "avx2_x3")) return keccaktree_keccak256_avx2_x3;
    if (!strcmp(n, "avx2_x1")) return keccaktree_keccak256_avx2_x1;
    if (!strcmp(n, "bmi2_x1")) return keccaktree_keccak256_bmi2_x1;
    if (!strcmp(n, "avx2_x5")) return keccaktree_keccak256_avx2_x5;
    if (!strcmp(n, "avx2_x2")) return keccaktree_keccak256_avx2_x2;
    if (!strcmp(n, "avx2_x12")) return keccaktree_keccak256_avx2_x12;
    if (!strcmp(n, "avx2_x16")) return keccaktree_keccak256_avx2_x16;
    if (!strcmp(n, "sse2_x2")) return keccaktree_keccak256_sse2_x2;
    if (!strcmp(n, "generic_x1")) return keccaktree_keccak256_generic_x1;
    if (!strcmp(n, "x86_x1")) return keccaktree_keccak256_x86_x1;
    if (!strcmp(n, "avx2_x9")) return keccaktree_keccak256_avx2_x9;
    if (!strcmp(n, "avx2_x10")) return keccaktree_keccak256_avx2_x10;
    if (!strcmp(n, "avx512_x8")) return keccaktree_keccak256_avx512_x8;
    if (!strcmp(n, "avx512vl_x4")) return keccaktree_keccak256_avx512vl_x4;
    if (!strcmp(n, "avx512_x9")) return keccaktree_keccak256_avx512_x9;
    if (!strcmp(n, "avx512_x10")) return keccaktree_keccak256_avx512_x10;
    if (!strcmp(n, "avx512vl_x5")) return keccaktree_keccak256_avx512vl_x5;
    if (!strcmp(n, "avx512_x16")) return keccaktree_keccak256_avx512_x16;
    if (!strcmp(n, "sha3_x4")) return keccaktree_keccak256_sha3_x4;
    if (!strcmp(n, "sha3_x3b")) return keccaktree_keccak256_sha3_x3b;
    return NULL;
}
static fn lookup_base(const char* n) {
    if (!strcmp(n, "generic")) return base_keccaktree_keccak256_generic;
    if (!strcmp(n, "auto")) return base_keccaktree_hash;
#ifdef __x86_64__
    if (!strcmp(n, "avx2_x4")) return base_keccaktree_keccak256_avx2_x4;
    if (!strcmp(n, "avx2_x8")) return base_keccaktree_keccak256_avx2_x8;
    if (!strcmp(n, "avx2_x10")) return base_keccaktree_keccak256_avx2_x10;
    if (!strcmp(n, "avx2_x9")) return base_keccaktree_keccak256_avx2_x9;
    if (!strcmp(n, "avx2_x5")) return base_keccaktree_keccak256_avx2_x5;
    if (!strcmp(n, "avx2_x2")) return base_keccaktree_keccak256_avx2_x2;
    if (!strcmp(n, "x86_x1")) return base_keccaktree_keccak256_x86_x1;
    if (!strcmp(n, "avx512_x8")) return base_keccaktree_keccak256_avx512_x8;
    if (!strcmp(n, "avx512vl_x4")) return base_keccaktree_keccak256_avx512vl_x4;
#endif
#ifdef __aarch64__
    if (!strcmp(n, "neon_x2")) return base_keccaktree_keccak256_neon_x2;
    if (!strcmp(n, "scalar_x1")) return base_keccaktree_keccak256_scalar_x1;
    if (!strcmp(n, "sha3_x2")) return base_keccaktree_keccak256_sha3_x2;
    if (!strcmp(n, "sha3_x3")) return base_keccaktree_keccak256_sha3_x3;
    if (!strcmp(n, "sha3_x3r")) return base_keccaktree_keccak256_sha3_x3r;
    if (!strcmp(n, "neon_x3")) return base_keccaktree_keccak256_neon_x3;
#endif
    return NULL;
}

/* core class from the baseline avx2_x4 speed at 1024 nodes: on this VM the
 * host P-core gives ~100 ns/node, the E-core ~240 */
static const char* core_class(double* ns) {
    uint64_t reps = calib_reps(base_keccaktree_hash, 1024, 0.01);
    double best = 1e9;
    for (int i = 0; i < 5; i++) { double s = sample(base_keccaktree_hash, 1024, reps); if (s < best) best = s; }
    *ns = best;
#ifdef __x86_64__
    /* only meaningful on the local Alder Lake VM: P-core ~100, E-core ~240 ns/node */
    return best < 160 ? "fast(P-core?)" : "slow(E-core?)";
#else
    return "n/a";
#endif
}

int main(int argc, char** argv) {
    int rounds = 15;
    double target = 0.005; /* seconds per sample */
    uint64_t sizes[256] = {1, 2, 3, 4, 5, 7, 8, 16, 64, 256, 1024, 16384};
    int nsizes = 12;
    const char* klist = NULL;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-n") && i + 1 < argc) rounds = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-t") && i + 1 < argc) target = atof(argv[++i]);
        else if (!strcmp(argv[i], "-s") && i + 1 < argc) {
            nsizes = 0;
            for (char* p = strtok(argv[++i], ","); p; p = strtok(NULL, ",")) sizes[nsizes++] = strtoull(p, NULL, 10);
        } else klist = argv[i];
    }
    if (!klist) { fprintf(stderr, "usage: ab [-n rounds] [-t sec] [-s sizes] kernel[,kernel...]\n"); return 2; }

    in = aligned_alloc(64, MAXN * 64);
    out = aligned_alloc(64, MAXN * 32);
    for (size_t i = 0; i < MAXN * 64; i++) in[i] = (unsigned char)(i * 131 + 7);
    base_keccaktree_init(NULL);
    keccaktree_init(NULL);

    struct k ks[16];
    int nk = 0;
    char buf[256];
    strncpy(buf, klist, 255);
    for (char* p = strtok(buf, ","); p; p = strtok(NULL, ",")) {
        const char* cn = p, *bn = p;
        char* vs = strchr(p, ':'); /* cand:base */
        if (vs) { *vs = 0; cn = p; bn = vs + 1; }
        ks[nk].name = strdup(p);
        ks[nk].cand = lookup_cand(cn);
        ks[nk].base = lookup_base(bn);
        if (!ks[nk].cand) { fprintf(stderr, "unknown/absent candidate kernel %s\n", cn); return 2; }
        if (!ks[nk].base) { fprintf(stderr, "unknown base kernel %s\n", bn); return 2; }
        nk++;
    }

    double cns;
    const char* cls0 = core_class(&cns);
    printf("core: %s (base auto @1024: %.1f ns/node), %d rounds, interleaved base/cand, min and median of rounds\n", cls0, cns, rounds);
    printf("%-10s %7s | %9s %9s %7s | %9s %9s %7s\n", "kernel", "nodes", "base min", "cand min", "ratio", "base med", "cand med", "ratio");
    for (int ki = 0; ki < nk; ki++) {
        for (int si = 0; si < nsizes; si++) {
            uint64_t n = sizes[si];
            uint64_t reps = calib_reps(ks[ki].base, n, target);
            double b[256], c[256];
            for (int r = 0; r < rounds; r++) {
                if (r & 1) { c[r] = sample(ks[ki].cand, n, reps); b[r] = sample(ks[ki].base, n, reps); }
                else       { b[r] = sample(ks[ki].base, n, reps); c[r] = sample(ks[ki].cand, n, reps); }
            }
            qsort(b, rounds, sizeof b[0], cmpd);
            qsort(c, rounds, sizeof c[0], cmpd);
            double bm = b[rounds / 2], cm = c[rounds / 2];
            printf("%-10s %7llu | %9.2f %9.2f %6.3fx | %9.2f %9.2f %6.3fx\n", ks[ki].name, (unsigned long long)n,
                   b[0], c[0], b[0] / c[0], bm, cm, bm / cm);
            fflush(stdout);
        }
    }
    double cns1;
    const char* cls1 = core_class(&cns1);
    if (strcmp(cls0, cls1) || cns1 > cns * 1.08 || cns1 < cns / 1.08) printf("WARNING: speed class changed during the run (%s %.1f -> %s %.1f ns): rerun\n", cls0, cns, cls1, cns1);
    else printf("core: %s at end (%.1f ns/node); ratio > 1 = candidate faster\n", cls1, cns1);
    return 0;
}
