/* Throughput benchmark: keccaktree backends vs hashtree sha256 backends.
 * Build with `make bench HASHTREE=1` to include the sha256 comparison. */
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef __x86_64__
#include <cpuid.h>
#endif
#if defined(__aarch64__) && defined(__linux__)
#include <sys/auxv.h>
#include <asm/hwcap.h>
#endif
#include "keccaktree.h"
#ifdef HAVE_HASHTREE
#include "hashtree.h"
#endif

typedef void (*fn)(unsigned char*, const unsigned char*, uint64_t);

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static unsigned char *in, *out;

static double run(fn f, uint64_t nodes) {
    /* best of 7 runs of ~>=20ms each */
    uint64_t reps = 1;
    for (;;) {
        double t0 = now();
        for (uint64_t r = 0; r < reps; r++) f(out, in, nodes);
        if (now() - t0 > 0.02) break;
        reps *= 2;
    }
    double best = 1e9;
    for (int k = 0; k < 7; k++) {
        double t0 = now();
        for (uint64_t r = 0; r < reps; r++) f(out, in, nodes);
        double dt = (now() - t0) / (reps * nodes);
        if (dt < best) best = dt;
    }
    return best * 1e9; /* ns per 64-byte node */
}

static const uint64_t sizes[] = {1, 8, 64, 1024, 65536};
#define NS (sizeof sizes / sizeof sizes[0])

static void row(const char* name, fn f) {
    printf("%-26s", name);
    for (size_t i = 0; i < NS; i++) printf(" %9.1f", run(f, sizes[i]));
    double ns = run(f, 65536);
    printf("  %8.2f\n", 1e3 / ns);
}

int main(void) {
    in = aligned_alloc(64, 65536 * 64);
    out = aligned_alloc(64, 65536 * 32);
    for (size_t i = 0; i < 65536 * 64; i++) in[i] = (unsigned char)(i * 131 + 7);
    printf("ns per 64-byte node (lower is better), by batch size; last column Mnodes/s @65536\n");
    printf("%-26s", "implementation");
    for (size_t i = 0; i < NS; i++) printf(" %9llu", (unsigned long long)sizes[i]);
    printf("  %8s\n", "Mnode/s");
    row("keccak256 generic", keccaktree_keccak256_generic);
#ifdef __x86_64__
    uint32_t a = 0, b = 0, c = 0, d = 0;
    __get_cpuid_count(7, 0, &a, &b, &c, &d);
    int avx2 = b & bit_AVX2, avx512 = (b & bit_AVX512F) && (b & bit_AVX512VL), sha = b & bit_SHA;
    (void)sha;
    if (avx2) row("keccak256 avx2_x4", keccaktree_keccak256_avx2_x4);
    if (avx512) row("keccak256 avx512vl_x4", keccaktree_keccak256_avx512vl_x4);
    if (avx512) row("keccak256 avx512_x8", keccaktree_keccak256_avx512_x8);
#ifdef HAVE_HASHTREE
    row("sha256 hashtree generic", hashtree_sha256_generic);
    row("sha256 hashtree avx_x1", hashtree_sha256_avx_x1);
    if (avx2) row("sha256 hashtree avx2_x8", hashtree_sha256_avx2_x8);
    if (avx512) row("sha256 hashtree avx512_x16", hashtree_sha256_avx512_x16);
    if (sha) row("sha256 hashtree shani_x2", hashtree_sha256_shani_x2);
#endif
#endif
#ifdef __aarch64__
#if defined(__APPLE__)
    int sha3 = 1, sha2 = 1;
#elif defined(__linux__)
    unsigned long hw = getauxval(AT_HWCAP);
    int sha3 = (hw & HWCAP_SHA3) != 0, sha2 = (hw & HWCAP_SHA2) != 0;
#else
    int sha3 = 0, sha2 = 0;
#endif
    (void)sha2;
    row("keccak256 scalar_x1", keccaktree_keccak256_scalar_x1);
    row("keccak256 neon_x2", keccaktree_keccak256_neon_x2);
    if (sha3) {
        row("keccak256 sha3_x2", keccaktree_keccak256_sha3_x2);
        row("keccak256 sha3_x3", keccaktree_keccak256_sha3_x3);
        row("keccak256 sha3_x3r", keccaktree_keccak256_sha3_x3r);
    }
#ifdef HAVE_HASHTREE
    row("sha256 hashtree generic", hashtree_sha256_generic);
    row("sha256 hashtree neon_x1", hashtree_sha256_neon_x1);
    row("sha256 hashtree neon_x4", hashtree_sha256_neon_x4);
    if (sha2) row("sha256 hashtree sha_x1", hashtree_sha256_sha_x1);
#endif
#endif
    row("keccaktree_hash (auto)", keccaktree_hash);
    return 0;
}
