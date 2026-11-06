/* Tests: reference sponge validated against published vectors, then every
 * backend vs the reference for all counts 0..300, in-place, and tails. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __x86_64__
#include <cpuid.h>
#endif
#include "keccaktree.h"

static const uint64_t RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL,
};
static const int RHO[25] = {0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
                            41, 45, 15, 21, 8, 18, 2, 61, 56, 14};

/* Textbook Keccak-f[1600], written independently of the generator. */
static void keccakf(uint64_t s[25]) {
    for (int r = 0; r < 24; r++) {
        uint64_t C[5], D[5], B[25];
        for (int x = 0; x < 5; x++) C[x] = s[x] ^ s[x + 5] ^ s[x + 10] ^ s[x + 15] ^ s[x + 20];
        for (int x = 0; x < 5; x++) D[x] = C[(x + 4) % 5] ^ ((C[(x + 1) % 5] << 1) | (C[(x + 1) % 5] >> 63));
        for (int i = 0; i < 25; i++) s[i] ^= D[i % 5];
        for (int x = 0; x < 5; x++)
            for (int y = 0; y < 5; y++) {
                uint64_t v = s[x + 5 * y];
                int n = RHO[x + 5 * y];
                B[y + 5 * ((2 * x + 3 * y) % 5)] = n ? (v << n) | (v >> (64 - n)) : v;
            }
        for (int x = 0; x < 5; x++)
            for (int y = 0; y < 5; y++)
                s[x + 5 * y] = B[x + 5 * y] ^ (~B[(x + 1) % 5 + 5 * y] & B[(x + 2) % 5 + 5 * y]);
        s[0] ^= RC[r];
    }
}

/* Generic sponge, rate 136, any length; pad = 0x01 keccak256, 0x06 SHA3-256 */
static void sponge256(unsigned char out[32], const unsigned char* in, size_t len, unsigned char pad) {
    uint64_t s[25] = {0};
    unsigned char blk[136];
    for (;;) {
        size_t n = len < 136 ? len : 136;
        memset(blk, 0, 136);
        memcpy(blk, in, n);
        if (n < 136) {
            blk[n] ^= pad;
            blk[135] ^= 0x80;
        }
        for (int i = 0; i < 17; i++) {
            uint64_t w = 0;
            for (int j = 0; j < 8; j++) w |= (uint64_t)blk[8 * i + j] << (8 * j);
            s[i] ^= w;
        }
        keccakf(s);
        if (n < 136) break;
        in += 136;
        len -= 136;
        if (len == 0) { /* exact multiple: one more padding-only block */
            memset(blk, 0, 136);
            blk[0] ^= pad;
            blk[135] ^= 0x80;
            for (int i = 0; i < 17; i++) {
                uint64_t w = 0;
                for (int j = 0; j < 8; j++) w |= (uint64_t)blk[8 * i + j] << (8 * j);
                s[i] ^= w;
            }
            keccakf(s);
            break;
        }
    }
    for (int i = 0; i < 32; i++) out[i] = (unsigned char)(s[i / 8] >> (8 * (i % 8)));
}

static int fails = 0;
static void hex(char* dst, const unsigned char* p, int n) {
    for (int i = 0; i < n; i++) sprintf(dst + 2 * i, "%02x", p[i]);
}
static void check_hex(const char* name, const unsigned char* got, const char* want) {
    char h[65];
    hex(h, got, 32);
    int ok = strcmp(h, want) == 0;
    printf("  %-48s [ %s ]\n", name, ok ? "OK" : "FAIL");
    if (!ok) {
        printf("    got  %s\n    want %s\n", h, want);
        fails++;
    }
}

static void test_reference(void) {
    unsigned char d[32];
    printf("reference sponge (published vectors)\n");
    sponge256(d, (const unsigned char*)"", 0, 0x01);
    check_hex("keccak256(\"\")", d, "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
    sponge256(d, (const unsigned char*)"abc", 3, 0x01);
    check_hex("keccak256(\"abc\")", d, "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45");
    sponge256(d, (const unsigned char*)"", 0, 0x06);
    check_hex("sha3-256(\"\")", d, "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a");
    sponge256(d, (const unsigned char*)"abc", 3, 0x06);
    check_hex("sha3-256(\"abc\")", d, "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532");
    unsigned char z[64] = {0};
    sponge256(d, z, 64, 0x01);
    /* keccak256(bytes32(0) ++ bytes32(0)) - the depth-1 zero hash of Ethereum keccak Merkle trees */
    check_hex("keccak256(0^64)", d, "ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5");
}

static uint64_t rng = 0x9E3779B97F4A7C15ULL;
static uint64_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return rng;
}

#define MAXN 300
static void test_backend(const char* name, keccaktree_hash_fcn f) {
    static unsigned char in[MAXN * 64 + 64], out[MAXN * 32 + 64], ref[MAXN * 32], ip[MAXN * 64 + 64];
    for (size_t i = 0; i < sizeof in; i++) in[i] = (unsigned char)next();
    for (int i = 0; i < MAXN; i++) sponge256(ref + 32 * i, in + 64 * i, 64, 0x01);
    int ok = 1;
    for (int n = 0; n <= MAXN && ok; n++) {
        memset(out, 0xEE, sizeof out);
        f(out, in, n);
        if (memcmp(out, ref, 32 * n)) { printf("    mismatch at count=%d\n", n); ok = 0; }
        for (size_t j = 32 * n; j < sizeof out; j++)
            if (out[j] != 0xEE) { printf("    wrote past end at count=%d\n", n); ok = 0; break; }
    }
    /* unaligned buffers */
    for (int off = 1; off < 8 && ok; off++) {
        memcpy(ip + off, in, 64 * 37);
        f(out + off, ip + off, 37);
        if (memcmp(out + off, ref, 32 * 37)) { printf("    unaligned mismatch off=%d\n", off); ok = 0; }
    }
    /* in place: output == input (layer reduction) */
    memcpy(ip, in, MAXN * 64);
    f(ip, ip, MAXN);
    if (ok && memcmp(ip, ref, 32 * MAXN)) { printf("    in-place mismatch\n"); ok = 0; }
    printf("  %-48s [ %s ]\n", name, ok ? "OK" : "FAIL");
    if (!ok) fails++;
}

int main(void) {
    test_reference();
    printf("backends vs reference (count 0..%d, unaligned, in-place)\n", MAXN);
    test_backend("generic", keccaktree_keccak256_generic);
    keccaktree_init(NULL);
    test_backend("keccaktree_hash (auto-detected)", keccaktree_hash);
#ifdef __x86_64__
    uint32_t a = 0, b = 0, c = 0, d = 0;
    __get_cpuid_count(7, 0, &a, &b, &c, &d);
    if ((b & bit_BMI) && (b & bit_BMI2)) {
        test_backend("x86_x1", keccaktree_keccak256_x86_x1);
    } else {
        printf("  %-48s [ no CPU support ]\n", "x86_x1");
    }
    if ((b & bit_AVX2) && (b & bit_BMI) && (b & bit_BMI2)) {
        test_backend("avx2_x2", keccaktree_keccak256_avx2_x2);
        /* both remainder paths of avx2_x4 (and so of avx2_x8): 2 nodes
         * padded, or handed to avx2_x2 */
        keccaktree_avx2_small_tail(1);
        test_backend("avx2_x4 (padded pair)", keccaktree_keccak256_avx2_x4);
        test_backend("avx2_x8 (padded pair)", keccaktree_keccak256_avx2_x8);
        keccaktree_avx2_small_tail(2);
        test_backend("avx2_x4 (avx2_x2 pair)", keccaktree_keccak256_avx2_x4);
        test_backend("avx2_x8 (avx2_x2 pair)", keccaktree_keccak256_avx2_x8);
        test_backend("avx2_x9", keccaktree_keccak256_avx2_x9);
        test_backend("avx2_x10", keccaktree_keccak256_avx2_x10);
        test_backend("avx2_x5", keccaktree_keccak256_avx2_x5);
        test_backend("avx2_x6", keccaktree_keccak256_avx2_x6);
    } else {
        printf("  %-48s [ no CPU support ]\n", "avx2");
    }
    if ((b & bit_AVX512F) && (b & bit_AVX512VL)) {
        test_backend("avx512vl_x4", keccaktree_keccak256_avx512vl_x4);
        test_backend("avx512_x8", keccaktree_keccak256_avx512_x8);
    } else {
        printf("  %-48s [ no CPU support ]\n", "avx512");
    }
#endif
#ifdef __aarch64__
    test_backend("neon_x2", keccaktree_keccak256_neon_x2);
    test_backend("scalar_x1", keccaktree_keccak256_scalar_x1);
    test_backend("neon_x3", keccaktree_keccak256_neon_x3);
    if (getenv("KT_TEST_SHA3")) {
        test_backend("sha3_x2", keccaktree_keccak256_sha3_x2);
        test_backend("sha3_x3", keccaktree_keccak256_sha3_x3);
        test_backend("sha3_x3r", keccaktree_keccak256_sha3_x3r);
    } else {
        printf("  %-48s [ skipped, set KT_TEST_SHA3=1 on FEAT_SHA3 CPUs ]\n", "sha3_*");
    }
#endif
#if defined(__riscv) && __riscv_xlen == 64
    test_backend("rv64_x1", keccaktree_keccak256_rv64_x1);
    /* the extension kernels only where qemu / the CPU has the extension:
     * KT_TEST_ZBB=1, KT_TEST_RVV=1, KT_TEST_ZVKB=1 */
    if (getenv("KT_TEST_ZBB")) test_backend("zbb_x1", keccaktree_keccak256_zbb_x1);
    else printf("  %-48s [ skipped, set KT_TEST_ZBB=1 on Zbb CPUs ]\n", "zbb_x1");
    if (getenv("KT_TEST_RVV")) test_backend("rvv", keccaktree_keccak256_rvv);
    else printf("  %-48s [ skipped, set KT_TEST_RVV=1 on RVV 1.0 CPUs ]\n", "rvv");
    if (getenv("KT_TEST_ZVKB")) test_backend("rvv_zvkb", keccaktree_keccak256_rvv_zvkb);
    else printf("  %-48s [ skipped, set KT_TEST_ZVKB=1 on RVV + Zvkb CPUs ]\n", "rvv_zvkb");
#endif
    printf(fails ? "\n%d FAILED\n" : "\nall passed\n", fails);
    return fails != 0;
}
