/*
 * Portable keccak256 over 64-byte nodes: digest = keccak256(node).
 *
 * A node fits in one 136-byte block, so the sponge is a single permutation:
 * lanes 0..7 hold the input, lane 8 the Keccak padding byte 0x01, lane 16 the
 * final padding bit, every other lane is zero. The digest is lanes 0..3.
 *
 * This is the fallback for CPUs without a dedicated kernel; it is written for
 * clarity, the fast paths are the assembly kernels.
 */
#include <stdint.h>
#include "keccaktree.h"

static const uint64_t RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL,
};

/* rho offsets and pi destinations along pi's 24-cycle starting at lane 1 */
static const unsigned RHO[24] = {
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
};
static const unsigned PI[24] = {
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
};

#define ROL(a, n) (((a) << (n)) | ((a) >> (64 - (n))))

static inline uint64_t ld64(const unsigned char *p) {
    uint64_t v = 0;
    for (int i = 7; i >= 0; i--) v = (v << 8) | p[i];
    return v;
}

static inline void st64(unsigned char *p, uint64_t v) {
    for (int i = 0; i < 8; i++) p[i] = (unsigned char)(v >> (8 * i));
}

static void keccak_f1600(uint64_t a[25]) {
    uint64_t c[5], d, t, u;
    for (int r = 0; r < 24; r++) {
        /* theta */
        for (int x = 0; x < 5; x++) c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        for (int x = 0; x < 5; x++) {
            d = c[(x + 4) % 5] ^ ROL(c[(x + 1) % 5], 1);
            for (int y = 0; y < 25; y += 5) a[y + x] ^= d;
        }
        /* rho and pi */
        t = a[1];
        for (int i = 0; i < 24; i++) {
            u = a[PI[i]];
            a[PI[i]] = ROL(t, RHO[i]);
            t = u;
        }
        /* chi */
        for (int y = 0; y < 25; y += 5) {
            for (int x = 0; x < 5; x++) c[x] = a[y + x];
            for (int x = 0; x < 5; x++) a[y + x] = c[x] ^ (~c[(x + 1) % 5] & c[(x + 2) % 5]);
        }
        /* iota */
        a[0] ^= RC[r];
    }
}

void keccaktree_keccak256_generic(unsigned char *output, const unsigned char *input, uint64_t count) {
    for (uint64_t k = 0; k < count; k++) {
        uint64_t a[25] = {0};
        for (int i = 0; i < 8; i++) a[i] = ld64(input + 64 * k + 8 * i);
        a[8] = 0x01;
        a[16] = 0x8000000000000000ULL;
        keccak_f1600(a);
        for (int i = 0; i < 4; i++) st64(output + 32 * k + 8 * i, a[i]);
    }
}
