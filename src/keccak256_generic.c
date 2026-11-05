/* Portable keccak256 over 64-byte nodes, specialised single-block sponge. */
#include <stdint.h>
#include <string.h>
#include "keccaktree.h"

typedef uint64_t V;
#define XOR(a, b) ((a) ^ (b))
#define XOR3(a, b, c) ((a) ^ (b) ^ (c))
#define ROL(a, n) (((a) << (n)) | ((a) >> (64 - (n))))
#define ROL1XOR(a, b) ((a) ^ ROL((b), 1))
#define XORROL(a, b, n) ROL(((a) ^ (b)), n)
#define CHI(a, b, c) ((a) ^ (~(b) & (c)))
#define KC(x) ((V)(x))
#define IOTA(a, i) ((a) ^ RC[i])

static const uint64_t RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL,
};

static inline uint64_t ld64(const unsigned char* p) {
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    uint64_t v;
    memcpy(&v, p, 8);
    return v;
#else
    return (uint64_t)p[0] | ((uint64_t)p[1] << 8) | ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24) |
           ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40) | ((uint64_t)p[6] << 48) | ((uint64_t)p[7] << 56);
#endif
}

static inline void st64(unsigned char* p, uint64_t v) {
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    memcpy(p, &v, 8);
#else
    for (int i = 0; i < 8; i++) p[i] = (unsigned char)(v >> (8 * i));
#endif
}

void keccaktree_keccak256_generic(unsigned char* output, const unsigned char* input, uint64_t count) {
    for (uint64_t k = 0; k < count; k++) {
        const unsigned char* in = input + 64 * k;
        V a0 = ld64(in), a1 = ld64(in + 8), a2 = ld64(in + 16), a3 = ld64(in + 24);
        V a4 = ld64(in + 32), a5 = ld64(in + 40), a6 = ld64(in + 48), a7 = ld64(in + 56);
        V o0, o1, o2, o3;
#include "keccak256_core.inc"
        unsigned char* out = output + 32 * k;
        st64(out, o0);
        st64(out + 8, o1);
        st64(out + 16, o2);
        st64(out + 24, o3);
    }
}
