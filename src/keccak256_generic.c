/*
 * Portable keccak256 over 64-byte nodes: digest = keccak256(node).
 *
 * A node fits in one 136-byte block, so the sponge is a single permutation:
 * lanes 0..7 hold the input, lane 8 the Keccak padding byte 0x01, lane 16 the
 * final padding bit, every other lane is zero. The digest is lanes 0..3.
 *
 * This is the fallback for CPUs without a dedicated kernel (and for builds
 * that cannot assemble the kernels: MSVC, CGO-less Go). It is plain C with
 * no intrinsics, endianness-safe byte loads and stores, and the permutation
 * in the classic "compact unrolled" shape:
 *
 *  - the 25 lanes are locals (two sets, A and E, the rounds alternate
 *    between them so no copy is needed), theta/rho/pi/chi/iota are one
 *    macro per round with the rho offsets and the pi destinations as
 *    literals; the row-by-row chi keeps only five rho/pi results live at
 *    a time. No table lookups for the state, no variable shifts: the
 *    compiler sees the real dependency graph and schedules across the
 *    steps.
 *  - round 0 is written out on the literal initial state, so the compiler
 *    folds it (only 8 data lanes and two padding constants: half the theta
 *    XORs and all the "zero lane ^= D" steps vanish); rounds 1..22 are a
 *    loop over a two-round body; round 23 is written out and its output
 *    uses only lanes 0..3, so dead-code elimination drops the other four
 *    rows of its rho/pi/chi. The loop keeps the hot code at ~2.7 KB (gcc
 *    14, x86-64), one or two pages. Fully unrolling all 24 rounds (~25 KB,
 *    ~5400 instructions, seven pages) is no faster when the front end
 *    streams it well and fragile when it does not: on Zen 3 the straight-
 *    line version ran at 365 or at 830 ns/node from the same binary
 *    depending on which physical pages the page cache happened to back
 *    its code with (a fresh copy of the file, or dropping the page cache,
 *    flipped it; link address, stack position and data addresses did
 *    not), with the instruction-fetch stall cycles doubling in the slow
 *    case. The loop version ran 336-343 ns in every layout and copy
 *    tried, and shows no placement sensitivity on Neoverse N1 either.
 *  - lane complementing (the Keccak team's trick): lanes 1, 2, 8, 12, 17
 *    and 20 are kept inverted. That mask is a fixed point of the round
 *    (theta flips whole columns, pi permutes, chi maps it back onto
 *    itself), and in the inverted representation chi needs one NOT per row
 *    instead of one per lane: a ^ (~b & c) turns into a ^ (b | c),
 *    a ^ (b & c), or a form sharing the row's single NOT. That is 20 fewer
 *    operations per round on CPUs without an and-not instruction (x86-64
 *    without BMI1), and neutral on AArch64 (BIC/ORN). The mask and the
 *    expressions were found by exhaustive search over the 2^25 masks for
 *    the fewest NOTs; the inversions are applied when the node is loaded
 *    and undone on lanes 1 and 2 of the digest.
 *
 * The table-driven version this replaces spent most of its time on loop
 * control, indexed loads/stores of the state in memory and variable-count
 * rotates; this one is ~2.8x faster on Zen 3 (gcc 14 / clang 19) and
 * ~2.7x on Neoverse N1.
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

#define ROL(a, n) (((a) << (n)) | ((a) >> (64 - (n))))

static inline uint64_t ld64(const unsigned char *p) {
    return (uint64_t)p[0] | ((uint64_t)p[1] << 8) | ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24) |
           ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40) | ((uint64_t)p[6] << 48) | ((uint64_t)p[7] << 56);
}

static inline void st64(unsigned char *p, uint64_t v) {
    p[0] = (unsigned char)v;
    p[1] = (unsigned char)(v >> 8);
    p[2] = (unsigned char)(v >> 16);
    p[3] = (unsigned char)(v >> 24);
    p[4] = (unsigned char)(v >> 32);
    p[5] = (unsigned char)(v >> 40);
    p[6] = (unsigned char)(v >> 48);
    p[7] = (unsigned char)(v >> 56);
}

/* One round from lanes A0..A24 into E0..E24 (lane index = x + 5y).
 * Theta: C[x] = column parity, D[x] = C[x-1] ^ rol(C[x+1], 1).
 * Rho/pi: B[y][2x+3y] = rol(A[x][y] ^ D[x], r[x][y]), written row by row
 * of B so chi follows each row at once. Iota on lane 0. */
#define KECCAK_ROUND(A, E, rc)                                                                                  \
    do {                                                                                                       \
        C0 = A##0 ^ A##5 ^ A##10 ^ A##15 ^ A##20;                                                              \
        C1 = A##1 ^ A##6 ^ A##11 ^ A##16 ^ A##21;                                                              \
        C2 = A##2 ^ A##7 ^ A##12 ^ A##17 ^ A##22;                                                              \
        C3 = A##3 ^ A##8 ^ A##13 ^ A##18 ^ A##23;                                                              \
        C4 = A##4 ^ A##9 ^ A##14 ^ A##19 ^ A##24;                                                              \
        D0 = C4 ^ ROL(C1, 1);                                                                                  \
        D1 = C0 ^ ROL(C2, 1);                                                                                  \
        D2 = C1 ^ ROL(C3, 1);                                                                                  \
        D3 = C2 ^ ROL(C4, 1);                                                                                  \
        D4 = C3 ^ ROL(C0, 1);                                                                                  \
        /* row 0 */                                                                                            \
        B0 = A##0 ^ D0;                                                                                        \
        B1 = ROL(A##6 ^ D1, 44);                                                                               \
        B2 = ROL(A##12 ^ D2, 43);                                                                              \
        B3 = ROL(A##18 ^ D3, 21);                                                                              \
        B4 = ROL(A##24 ^ D4, 14);                                                                              \
        N2 = ~B2;                                                                                              \
        E##0 = B0 ^ (B1 | B2) ^ (rc);                                                                          \
        E##1 = B1 ^ (N2 | B3);                                                                                 \
        E##2 = B2 ^ (B3 & B4);                                                                                 \
        E##3 = B3 ^ (B4 | B0);                                                                                 \
        E##4 = B4 ^ (B0 & B1);                                                                                 \
        /* row 1 */                                                                                            \
        B0 = ROL(A##3 ^ D3, 28);                                                                               \
        B1 = ROL(A##9 ^ D4, 20);                                                                               \
        B2 = ROL(A##10 ^ D0, 3);                                                                               \
        B3 = ROL(A##16 ^ D1, 45);                                                                              \
        B4 = ROL(A##22 ^ D2, 61);                                                                              \
        N4 = ~B4;                                                                                              \
        E##5 = B0 ^ (B1 | B2);                                                                                 \
        E##6 = B1 ^ (B2 & B3);                                                                                 \
        E##7 = B2 ^ (B3 | N4);                                                                                 \
        E##8 = B3 ^ (B4 | B0);                                                                                 \
        E##9 = B4 ^ (B0 & B1);                                                                                 \
        /* row 2 */                                                                                            \
        B0 = ROL(A##1 ^ D1, 1);                                                                                \
        B1 = ROL(A##7 ^ D2, 6);                                                                                \
        B2 = ROL(A##13 ^ D3, 25);                                                                              \
        B3 = ROL(A##19 ^ D4, 8);                                                                               \
        B4 = ROL(A##20 ^ D0, 18);                                                                              \
        N3 = ~B3;                                                                                              \
        E##10 = B0 ^ (B1 | B2);                                                                                \
        E##11 = B1 ^ (B2 & B3);                                                                                \
        E##12 = B2 ^ (N3 & B4);                                                                                \
        E##13 = N3 ^ (B4 | B0);                                                                                \
        E##14 = B4 ^ (B0 & B1);                                                                                \
        /* row 3 */                                                                                            \
        B0 = ROL(A##4 ^ D4, 27);                                                                               \
        B1 = ROL(A##5 ^ D0, 36);                                                                               \
        B2 = ROL(A##11 ^ D1, 10);                                                                              \
        B3 = ROL(A##17 ^ D2, 15);                                                                              \
        B4 = ROL(A##23 ^ D3, 56);                                                                              \
        N3 = ~B3;                                                                                              \
        E##15 = B0 ^ (B1 & B2);                                                                                \
        E##16 = B1 ^ (B2 | B3);                                                                                \
        E##17 = B2 ^ (N3 | B4);                                                                                \
        E##18 = N3 ^ (B4 & B0);                                                                                \
        E##19 = B4 ^ (B0 | B1);                                                                                \
        /* row 4 */                                                                                            \
        B0 = ROL(A##2 ^ D2, 62);                                                                               \
        B1 = ROL(A##8 ^ D3, 55);                                                                               \
        B2 = ROL(A##14 ^ D4, 39);                                                                              \
        B3 = ROL(A##15 ^ D0, 41);                                                                              \
        B4 = ROL(A##21 ^ D1, 2);                                                                               \
        N1 = ~B1;                                                                                              \
        E##20 = B0 ^ (N1 & B2);                                                                                \
        E##21 = N1 ^ (B2 | B3);                                                                                \
        E##22 = B2 ^ (B3 & B4);                                                                                \
        E##23 = B3 ^ (B4 | B0);                                                                                \
        E##24 = B4 ^ (B0 & B1);                                                                                \
    } while (0)

/* One node. Kept out of line so the node loop is a loop of calls: inlined,
 * gcc and clang -O3 vectorize the loop across nodes with 2-lane vectors,
 * which have no rotate and run slower than the scalar code.
 *
 * gcc's post-register-allocation scheduler (-fschedule-insns2) under the
 * default x86-64 tuning reorders this straight-line code into a sequence
 * that runs at ~4 IPC instead of ~6.5 on Zen 3 (1.6x slower, same
 * instructions); the pass is switched off for this function. clang does
 * not have the pass and is unaffected. */
#if defined(__GNUC__) && !defined(__clang__)
__attribute__((noinline, optimize("no-schedule-insns2")))
#elif defined(__GNUC__)
__attribute__((noinline))
#elif defined(_MSC_VER)
__declspec(noinline)
#endif
static void keccak256_node(unsigned char *output, const unsigned char *input) {
    {
        uint64_t A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19,
            A20, A21, A22, A23, A24;
        uint64_t E0, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18, E19,
            E20, E21, E22, E23, E24;
        uint64_t B0, B1, B2, B3, B4, C0, C1, C2, C3, C4, D0, D1, D2, D3, D4, N1, N2, N3, N4;

        /* absorb: the node, the 0x01 pad byte at offset 64, the final bit at
         * offset 135; the compiler folds the zero lanes out of round 0 */
        A0 = ld64(input);
        A1 = ~ld64(input + 8);
        A2 = ~ld64(input + 16);
        A3 = ld64(input + 24);
        A4 = ld64(input + 32);
        A5 = ld64(input + 40);
        A6 = ld64(input + 48);
        A7 = ld64(input + 56);
        A8 = ~0x0000000000000001ULL;
        A9 = A10 = A11 = A13 = A14 = A15 = 0;
        A12 = ~0ULL;
        A16 = 0x8000000000000000ULL;
        A17 = A20 = ~0ULL;
        A18 = A19 = A21 = A22 = A23 = A24 = 0;

        /* round 0 on the sparse state: the compiler folds the constant lanes */
        KECCAK_ROUND(A, E, 0x0000000000000001ULL);
        /* rounds 1..22: a loop over a two-round body (the complement mask is
         * a fixed point of the round, so the body is the same each time) */
        for (int r = 1; r < 23; r += 2) {
            KECCAK_ROUND(E, A, RC[r]);
            KECCAK_ROUND(A, E, RC[r + 1]);
        }
        /* round 23: only lanes 0..3 are squeezed, the rest is dead code */
        KECCAK_ROUND(E, A, 0x8000000080008008ULL);

        st64(output, A0);
        st64(output + 8, ~A1);
        st64(output + 16, ~A2);
        st64(output + 24, A3);
    }
}

void keccaktree_keccak256_generic(unsigned char *output, const unsigned char *input, uint64_t count) {
    for (uint64_t k = 0; k < count; k++) keccak256_node(output + 32 * k, input + 64 * k);
}
