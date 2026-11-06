/*
 * void keccaktree_keccak256_avx2_x8(unsigned char *output,
 *                                   const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, 8 at a time as two
 * independent 4-node batches whose rounds alternate: a round of batch A,
 * then the same round of batch B. The ALUs are the bottleneck of the 4-node
 * rounds of keccak256_avx2.inc, but every round starts with theta, which
 * needs all five parities of the previous round and so leaves the ports
 * idle at each round boundary while that short chain resolves. Here each
 * round computes the other batch's theta (from its parities in memory) in
 * the shadow of its own last chi row, so the next round starts straight
 * into rho and the ports stay busy.
 *
 * The 16 ymm registers only hold one batch's working set, so the parities
 * of the batch that is not in flight stay in memory: STORE_C writes them
 * after each round and the other batch's round reads them for theta, which
 * adds loads and stores but no ALU work. 2..7 remaining nodes go to
 * keccaktree_keccak256_avx2_x4 (which hands 2 to the lane-pair kernel and
 * pads 3), a single one straight to the scalar code.
 *
 * Registers: ymm0..15; rcx, rsi here and the frame's r9..r11.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#define NODES		8
#define VBYTES		32
#define SLOTS		(110*32)		/* 4 state buffers, 2 parity rows */
#define SMALL_TAIL_X1	keccaktree_keccak256_x86_x1
#define SMALL_TAIL	keccaktree_keccak256_avx2_x4
#define SMALL_TAIL_MAX	7
#include "keccak256_x86_frame.inc"

#define RCP		rsi			/* round constants (broadcast) */
#include "keccak256_avx2.inc"

/* frame layout at r9 (= rsp): the two state buffers of each batch and the
 * saved parities of each batch (no spaces: these are macro arguments) */
#define SA0		r9
#define SA1		r9+25*32
#define SB0		r9+50*32
#define SB1		r9+75*32
#define PA		r9+100*32
#define PB		r9+105*32

.text
.p2align 6
/* one batch: 8 nodes at [BIN] -> 8 digests at [BOUT] */
.Lbatch:
	lea		RCP, [rip + .LRC4]
	LOAD		BIN
	ROUND0		SA1, SA0
	STORE_C		PA
	LOAD		BIN+4*64
	ROUND0		SB1, SB0
	STORE_C		PB
	THETA		PA

	/* rounds 1..22, two per iteration, batch A then batch B; each round
	 * leaves the other batch's theta in D0..D4 */
	mov		ecx, 11
1:
	ROUND		SA0, SA1, 32, PB
	STORE_C		PA
	ROUND		SB0, SB1, 32, PA
	STORE_C		PB
	ROUND		SA1, SA0, 64, PB
	STORE_C		PA
	ROUND		SB1, SB0, 64, PA
	STORE_C		PB
	add		RCP, 64
	dec		ecx
	jnz		1b

	ROUND23		SA0, 32, D
	OUTPUT		BOUT
	THETA		PB
	ROUND23		SB0, 32, D
	OUTPUT		BOUT+4*32
	ret

	FUNCTION keccaktree_keccak256_avx2_x8
	AVX2_RODATA

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
