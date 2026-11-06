/*
 * void keccaktree_keccak256_x86_x1(unsigned char *output,
 *                                  const unsigned char *input, uint64_t count)
 *
 * keccak256 (Ethereum, pad 0x01) of count 64-byte nodes, one at a time in
 * the general registers with the rounds of keccak256_x86_scalar.inc, all
 * 24 unrolled. Needs BMI1 (andn) and BMI2 (rorx). This is the single-node
 * path of the AVX2 kernels: a padded 4-node vector batch costs four
 * nodes' worth of vector work, and the portable C code it replaces spends
 * a third of its instructions on loop control and lane shuffling, where
 * this kernel's rounds are straight-line ALU work (130 operations per
 * round, see the .inc).
 *
 * Calling convention: SysV (rdi, rsi, rdx) or Windows x64 (rcx, rdx, r8),
 * where rsi and rdi are callee-saved. Uses all 15 general registers:
 * the pointers and the count live on the stack.
 */
#ifdef __x86_64__
.intel_syntax noprefix

#include "keccak256_x86_frame.inc"

#define B0	rax
#define B1	rbx
#define B2	rcx
#define B3	rdx
#define B4	rsi
#define C0	rdi
#define C1	rbp
#define C2	r8
#define C3	r9
#define C4	r10
#define D0	r11
#define D1	r12
#define D2	r13
#define D3	r14
#define T	r15

/* frame at rsp: the two state buffers, the D4 spill, the saved output
 * pointer, input pointer and count */
#define S0	0
#define S1	200
#define D4S	400
#define OUTP	408
#define INP	416
#define CNT	424
#define FRAME_X1	432

#include "keccak256_x86_scalar.inc"

.text
.p2align 6
.globl keccaktree_keccak256_x86_x1
#ifndef _WIN64
.type keccaktree_keccak256_x86_x1,%function
#endif
keccaktree_keccak256_x86_x1:
	push		rbp
	push		rbx
	push		r12
	push		r13
	push		r14
	push		r15
#ifdef _WIN64
	push		rsi
	push		rdi
#endif
	sub		rsp, FRAME_X1
	test		ARG_COUNT, ARG_COUNT
	jz		2f
	mov		qword ptr [rsp + OUTP], ARG_OUT
	mov		qword ptr [rsp + INP], ARG_IN
	mov		qword ptr [rsp + CNT], ARG_COUNT
	mov		T, ARG_IN
1:	/* one node: the 8 words at [T] */
	mov		B0, qword ptr [T + 0]
	mov		B1, qword ptr [T + 8]
	mov		B2, qword ptr [T + 16]
	mov		B3, qword ptr [T + 24]
	mov		B4, qword ptr [T + 32]
	mov		C0, qword ptr [T + 40]
	mov		C1, qword ptr [T + 48]
	mov		C2, qword ptr [T + 56]
	KECCAK_X1
	add		qword ptr [rsp + OUTP], 32
	mov		T, qword ptr [rsp + INP]
	add		T, 64
	mov		qword ptr [rsp + INP], T
	dec		qword ptr [rsp + CNT]
	jnz		1b
2:
	add		rsp, FRAME_X1
#ifdef _WIN64
	pop		rdi
	pop		rsi
#endif
	pop		r15
	pop		r14
	pop		r13
	pop		r12
	pop		rbx
	pop		rbp
	ret
#ifndef _WIN64
.size keccaktree_keccak256_x86_x1, .-keccaktree_keccak256_x86_x1
#endif

	KECCAK_RODATA

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
#endif
