/*
 * Function frame shared by the x86-64 batch kernels. The including file
 * defines NODES (nodes per batch), VBYTES (vector register size), a local
 * label .Lbatch that hashes NODES nodes from [BIN] to [BOUT], and
 * optionally SLOTS (bytes of kernel scratch, default two rows of lanes),
 * SMALL_TAIL, a function that handles 1..SMALL_TAIL_MAX remaining nodes
 * faster than a padded batch (or, with SMALL_TAIL_MAX_VAR, up to the count
 * in that quadword, which the kernel can expose for run-time calibration),
 * and SMALL_TAIL_X1, one that handles a single remaining node (so that a
 * node need not pass through every smaller kernel's frame on its way to
 * the scalar code).
 *
 * Calling convention: SysV (rdi, rsi, rdx) or Windows x64 (rcx, rdx, r8),
 * where xmm6..15, rsi and rdi are callee-saved. Inside, rdi = output,
 * rsi = input, rdx = count on both, and r9 points at the 64-byte aligned
 * frame: VMEM slots first, then the tail buffers. A kernel that uses the
 * callee-saved rbx and r12..r15 defines SAVE_GPRS: the frame pushes them
 * after rbp and restores them on exit.
 */
#ifdef _WIN64
#define ARG_OUT		rcx
#define ARG_IN		rdx
#define ARG_COUNT	r8
#else
#define ARG_OUT		rdi
#define ARG_IN		rsi
#define ARG_COUNT	rdx
#endif
#define BIN		r10		/* batch input */
#define BOUT		r11		/* batch output */

#ifndef SLOTS
#define SLOTS		(10*VBYTES)		/* two rows of 5 lanes */
#endif
#define TAIL_IN		SLOTS			/* NODES x 64 bytes */
#define TAIL_OUT	(TAIL_IN + NODES*64)	/* NODES x 32 bytes */
#define SAVE		(TAIL_OUT + NODES*32)	/* Windows: xmm6..15, rsi, rdi */
#define FRAME		(SAVE + 10*16 + 16)

.macro FUNCTION name
.text
.p2align 6
.globl \name
#ifndef _WIN64
.type \name,%function
#endif
\name:
	push		rbp
	mov		rbp, rsp
#ifdef SAVE_GPRS
	push		rbx
	push		r12
	push		r13
	push		r14
	push		r15
#endif
	sub		rsp, FRAME
	and		rsp, -64
#ifdef _WIN64
	vmovdqu		xmmword ptr [rsp + SAVE + 0*16], xmm6
	vmovdqu		xmmword ptr [rsp + SAVE + 1*16], xmm7
	vmovdqu		xmmword ptr [rsp + SAVE + 2*16], xmm8
	vmovdqu		xmmword ptr [rsp + SAVE + 3*16], xmm9
	vmovdqu		xmmword ptr [rsp + SAVE + 4*16], xmm10
	vmovdqu		xmmword ptr [rsp + SAVE + 5*16], xmm11
	vmovdqu		xmmword ptr [rsp + SAVE + 6*16], xmm12
	vmovdqu		xmmword ptr [rsp + SAVE + 7*16], xmm13
	vmovdqu		xmmword ptr [rsp + SAVE + 8*16], xmm14
	vmovdqu		xmmword ptr [rsp + SAVE + 9*16], xmm15
	mov		qword ptr [rsp + SAVE + 10*16], rsi
	mov		qword ptr [rsp + SAVE + 10*16 + 8], rdi
	mov		rdi, ARG_OUT
	mov		rsi, ARG_IN
	mov		rdx, ARG_COUNT
#endif
	mov		r9, rsp
	mov		BIN, rsi
	mov		BOUT, rdi
1:	/* full batches */
	cmp		rdx, NODES
	jb		2f
	call		.Lbatch
	add		BIN, NODES*64
	add		BOUT, NODES*32
	sub		rdx, NODES
	jmp		1b
2:	/* 0 < count < NODES */
	test		rdx, rdx
	jz		4f
#ifdef SMALL_TAIL_X1
	cmp		rdx, 1
	jne		7f
	mov		eax, 2
	jmp		5f
7:
#endif
#ifdef SMALL_TAIL
#ifdef SMALL_TAIL_MAX_VAR
	cmp		rdx, qword ptr [rip + SMALL_TAIL_MAX_VAR]
#else
	cmp		rdx, SMALL_TAIL_MAX
#endif
	ja		3f
	mov		eax, 1
	jmp		5f
3:
#endif
	/* hash a copy in the stack buffer; lanes past count hash whatever is
	 * there and are not stored. The copies are vector loops, not rep movsb:
	 * at these sizes (64..448 bytes) rep movsb's startup costs more than
	 * the copy itself (Zen 3: ~20 ns per tail with rep movsb, ~5 with
	 * ymm moves). */
	mov		rax, rdx
	mov		rsi, BIN
	lea		rdi, [rsp + TAIL_IN]
	mov		rcx, rax
7:	vmovdqu		ymm0, ymmword ptr [rsi]
	vmovdqu		ymm1, ymmword ptr [rsi + 32]
	vmovdqu		ymmword ptr [rdi], ymm0
	vmovdqu		ymmword ptr [rdi + 32], ymm1
	add		rsi, 64
	add		rdi, 64
	dec		rcx
	jnz		7b
	mov		rdi, BOUT
	lea		BIN, [rsp + TAIL_IN]
	lea		BOUT, [rsp + TAIL_OUT]
	call		.Lbatch
	lea		rsi, [rsp + TAIL_OUT]
	mov		rcx, rax
8:	vmovdqu		ymm0, ymmword ptr [rsi]
	vmovdqu		ymmword ptr [rdi], ymm0
	add		rsi, 32
	add		rdi, 32
	dec		rcx
	jnz		8b
4:	/* done */
	xor		eax, eax
5:	/* eax != 0: tail-call SMALL_TAIL (1) or SMALL_TAIL_X1 (2) for the
	 * rest (rdx nodes) */
	vzeroupper
#ifdef _WIN64
	vmovdqu		xmm6,  xmmword ptr [rsp + SAVE + 0*16]
	vmovdqu		xmm7,  xmmword ptr [rsp + SAVE + 1*16]
	vmovdqu		xmm8,  xmmword ptr [rsp + SAVE + 2*16]
	vmovdqu		xmm9,  xmmword ptr [rsp + SAVE + 3*16]
	vmovdqu		xmm10, xmmword ptr [rsp + SAVE + 4*16]
	vmovdqu		xmm11, xmmword ptr [rsp + SAVE + 5*16]
	vmovdqu		xmm12, xmmword ptr [rsp + SAVE + 6*16]
	vmovdqu		xmm13, xmmword ptr [rsp + SAVE + 7*16]
	vmovdqu		xmm14, xmmword ptr [rsp + SAVE + 8*16]
	vmovdqu		xmm15, xmmword ptr [rsp + SAVE + 9*16]
	mov		rsi, qword ptr [rsp + SAVE + 10*16]
	mov		rdi, qword ptr [rsp + SAVE + 10*16 + 8]
#endif
#ifdef SAVE_GPRS
	lea		rsp, [rbp - 40]
	pop		r15
	pop		r14
	pop		r13
	pop		r12
	pop		rbx
#else
	mov		rsp, rbp
#endif
	pop		rbp
#if defined(SMALL_TAIL) || defined(SMALL_TAIL_X1)
	test		eax, eax
	jz		6f
	mov		ARG_COUNT, rdx
	mov		ARG_OUT, BOUT
	mov		ARG_IN, BIN
#ifdef SMALL_TAIL_X1
	cmp		eax, 2
	je		SMALL_TAIL_X1
#endif
#ifdef SMALL_TAIL
	jmp		SMALL_TAIL
#endif
6:
#endif
	ret
#ifndef _WIN64
.size \name, .-\name
#endif
.endm

/* constants shared by the kernels */
.macro KECCAK_RODATA
#ifdef _WIN64
.section .rdata,"dr"
#else
.section .rodata
#endif
.p2align 6
.LKECCAK_RC:
	.quad 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000
	.quad 0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009
	.quad 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a
	.quad 0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003
	.quad 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a
	.quad 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
.LK1:	.quad 0x0000000000000001
.LK63:	.quad 0x8000000000000000
.endm
