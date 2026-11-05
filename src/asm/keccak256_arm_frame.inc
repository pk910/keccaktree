/*
 * Shared by the AArch64 kernels: function prologue/epilogue macros for ELF
 * (Linux) and Mach-O (macOS) objects, and the round constant table. The
 * table lives in .text right after the code, so the kernels load constants
 * with pc-relative literal loads and need no pointer register.
 *
 * Calling convention (both ABIs): x0 = output, x1 = input, x2 = count;
 * x19..x28, d8..d15 (low halves) are callee-saved; x18 is reserved on macOS
 * and never used here.
 */
.macro FUNCTION name
.text
.p2align 4
#ifdef __APPLE__
.globl _\name
_\name:
#else
.globl \name
.type \name,%function
\name:
#endif
.endm

.macro END_FUNCTION name
#ifndef __APPLE__
.size \name, .-\name
#endif
.endm

/* the 24 round constants, each in both 64-bit lanes: ldr q, .LRC + 16*r
 * for the vector kernels, ldr x, .LRC + 16*r for the scalar ones */
.macro KECCAK_RC
.p2align 4
.LRC:
	.quad 0x0000000000000001, 0x0000000000000001
	.quad 0x0000000000008082, 0x0000000000008082
	.quad 0x800000000000808a, 0x800000000000808a
	.quad 0x8000000080008000, 0x8000000080008000
	.quad 0x000000000000808b, 0x000000000000808b
	.quad 0x0000000080000001, 0x0000000080000001
	.quad 0x8000000080008081, 0x8000000080008081
	.quad 0x8000000000008009, 0x8000000000008009
	.quad 0x000000000000008a, 0x000000000000008a
	.quad 0x0000000000000088, 0x0000000000000088
	.quad 0x0000000080008009, 0x0000000080008009
	.quad 0x000000008000000a, 0x000000008000000a
	.quad 0x000000008000808b, 0x000000008000808b
	.quad 0x800000000000008b, 0x800000000000008b
	.quad 0x8000000000008089, 0x8000000000008089
	.quad 0x8000000000008003, 0x8000000000008003
	.quad 0x8000000000008002, 0x8000000000008002
	.quad 0x8000000000000080, 0x8000000000000080
	.quad 0x000000000000800a, 0x000000000000800a
	.quad 0x800000008000000a, 0x800000008000000a
	.quad 0x8000000080008081, 0x8000000080008081
	.quad 0x8000000000008080, 0x8000000000008080
	.quad 0x0000000080000001, 0x0000000080000001
	.quad 0x8000000080008008, 0x8000000080008008
.LK1:	.quad 0x0000000000000001, 0x0000000000000001
.LK63:	.quad 0x8000000000000000, 0x8000000000000000
.endm

.macro GNU_STACK_NOTE
#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
.endm
