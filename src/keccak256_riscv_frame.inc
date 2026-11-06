/*
 * Shared by the RISC-V (RV64, Linux ELF) kernels: function prologue/epilogue
 * macros and the round constant table.
 *
 * Calling convention (LP64D): a0 = output, a1 = input, a2 = count;
 * ra, sp, s0..s11 are callee-saved, a0..a7 and t0..t6 are not. gp and tp
 * are never touched (gp may be used for linker relaxation, tp is the
 * thread pointer). v0..v31 and vtype/vl are caller-saved.
 */
.macro FUNCTION name
.text
.p2align 2
.globl \name
.type \name,%function
\name:
.endm

.macro END_FUNCTION name
.size \name, .-\name
.endm

/* the 24 round constants, loaded with `ld t, .LRC + 8*r` (auipc + ld) */
.macro KECCAK_RC
.section .rodata
.p2align 3
.LRC:
	.quad 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000
	.quad 0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009
	.quad 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a
	.quad 0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003
	.quad 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a
	.quad 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
.text
.endm

.macro GNU_STACK_NOTE
.section .note.GNU-stack,"",@progbits
.endm
