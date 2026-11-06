//go:build cgo && linux && amd64

// The C kernels run on this frame's 8192 bytes of stack. SP is moved to the
// top of the frame and 32-byte aligned. Deepest kernel: avx2_x10, 5744
// bytes of frame plus the pushed rbp/rbx/r12..r15, the return address, up
// to 63 bytes of 64-byte alignment and the batch call, under 5.9 KB; the
// tails (x10 -> x8 -> x4 -> avx2_x2 / x86_x1) are jumps after the frame is
// torn down, so they do not add up.
//
// Kernel ids, as in bindings_linux_amd64.go (kernelAVX2X8 is the default).
#define KERNEL_AVX2_X4     1
#define KERNEL_AVX2_X5     2
#define KERNEL_AVX2_X9     3
#define KERNEL_AVX2_X10    4
#define KERNEL_X86_X1      5
#define KERNEL_AVX512VL_X4 6
#define KERNEL_AVX512_X8   7
#define KERNEL_AVX2_X6     8

TEXT ·KeccaktreeHash(SB), 0, $8192-24
	MOVQ output+0(FP), DI
	MOVQ input+8(FP), SI
	MOVQ count+16(FP), DX

	MOVQ SP, BX
	ADDQ $8192, SP
	ANDQ $~31, SP

	MOVBLZX ·kernel(SB), AX
	CMPB AX, $KERNEL_AVX2_X10
	JE   avx2x10
	CMPB AX, $KERNEL_AVX2_X9
	JE   avx2x9
	CMPB AX, $KERNEL_AVX2_X5
	JE   avx2x5
	CMPB AX, $KERNEL_AVX2_X6
	JE   avx2x6
	CMPB AX, $KERNEL_AVX2_X4
	JE   avx2x4
	CMPB AX, $KERNEL_X86_X1
	JE   x86x1
	CMPB AX, $KERNEL_AVX512_X8
	JE   avx512x8
	CMPB AX, $KERNEL_AVX512VL_X4
	JE   avx512vlx4
	CALL keccaktree_keccak256_avx2_x8(SB)
	JMP  epilog

avx2x10:
	CALL keccaktree_keccak256_avx2_x10(SB)
	JMP  epilog

avx2x9:
	CALL keccaktree_keccak256_avx2_x9(SB)
	JMP  epilog

avx2x5:
	CALL keccaktree_keccak256_avx2_x5(SB)
	JMP  epilog

avx2x6:
	CALL keccaktree_keccak256_avx2_x6(SB)
	JMP  epilog

avx2x4:
	CALL keccaktree_keccak256_avx2_x4(SB)
	JMP  epilog

x86x1:
	CALL keccaktree_keccak256_x86_x1(SB)
	JMP  epilog

avx512x8:
	CALL keccaktree_keccak256_avx512_x8(SB)
	JMP  epilog

avx512vlx4:
	CALL keccaktree_keccak256_avx512vl_x4(SB)

epilog:
	MOVQ BX, SP
	RET
