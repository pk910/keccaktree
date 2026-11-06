//go:build cgo && windows && amd64

// Windows x64 ABI: arguments in CX, DX, R8. R8 is saved in R12, which the
// callee preserves. The C kernels run on this frame's 8192 bytes of stack
// (deepest: avx2_x10, 5824 bytes of frame, 5951 with its pushed registers,
// alignment and batch call, see wrapper_linux_amd64.s; 5983 with the
// shadow space). The top 32 bytes are the shadow space the Windows ABI
// gives every callee, which compiled C code may write to.
//
// Kernel ids, as in bindings_windows_amd64.go (kernelAVX2X8 is the default).
#define KERNEL_AVX2_X4     1
#define KERNEL_AVX2_X5     2
#define KERNEL_AVX2_X9     3
#define KERNEL_AVX2_X10    4
#define KERNEL_X86_X1      5
#define KERNEL_AVX512VL_X4 6
#define KERNEL_AVX512_X8   7
#define KERNEL_AVX2_X6     8
#define KERNEL_AVX512_X9   9

TEXT ·KeccaktreeHash(SB), 0, $8192-24
	MOVQ output+0(FP), CX
	MOVQ input+8(FP), DX
	MOVQ R8, R12
	MOVQ count+16(FP), R8

	MOVQ SP, BX
	ADDQ $(8192-32), SP
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
	CMPB AX, $KERNEL_AVX512_X9
	JE   avx512x9
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

avx512x9:
	CALL keccaktree_keccak256_avx512_x9(SB)
	JMP  epilog

avx512x8:
	CALL keccaktree_keccak256_avx512_x8(SB)
	JMP  epilog

avx512vlx4:
	CALL keccaktree_keccak256_avx512vl_x4(SB)

epilog:
	MOVQ BX, SP
	MOVQ R12, R8
	RET
