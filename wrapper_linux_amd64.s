//go:build cgo && linux && amd64

// The C kernels run on this frame's 8192 bytes of stack (deepest: avx2_x8,
// about 4.5 KB). SP is moved to the top of the frame and 32-byte aligned.
TEXT ·KeccaktreeHash(SB), 0, $8192-24
	MOVQ output+0(FP), DI
	MOVQ input+8(FP), SI
	MOVQ count+16(FP), DX

	MOVQ SP, BX
	ADDQ $8192, SP
	ANDQ $~31, SP

	CMPB ·hasAVX512(SB), $1
	JE   avx512
	CMPB ·avx2X4(SB), $1
	JE   avx2x4
	CALL keccaktree_keccak256_avx2_x8(SB)
	JMP  epilog

avx2x4:
	CALL keccaktree_keccak256_avx2_x4(SB)
	JMP  epilog

avx512:
	CMPB ·avx512YMM(SB), $1
	JE   avx512ymm
	CALL keccaktree_keccak256_avx512_x8(SB)
	JMP  epilog

avx512ymm:
	CALL keccaktree_keccak256_avx512vl_x4(SB)

epilog:
	MOVQ BX, SP
	RET
