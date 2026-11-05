//go:build cgo && linux && amd64

// The C kernels run on this frame's 2048 bytes of stack (deepest: avx2_x4,
// about 1.3 KB). SP is moved to the top of the frame and 32-byte aligned.
TEXT ·KeccaktreeHash(SB), 0, $2048-24
	MOVQ output+0(FP), DI
	MOVQ input+8(FP), SI
	MOVQ count+16(FP), DX

	MOVQ SP, BX
	ADDQ $2048, SP
	ANDQ $~31, SP

	CMPB ·hasAVX512(SB), $1
	JE   avx512
	CALL keccaktree_keccak256_avx2_x4(SB)
	JMP  epilog

avx512:
	CALL keccaktree_keccak256_avx512_x8(SB)

epilog:
	MOVQ BX, SP
	RET
