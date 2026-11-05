//go:build cgo && arm64

// The C kernels run below this frame on its 2048 bytes of stack.
TEXT ·KeccaktreeHash(SB), 0, $2048-24
	MOVD output+0(FP), R0
	MOVD input+8(FP), R1
	MOVD count+16(FP), R2

	MOVBU ·hasSHA3(SB), R19
	CBNZ  R19, sha3

	BL keccaktree_keccak256_neon_x2(SB)
	RET

sha3:
	BL keccaktree_keccak256_sha3_x2(SB)
	RET
