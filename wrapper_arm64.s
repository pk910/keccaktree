//go:build cgo && arm64

// The C kernels run below this frame on its 2048 bytes of stack.
// Selection mirrors keccaktree_detect in src/keccaktree.c.
TEXT ·KeccaktreeHash(SB), 0, $2048-24
	MOVD output+0(FP), R0
	MOVD input+8(FP), R1
	MOVD count+16(FP), R2

	MOVBU ·hasSHA3(SB), R19
	MOVBU ·armLazy(SB), R20
	MOVBU ·armROR(SB), R21
	CBZ   R19, nosha3
	CBNZ  R20, sha3x3
	CBNZ  R21, sha3x3r
	BL    keccaktree_keccak256_sha3_x2(SB)
	RET

sha3x3:
	BL keccaktree_keccak256_sha3_x3(SB)
	RET

sha3x3r:
	BL keccaktree_keccak256_sha3_x3r(SB)
	RET

nosha3:
	MOVBU ·armScalar(SB), R20
	CBNZ  R20, scalar
	BL    keccaktree_keccak256_neon_x2(SB)
	RET

scalar:
	BL keccaktree_keccak256_scalar_x1(SB)
	RET
