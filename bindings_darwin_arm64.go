//go:build cgo && darwin && arm64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// link to the static library via cgo
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// FEAT_SHA3 (EOR3/RAX1/XAR/BCAX): Apple M-series, Graviton 3+, Neoverse V1/N2+.
var hasSHA3 = cpuid.CPU.Supports(cpuid.SHA3)

// Apple cores run EOR/BIC with a rotated operand slowly, so the
// lazy-rotation kernels (sha3_x3, scalar_x1) are never selected here;
// armApple picks sha3_x3r, the hybrid with explicit rotations.
var armLazy, armN1, armApple = false, false, true

func init() {
	// NEON / Advanced SIMD is mandatory on every ARMv8-A (AArch64) CPU, so the
	// neon_x2 path is always safe; hasSHA3 only selects the faster sha3_x2 path.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
}
