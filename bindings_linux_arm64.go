//go:build cgo && linux && arm64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// link to the static library via cgo
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// FEAT_SHA3 (EOR3/RAX1/XAR/BCAX), from AT_HWCAP.
var hasSHA3 = cpuid.CPU.Supports(cpuid.SHA3)

// Kernel choice between supported kernels, fixed as in keccaktree_detect
// (src/keccaktree.c): with FEAT_SHA3 sha3_x3 (armLazy), without it
// neon_x2. armROR (sha3_x3r) and armScalar (scalar_x1) are off by default
// and only set by the tests to force those kernels.
var armLazy, armROR, armScalar = true, false, false

func init() {
	// NEON / Advanced SIMD is mandatory on every ARMv8-A (AArch64) CPU, so the
	// neon_x2 path is always safe; hasSHA3 only selects the faster sha3_x3 path.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
}
