//go:build cgo && darwin && arm64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// link to the static library via cgo
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// FEAT_SHA3 (EOR3/RAX1/XAR/BCAX), from the hw.optional sysctls.
var hasSHA3 = cpuid.CPU.Supports(cpuid.SHA3)

// Kernel choice between supported kernels, fixed as in keccaktree_detect
// (src/keccaktree.c): with FEAT_SHA3 the arm64 macOS default sha3_x3r
// (armROR), without it neon_x2. armLazy (sha3_x3) and armScalar
// (scalar_x1) are only set by the tests to force those kernels.
var armLazy, armROR, armScalar = false, true, false

func init() {
	// NEON / Advanced SIMD is mandatory on every ARMv8-A (AArch64) CPU, so the
	// neon_x2 path is always safe; hasSHA3 only selects the faster sha3_x3r path.
	supportedCPU = true
	keccaktreeHash = KeccaktreeHash
}
