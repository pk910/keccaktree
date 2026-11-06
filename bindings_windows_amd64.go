//go:build cgo && windows && amd64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// links the static library; Detect runs its kernel selection
	ktcgo "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// The AVX-512 path also uses the 256-bit (VL) encodings for short tails.
var hasAVX512 = cpuid.CPU.Supports(cpuid.AVX512F, cpuid.AVX512VL)
var hasAVX2 = cpuid.CPU.Supports(cpuid.AVX2)

// avx512YMM picks avx512vl_x4 over avx512_x8, avx2X4 avx2_x4 over
// avx2_x8. Which of the supported kernels is fastest is not visible in the
// feature bits, so init takes the choice of the C library's detection,
// which times them once (keccaktree_detect in src/keccaktree.c).
var avx512YMM, avx2X4 bool

func init() {
	supportedCPU = hasAVX2 || hasAVX512
	keccaktreeHash = KeccaktreeHash
	if supportedCPU {
		switch ktcgo.Detect() {
		case "avx512vl_x4":
			avx512YMM = true
		case "avx2_x4":
			avx2X4 = true
		}
	}
}
