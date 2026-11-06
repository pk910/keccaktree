//go:build cgo && linux && amd64

package keccaktree

import (
	"github.com/klauspost/cpuid/v2"

	// link to the static library via cgo
	_ "github.com/pk910/keccaktree/cgo"
)

//go:noescape
func KeccaktreeHash(output *byte, input *byte, count uint64)

// The AVX-512 path also uses the 256-bit (VL) encodings for short tails.
var hasAVX512 = cpuid.CPU.Supports(cpuid.AVX512F, cpuid.AVX512VL)
var hasAVX2 = cpuid.CPU.Supports(cpuid.AVX2)

// avx512YMM switches the AVX-512 path from avx512_x8 to the 256-bit
// avx512vl_x4 kernel. Off by default, as in keccaktree_detect
// (src/keccaktree.c): kernels are chosen by feature bits only; the tests
// use it to force the ymm kernel.
var avx512YMM = false

func init() {
	supportedCPU = hasAVX2 || hasAVX512
	keccaktreeHash = KeccaktreeHash
}
