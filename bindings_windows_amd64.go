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
// The AVX2 kernels hand their last node to the scalar BMI1/BMI2 kernel.
var hasAVX2 = cpuid.CPU.Supports(cpuid.AVX2, cpuid.BMI1, cpuid.BMI2)

// The hybrid AVX2 kernels (avx2_x10, avx2_x9, avx2_x5) hash one or two
// extra nodes in the integer registers with BMI1 andn and BMI2 rorx.
var hasBMI = cpuid.CPU.Supports(cpuid.BMI1, cpuid.BMI2)

// The kernels KeccaktreeHash can call: the values are the ones
// wrapper_*_amd64.s switches on (its KERNEL_* defines), the names the ones
// cgo.Detect returns. Which of the supported kernels is fastest is not
// visible in the feature bits, so init takes the choice of the C library's
// detection, which times them once (keccaktree_detect in src/keccaktree.c).
const (
	kernelAVX2X8 uint8 = iota // also the wrapper's default
	kernelAVX2X4
	kernelAVX2X5
	kernelAVX2X9
	kernelAVX2X10
	kernelAVX512VLX4
	kernelAVX512X8
)

var kernelNames = [...]string{
	kernelAVX2X8:     "avx2_x8",
	kernelAVX2X4:     "avx2_x4",
	kernelAVX2X5:     "avx2_x5",
	kernelAVX2X9:     "avx2_x9",
	kernelAVX2X10:    "avx2_x10",
	kernelAVX512VLX4: "avx512vl_x4",
	kernelAVX512X8:   "avx512_x8",
}

// kernel is the one KeccaktreeHash calls, read by the wrapper.
var kernel uint8

// kernelByName maps a cgo.Detect name to the wrapper's kernel id. A name
// the wrapper does not know (a kernel added to the C library but not
// wired here yet) falls back to the widest kernel of the feature tier.
func kernelByName(name string) uint8 {
	for id, n := range kernelNames {
		if n == name {
			return uint8(id)
		}
	}
	if hasAVX512 {
		return kernelAVX512X8
	}
	return kernelAVX2X8
}

func init() {
	supportedCPU = hasAVX2 || hasAVX512
	keccaktreeHash = KeccaktreeHash
	if supportedCPU {
		kernel = kernelByName(ktcgo.Detect())
	}
}
