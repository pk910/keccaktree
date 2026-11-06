//go:build cgo && (linux || darwin) && arm64

package keccaktree

// activePath mirrors wrapper_arm64.s: the kernel id picked by init (NEON is
// mandatory on ARMv8, so supportedCPU is always true).
func activePath() string {
	if !supportedCPU {
		return "generic"
	}
	return kernelNames[kernel]
}

func forceARM64(supported bool, k uint8) func() func() {
	return func() func() {
		s, id := supportedCPU, kernel
		supportedCPU, kernel = supported, k
		return func() { supportedCPU, kernel = s, id }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceARM64(false, kernelNeonX2)},
	{"neon_x2", true, forceARM64(true, kernelNeonX2)},
	{"neon_x3", true, forceARM64(true, kernelNeonX3)},
	{"scalar_x1", true, forceARM64(true, kernelScalarX1)},
	{"sha3_x2", hasSHA3, forceARM64(true, kernelSha3X2)},
	{"sha3_x3", hasSHA3, forceARM64(true, kernelSha3X3)},
	{"sha3_x3r", hasSHA3, forceARM64(true, kernelSha3X3r)},
}
