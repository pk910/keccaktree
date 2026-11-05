//go:build cgo && (linux || darwin) && arm64

package keccaktree

// activePath mirrors wrapper_arm64.s: sha3_x2 when FEAT_SHA3 is present, else
// neon_x2 (NEON is mandatory on ARMv8, so supportedCPU is always true).
func activePath() string {
	switch {
	case !supportedCPU:
		return "generic"
	case hasSHA3:
		return "sha3_x2"
	default:
		return "neon_x2"
	}
}

func forceARM64(supported, sha3 bool) func() func() {
	return func() func() {
		s, s3 := supportedCPU, hasSHA3
		supportedCPU, hasSHA3 = supported, sha3
		return func() { supportedCPU, hasSHA3 = s, s3 }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceARM64(false, false)},
	{"neon_x2", true, forceARM64(true, false)},
	{"sha3_x2", hasSHA3, forceARM64(true, true)},
}
