//go:build cgo && (linux || darwin) && arm64

package keccaktree

// activePath mirrors wrapper_arm64.s (NEON is mandatory on ARMv8, so
// supportedCPU is always true).
func activePath() string {
	switch {
	case !supportedCPU:
		return "generic"
	case hasSHA3 && armLazy:
		return "sha3_x3"
	case hasSHA3:
		return "sha3_x2"
	case armN1:
		return "scalar_x1"
	default:
		return "neon_x2"
	}
}

func forceARM64(supported, sha3, lazy, n1 bool) func() func() {
	return func() func() {
		s, s3, l, n := supportedCPU, hasSHA3, armLazy, armN1
		supportedCPU, hasSHA3, armLazy, armN1 = supported, sha3, lazy, n1
		return func() { supportedCPU, hasSHA3, armLazy, armN1 = s, s3, l, n }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceARM64(false, false, false, false)},
	{"neon_x2", true, forceARM64(true, false, false, false)},
	{"scalar_x1", true, forceARM64(true, false, false, true)},
	{"sha3_x2", hasSHA3, forceARM64(true, true, false, false)},
	{"sha3_x3", hasSHA3, forceARM64(true, true, true, false)},
}
