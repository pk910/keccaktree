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
	case hasSHA3 && armROR:
		return "sha3_x3r"
	case hasSHA3:
		return "sha3_x2"
	case armScalar:
		return "scalar_x1"
	case armHybrid:
		return "neon_x3"
	default:
		return "neon_x2"
	}
}

func forceARM64(supported, sha3, lazy, scalar, ror bool) func() func() {
	return forceARM64h(supported, sha3, lazy, scalar, ror, false)
}

func forceARM64h(supported, sha3, lazy, scalar, ror, hybrid bool) func() func() {
	return func() func() {
		s, s3, l, n, a, h := supportedCPU, hasSHA3, armLazy, armScalar, armROR, armHybrid
		supportedCPU, hasSHA3, armLazy, armScalar, armROR, armHybrid = supported, sha3, lazy, scalar, ror, hybrid
		return func() { supportedCPU, hasSHA3, armLazy, armScalar, armROR, armHybrid = s, s3, l, n, a, h }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceARM64(false, false, false, false, false)},
	{"neon_x2", true, forceARM64(true, false, false, false, false)},
	{"scalar_x1", true, forceARM64(true, false, false, true, false)},
	{"neon_x3", true, forceARM64h(true, false, false, false, false, true)},
	{"sha3_x2", hasSHA3, forceARM64(true, true, false, false, false)},
	{"sha3_x3", hasSHA3, forceARM64(true, true, true, false, false)},
	{"sha3_x3r", hasSHA3, forceARM64(true, true, false, false, true)},
}
