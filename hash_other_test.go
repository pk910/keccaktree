//go:build !cgo || !((linux && amd64) || (windows && amd64) || (linux && arm64) || (darwin && arm64))

package keccaktree

// Builds without cgo, or platforms without a prebuilt library, always use the
// pure-Go fallback.
func activePath() string {
	if supportedCPU {
		return "unknown"
	}
	return "generic"
}

var forcedCases = []forcedCase{
	{"generic", true, func() func() {
		saved := supportedCPU
		supportedCPU = false
		return func() { supportedCPU = saved }
	}},
}
