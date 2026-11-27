//go:build cgo && (linux || windows) && amd64

package keccaktree

import "testing"

// activePath mirrors wrapper_*_amd64.s: the kernel id picked by init, behind
// the supportedCPU gate.
func activePath() string {
	if !supportedCPU {
		return "generic"
	}
	return kernelNames[kernel]
}

func forceAMD64(supported bool, k uint8) func() func() {
	return func() func() {
		s, id := supportedCPU, kernel
		supportedCPU, kernel = supported, k
		return func() { supportedCPU, kernel = s, id }
	}
}

var forcedCases = []forcedCase{
	{"generic", true, forceAMD64(false, kernelAVX2X8)},
	{"avx2_x8", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X8)},
	{"avx2_x4", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X4)},
	{"avx2_x5", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X5)},
	{"avx2_x6", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X6)},
	{"avx2_x9", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X9)},
	{"avx2_x10", hasAVX2 && hasBMI, forceAMD64(true, kernelAVX2X10)},
	{"avx2_hybrid", hasAVX2 && hasBMI && hostX86CPU().rdpid, forceAMD64(true, kernelAVX2Hybrid)},
	{"x86_x1", hasBMI, forceAMD64(true, kernelX86X1)},
	{"avx512_x8", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512X8)},
	{"avx512_x9", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512X9)},
	{"avx512vl_x4", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512VLX4)},
	{"avx512_x8d", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512X8D)},
	{"avx512_x9d", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512X9D)},
	{"avx512vl_x4d", hasAVX512 && hasBMI, forceAMD64(true, kernelAVX512VLX4D)},
}

// selectKernel on CPUs the tests do not run on: the cores each rule was
// written for, as CPUID describes them.
func TestSelectKernelTable(t *testing.T) {
	for _, c := range []struct {
		name string
		cpu  x86CPU
		want string
	}{
		{"no BMI", x86CPU{avx2: true}, "generic"},
		{"BMI only", x86CPU{bmi: true}, "x86_x1"},
		{"Zen 3", x86CPU{bmi: true, avx2: true, amd: true, family: 0x19}, "avx2_x10"},
		{"Haswell", x86CPU{bmi: true, avx2: true, intel: true, family: 6, model: 0x3c}, "avx2_x8"},
		{"Alder Lake-N", x86CPU{bmi: true, avx2: true, intel: true, family: 6, rdpid: true, atom: true}, "avx2_x6"},
		{"Raptor Lake", x86CPU{bmi: true, avx2: true, intel: true, family: 6, hybrid: true, rdpid: true}, "avx2_hybrid"},
		{"Raptor Lake, started on an E-core", x86CPU{bmi: true, avx2: true, intel: true, family: 6, hybrid: true, rdpid: true, atom: true}, "avx2_hybrid"},
		{"hybrid without RDPID", x86CPU{bmi: true, avx2: true, intel: true, family: 6, hybrid: true}, "avx2_x5"},
		{"other vendor", x86CPU{bmi: true, avx2: true}, "avx2_x5"},
		{"Zen 4", x86CPU{bmi: true, avx2: true, avx512: true, amd: true, family: 0x19}, "avx512_x9d"},
		{"Zen 5", x86CPU{bmi: true, avx2: true, avx512: true, amd: true, family: 0x1a}, "avx512_x8d"},
		{"Tiger Lake", x86CPU{bmi: true, avx2: true, avx512: true, intel: true, family: 6, model: 0x8c}, "avx512vl_x4"},
		{"Ice Lake server", x86CPU{bmi: true, avx2: true, avx512: true, intel: true, family: 6, model: 0x6a}, "avx512_x8"},
		{"Sapphire Rapids", x86CPU{bmi: true, avx2: true, avx512: true, fp16: true, intel: true, family: 6, model: 0x8f}, "avx512_x8d"},
	} {
		got := "generic"
		if id, ok := selectKernel(c.cpu); ok {
			got = kernelNames[id]
		}
		if got != c.want {
			t.Errorf("%s: selected %s, want %s", c.name, got, c.want)
		}
	}
}
