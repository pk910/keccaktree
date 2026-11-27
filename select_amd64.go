//go:build cgo && (linux || windows) && amd64

package keccaktree

import "github.com/klauspost/cpuid/v2"

// cpuidex runs CPUID with EAX = leaf and ECX = sub (select_amd64.s).
func cpuidex(leaf, sub uint32) (eax, ebx, ecx, edx uint32)

// The AVX-512 path also uses the 256-bit (VL) encodings for short tails,
// and EVEX vpshufb (BW) for the rotations by 8 and 56.
var hasAVX512 = cpuid.CPU.Supports(cpuid.AVX512F, cpuid.AVX512VL, cpuid.AVX512BW)
var hasAVX2 = cpuid.CPU.Supports(cpuid.AVX2)

// BMI1 andn and BMI2 rorx: the scalar kernel x86_x1, which every AVX-512
// and AVX2 kernel hands its last node to and which runs alone without
// them, and the extra nodes of the hybrid kernels (avx512_x9, avx2_x10,
// avx2_x9, avx2_x6, avx2_x5).
var hasBMI = cpuid.CPU.Supports(cpuid.BMI1, cpuid.BMI2)

// The kernels KeccaktreeHash can call: the values are the ones
// wrapper_*_amd64.s switches on (its KERNEL_* defines), the names those of
// the C library (keccaktree_keccak256_<name>).
const (
	kernelAVX2X8 uint8 = iota // also the wrapper's default
	kernelAVX2X4
	kernelAVX2X5
	kernelAVX2X9
	kernelAVX2X10
	kernelX86X1
	kernelAVX512VLX4
	kernelAVX512X8
	kernelAVX2X6
	kernelAVX512X9
	kernelAVX512X8D
	kernelAVX512X9D
	kernelAVX512VLX4D
	kernelAVX2Hybrid
)

var kernelNames = [...]string{
	kernelAVX2X8:      "avx2_x8",
	kernelAVX2X4:      "avx2_x4",
	kernelAVX2X5:      "avx2_x5",
	kernelAVX2X9:      "avx2_x9",
	kernelAVX2X10:     "avx2_x10",
	kernelX86X1:       "x86_x1",
	kernelAVX512VLX4:  "avx512vl_x4",
	kernelAVX512X8:    "avx512_x8",
	kernelAVX2X6:      "avx2_x6",
	kernelAVX512X9:    "avx512_x9",
	kernelAVX512X8D:   "avx512_x8d",
	kernelAVX512X9D:   "avx512_x9d",
	kernelAVX512VLX4D: "avx512vl_x4d",
	kernelAVX2Hybrid:  "avx2_hybrid",
}

// kernel is the one KeccaktreeHash calls, read by the wrapper.
var kernel uint8

// x86CPU is what the kernel selection looks at: the usable instruction set
// extensions and, for the kernels that differ only in how they suit a
// core, the vendor, family, model and core type CPUID reports.
type x86CPU struct {
	bmi, avx2, avx512 bool // usable: CPUID and the OS register state
	fp16              bool // AVX512-FP16 (Sapphire Rapids and later)
	intel, amd        bool // GenuineIntel; AuthenticAMD or HygonGenuine
	family, model     int
	hybrid            bool // CPUID.7:EDX[15], more than one kind of core
	rdpid             bool // CPUID.7:ECX[22]
	atom              bool // CPUID.1AH:EAX[31:24] = 20H on the calling core
}

func hostX86CPU() x86CPU {
	c := x86CPU{
		bmi:    hasBMI,
		avx2:   hasAVX2,
		avx512: hasAVX512,
		fp16:   cpuid.CPU.Supports(cpuid.AVX512FP16),
		intel:  cpuid.CPU.VendorID == cpuid.Intel,
		amd:    cpuid.CPU.VendorID == cpuid.AMD || cpuid.CPU.VendorID == cpuid.Hygon,
		family: cpuid.CPU.Family,
		model:  cpuid.CPU.Model,
	}
	if maxLeaf, _, _, _ := cpuidex(0, 0); maxLeaf >= 7 {
		_, _, ecx, edx := cpuidex(7, 0)
		c.rdpid = ecx&(1<<22) != 0
		// the per-core dispatcher reads leaf 1AH on each core
		c.hybrid = edx&(1<<15) != 0 && maxLeaf >= 0x1a
		if maxLeaf >= 0x1a {
			eax, _, _, _ := cpuidex(0x1a, 0)
			c.atom = eax>>24 == 0x20
		}
	}
	return c
}

// selectKernel picks the kernel for a CPU from what it reports about
// itself, without running or timing anything. It is keccaktree_detect of
// src/keccaktree.c, where the measurements behind each rule are listed;
// the two must stay the same (TestSelectionMatchesC compares them on the
// CPU the tests run on). ok is false when no assembly kernel can run and
// the pure-Go code is used.
func selectKernel(c x86CPU) (id uint8, ok bool) {
	switch {
	case !c.bmi:
		return 0, false
	case c.avx512:
		switch {
		case c.amd && c.family == 0x19: // Zen 4
			return kernelAVX512X9D, true
		case c.intel && c.family == 6 && avx512SinglePort(c.model):
			return kernelAVX512VLX4, true
		case c.intel && !c.fp16: // Skylake-SP .. Ice Lake
			return kernelAVX512X8, true
		}
		return kernelAVX512X8D, true
	case c.avx2:
		switch {
		case c.hybrid && c.rdpid: // P- and E-cores: chosen per call
			return kernelAVX2Hybrid, true
		case c.amd:
			return kernelAVX2X10, true
		case c.intel && !c.hybrid && c.atom: // only E-cores
			return kernelAVX2X6, true
		case c.intel && !c.hybrid:
			return kernelAVX2X8, true
		}
		return kernelAVX2X5, true
	}
	return kernelX86X1, true
}

// avx512SinglePort lists the Intel client cores with one 512-bit ALU port
// (Cannon, Ice, Tiger and Rocket Lake), where the 256-bit kernel is faster.
func avx512SinglePort(model int) bool {
	switch model {
	case 0x66, 0x7d, 0x7e, 0x8c, 0x8d, 0xa7:
		return true
	}
	return false
}

func init() {
	keccaktreeHash = KeccaktreeHash
	kernel, supportedCPU = selectKernel(hostX86CPU())
}
