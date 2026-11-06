//go:build ((linux || windows) && amd64) || ((linux || darwin) && arm64) || (linux && riscv64)

package cgo

/*
#cgo CFLAGS: -I${SRCDIR}/../src
#include "keccaktree.h"

// Name of the kernel keccaktree_detect picks; the Go wrappers call the
// kernels directly and set their dispatch flags from it.
static const char* keccaktree_go_detect(void) {
	keccaktree_hash_fcn f = keccaktree_detect();
#ifdef __x86_64__
	if (f == keccaktree_keccak256_avx512_x9) return "avx512_x9";
	if (f == keccaktree_keccak256_avx512_x8) return "avx512_x8";
	if (f == keccaktree_keccak256_avx512vl_x4) return "avx512vl_x4";
	if (f == keccaktree_keccak256_avx2_x10) return "avx2_x10";
	if (f == keccaktree_keccak256_avx2_x9) return "avx2_x9";
	if (f == keccaktree_keccak256_avx2_x5) return "avx2_x5";
	if (f == keccaktree_keccak256_avx2_x6) return "avx2_x6";
	if (f == keccaktree_keccak256_avx2_x8) return "avx2_x8";
	if (f == keccaktree_keccak256_avx2_x4) return "avx2_x4";
	if (f == keccaktree_keccak256_x86_x1) return "x86_x1";
#endif
#ifdef __aarch64__
	if (f == keccaktree_keccak256_sha3_x3) return "sha3_x3";
	if (f == keccaktree_keccak256_sha3_x3r) return "sha3_x3r";
	if (f == keccaktree_keccak256_sha3_x2) return "sha3_x2";
	if (f == keccaktree_keccak256_neon_x3) return "neon_x3";
	if (f == keccaktree_keccak256_scalar_x1) return "scalar_x1";
	if (f == keccaktree_keccak256_neon_x2) return "neon_x2";
#endif
#if defined(__riscv) && __riscv_xlen == 64
	if (f == keccaktree_keccak256_rvv_zvkb) return "rvv_zvkb";
	if (f == keccaktree_keccak256_rvv) return "rvv";
	if (f == keccaktree_keccak256_zbb_x1) return "zbb_x1";
	if (f == keccaktree_keccak256_rv64_x1) return "rv64_x1";
#endif
	return "generic";
}
*/
import "C"

// Detect returns the name of the kernel the C library's auto-detection
// picks on this CPU: it probes the CPU features, then times the supported
// kernels once on a small batch and keeps the fastest. Each call measures
// again, so call it once.
func Detect() string {
	return C.GoString(C.keccaktree_go_detect())
}
