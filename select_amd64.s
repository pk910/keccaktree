//go:build cgo && (linux || windows) && amd64

#include "textflag.h"

// func cpuidex(leaf, sub uint32) (eax, ebx, ecx, edx uint32)
TEXT ·cpuidex(SB), NOSPLIT, $0-24
	MOVL leaf+0(FP), AX
	MOVL sub+4(FP), CX
	CPUID
	MOVL AX, eax+8(FP)
	MOVL BX, ebx+12(FP)
	MOVL CX, ecx+16(FP)
	MOVL DX, edx+20(FP)
	RET
