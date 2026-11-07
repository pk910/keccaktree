/* probe: sha3_x2 with 16 nops per round (dispatch-slack test) */
#ifdef __aarch64__
.arch armv8.2-a+sha3
#include "keccak256_arm_frame.inc"
#include "keccak256_neon.inc"
#include "keccak256_sha3.inc"
.purgem ROUND
.macro ROUND r, ARGS
	THETA		PASS
	ROUND_ROWS01	\r, PASS
	ROUND_ROW2	PASS
	ROUND_ROW3	PASS
	ROUND_ROW4	PASS
	.rept 16
	nop
	.endr
.endm
	X2_FUNCTION keccaktree_keccak256_sha3_x2_n16
	GNU_STACK_NOTE
#endif
