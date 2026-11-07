/* probe: sha3_x2 with 16 extra independent vector EORs per round on the
 * dead D registers (vector-pipe pressure test) */
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
	.rept 4
	eor		v25.16b, v25.16b, v26.16b
	eor		v26.16b, v26.16b, v27.16b
	eor		v27.16b, v27.16b, v28.16b
	eor		v28.16b, v28.16b, v29.16b
	.endr
.endm
	X2_FUNCTION keccaktree_keccak256_sha3_x2_v16
	GNU_STACK_NOTE
#endif
