/* probe: sha3_x2 with 66 extra independent vector EORs per round written
 * to the dead D registers (doubles the vector ALU work: 4-pipe throughput
 * test; predicted 132/4 = 33 cycles per round if the pipes are the bound) */
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
	.rept 22
	eor		v25.16b, v0.16b, v1.16b
	eor		v26.16b, v2.16b, v3.16b
	eor		v27.16b, v4.16b, v5.16b
	.endr
.endm
	X2_FUNCTION keccaktree_keccak256_sha3_x2_v66
	GNU_STACK_NOTE
#endif
