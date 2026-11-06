package keccaktree

import (
	"encoding/binary"
	"math/bits"
)

// Pure-Go keccak256 over 64-byte nodes, used when no assembly kernel is
// available (other platforms, CGO_ENABLED=0). A node fits in one 136-byte
// block, so the sponge is a single permutation: lanes 0..7 hold the input,
// lane 8 the Keccak padding byte 0x01, lane 16 the final padding bit. The
// digest is lanes 0..3.
//
// The permutation mirrors src/keccak256_generic.c: the 25 lanes are locals
// (two sets, the rounds alternate between them), each round is written out
// with literal rho offsets and pi destinations, chi runs row by row, and
// lanes 1, 2, 8, 12, 17 and 20 are kept inverted (lane complementing, a
// fixed point of the round) so chi needs one NOT per row instead of one per
// lane. Round 0 is written for the sparse initial state (8 data lanes, two
// padding constants), rounds 1..22 are a loop over a two-round body (lane
// set A to E and back), round 23 computes only the row that is squeezed.
// This file is generated-style code: keep the structure when editing.

var keccakRC = [24]uint64{
	0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
	0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
	0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
	0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
	0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
	0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
}

// keccak256_1_generic computes digests[i] = keccak256(chunks[2i] || chunks[2i+1]).
func keccak256_1_generic(digests [][32]byte, chunks [][32]byte) {
	for i := 0; i+1 < len(chunks); i += 2 {
		l, r := &chunks[i], &chunks[i+1]
		var A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24 uint64
		var E0, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18, E19, E20, E21, E22, E23, E24 uint64
		var B0, B1, B2, B3, B4, C0, C1, C2, C3, C4, D0, D1, D2, D3, D4, N1, N2, N3, N4 uint64

		// absorb; lanes 1 and 2 inverted (complement mask), the zero and padding
		// lanes are folded into round 0 below
		A0 = binary.LittleEndian.Uint64(l[0:8])
		A1 = ^binary.LittleEndian.Uint64(l[8:16])
		A2 = ^binary.LittleEndian.Uint64(l[16:24])
		A3 = binary.LittleEndian.Uint64(l[24:32])
		A4 = binary.LittleEndian.Uint64(r[0:8])
		A5 = binary.LittleEndian.Uint64(r[8:16])
		A6 = binary.LittleEndian.Uint64(r[16:24])
		A7 = binary.LittleEndian.Uint64(r[24:32])

		// round 0 (sparse state: lanes 8, 12, 16, 17, 20 are constants, the rest zero)
		C0 = ^(A0 ^ A5)
		C1 = A1 ^ A6 ^ 0x8000000000000000
		C2 = (A2 ^ A7)
		C3 = A3 ^ 0xfffffffffffffffe
		D0 = A4 ^ bits.RotateLeft64(C1, 1)
		D1 = C0 ^ bits.RotateLeft64(C2, 1)
		D2 = C1 ^ bits.RotateLeft64(C3, 1)
		D3 = C2 ^ bits.RotateLeft64(A4, 1)
		D4 = C3 ^ bits.RotateLeft64(C0, 1)
		B0 = A0 ^ D0
		B1 = bits.RotateLeft64(A6^D1, 44)
		B2 = bits.RotateLeft64(^D2, 43)
		B3 = bits.RotateLeft64(D3, 21)
		B4 = bits.RotateLeft64(D4, 14)
		N2 = ^B2
		E0 = B0 ^ (B1 | B2) ^ 0x0000000000000001
		E1 = B1 ^ (N2 | B3)
		E2 = B2 ^ (B3 & B4)
		E3 = B3 ^ (B4 | B0)
		E4 = B4 ^ (B0 & B1)
		B0 = bits.RotateLeft64(A3^D3, 28)
		B1 = bits.RotateLeft64(D4, 20)
		B2 = bits.RotateLeft64(D0, 3)
		B3 = bits.RotateLeft64(0x8000000000000000^D1, 45)
		B4 = bits.RotateLeft64(D2, 61)
		N4 = ^B4
		E5 = B0 ^ (B1 | B2)
		E6 = B1 ^ (B2 & B3)
		E7 = B2 ^ (B3 | N4)
		E8 = B3 ^ (B4 | B0)
		E9 = B4 ^ (B0 & B1)
		B0 = bits.RotateLeft64(A1^D1, 1)
		B1 = bits.RotateLeft64(A7^D2, 6)
		B2 = bits.RotateLeft64(D3, 25)
		B3 = bits.RotateLeft64(D4, 8)
		B4 = bits.RotateLeft64(^D0, 18)
		N3 = ^B3
		E10 = B0 ^ (B1 | B2)
		E11 = B1 ^ (B2 & B3)
		E12 = B2 ^ (N3 & B4)
		E13 = N3 ^ (B4 | B0)
		E14 = B4 ^ (B0 & B1)
		B0 = bits.RotateLeft64(A4^D4, 27)
		B1 = bits.RotateLeft64(A5^D0, 36)
		B2 = bits.RotateLeft64(D1, 10)
		B3 = bits.RotateLeft64(^D2, 15)
		B4 = bits.RotateLeft64(D3, 56)
		N3 = ^B3
		E15 = B0 ^ (B1 & B2)
		E16 = B1 ^ (B2 | B3)
		E17 = B2 ^ (N3 | B4)
		E18 = N3 ^ (B4 & B0)
		E19 = B4 ^ (B0 | B1)
		B0 = bits.RotateLeft64(A2^D2, 62)
		B1 = bits.RotateLeft64(0xfffffffffffffffe^D3, 55)
		B2 = bits.RotateLeft64(D4, 39)
		B3 = bits.RotateLeft64(D0, 41)
		B4 = bits.RotateLeft64(D1, 2)
		N1 = ^B1
		E20 = B0 ^ (N1 & B2)
		E21 = N1 ^ (B2 | B3)
		E22 = B2 ^ (B3 & B4)
		E23 = B3 ^ (B4 | B0)
		E24 = B4 ^ (B0 & B1)

		// rounds 1..22
		for rc := 1; rc < 23; rc += 2 {
			C0 = E0 ^ E5 ^ E10 ^ E15 ^ E20
			C1 = E1 ^ E6 ^ E11 ^ E16 ^ E21
			C2 = E2 ^ E7 ^ E12 ^ E17 ^ E22
			C3 = E3 ^ E8 ^ E13 ^ E18 ^ E23
			C4 = E4 ^ E9 ^ E14 ^ E19 ^ E24
			D0 = C4 ^ bits.RotateLeft64(C1, 1)
			D1 = C0 ^ bits.RotateLeft64(C2, 1)
			D2 = C1 ^ bits.RotateLeft64(C3, 1)
			D3 = C2 ^ bits.RotateLeft64(C4, 1)
			D4 = C3 ^ bits.RotateLeft64(C0, 1)
			B0 = E0 ^ D0
			B1 = bits.RotateLeft64(E6^D1, 44)
			B2 = bits.RotateLeft64(E12^D2, 43)
			B3 = bits.RotateLeft64(E18^D3, 21)
			B4 = bits.RotateLeft64(E24^D4, 14)
			N2 = ^B2
			A0 = B0 ^ (B1 | B2) ^ keccakRC[rc]
			A1 = B1 ^ (N2 | B3)
			A2 = B2 ^ (B3 & B4)
			A3 = B3 ^ (B4 | B0)
			A4 = B4 ^ (B0 & B1)
			B0 = bits.RotateLeft64(E3^D3, 28)
			B1 = bits.RotateLeft64(E9^D4, 20)
			B2 = bits.RotateLeft64(E10^D0, 3)
			B3 = bits.RotateLeft64(E16^D1, 45)
			B4 = bits.RotateLeft64(E22^D2, 61)
			N4 = ^B4
			A5 = B0 ^ (B1 | B2)
			A6 = B1 ^ (B2 & B3)
			A7 = B2 ^ (B3 | N4)
			A8 = B3 ^ (B4 | B0)
			A9 = B4 ^ (B0 & B1)
			B0 = bits.RotateLeft64(E1^D1, 1)
			B1 = bits.RotateLeft64(E7^D2, 6)
			B2 = bits.RotateLeft64(E13^D3, 25)
			B3 = bits.RotateLeft64(E19^D4, 8)
			B4 = bits.RotateLeft64(E20^D0, 18)
			N3 = ^B3
			A10 = B0 ^ (B1 | B2)
			A11 = B1 ^ (B2 & B3)
			A12 = B2 ^ (N3 & B4)
			A13 = N3 ^ (B4 | B0)
			A14 = B4 ^ (B0 & B1)
			B0 = bits.RotateLeft64(E4^D4, 27)
			B1 = bits.RotateLeft64(E5^D0, 36)
			B2 = bits.RotateLeft64(E11^D1, 10)
			B3 = bits.RotateLeft64(E17^D2, 15)
			B4 = bits.RotateLeft64(E23^D3, 56)
			N3 = ^B3
			A15 = B0 ^ (B1 & B2)
			A16 = B1 ^ (B2 | B3)
			A17 = B2 ^ (N3 | B4)
			A18 = N3 ^ (B4 & B0)
			A19 = B4 ^ (B0 | B1)
			B0 = bits.RotateLeft64(E2^D2, 62)
			B1 = bits.RotateLeft64(E8^D3, 55)
			B2 = bits.RotateLeft64(E14^D4, 39)
			B3 = bits.RotateLeft64(E15^D0, 41)
			B4 = bits.RotateLeft64(E21^D1, 2)
			N1 = ^B1
			A20 = B0 ^ (N1 & B2)
			A21 = N1 ^ (B2 | B3)
			A22 = B2 ^ (B3 & B4)
			A23 = B3 ^ (B4 | B0)
			A24 = B4 ^ (B0 & B1)
			C0 = A0 ^ A5 ^ A10 ^ A15 ^ A20
			C1 = A1 ^ A6 ^ A11 ^ A16 ^ A21
			C2 = A2 ^ A7 ^ A12 ^ A17 ^ A22
			C3 = A3 ^ A8 ^ A13 ^ A18 ^ A23
			C4 = A4 ^ A9 ^ A14 ^ A19 ^ A24
			D0 = C4 ^ bits.RotateLeft64(C1, 1)
			D1 = C0 ^ bits.RotateLeft64(C2, 1)
			D2 = C1 ^ bits.RotateLeft64(C3, 1)
			D3 = C2 ^ bits.RotateLeft64(C4, 1)
			D4 = C3 ^ bits.RotateLeft64(C0, 1)
			B0 = A0 ^ D0
			B1 = bits.RotateLeft64(A6^D1, 44)
			B2 = bits.RotateLeft64(A12^D2, 43)
			B3 = bits.RotateLeft64(A18^D3, 21)
			B4 = bits.RotateLeft64(A24^D4, 14)
			N2 = ^B2
			E0 = B0 ^ (B1 | B2) ^ keccakRC[rc+1]
			E1 = B1 ^ (N2 | B3)
			E2 = B2 ^ (B3 & B4)
			E3 = B3 ^ (B4 | B0)
			E4 = B4 ^ (B0 & B1)
			B0 = bits.RotateLeft64(A3^D3, 28)
			B1 = bits.RotateLeft64(A9^D4, 20)
			B2 = bits.RotateLeft64(A10^D0, 3)
			B3 = bits.RotateLeft64(A16^D1, 45)
			B4 = bits.RotateLeft64(A22^D2, 61)
			N4 = ^B4
			E5 = B0 ^ (B1 | B2)
			E6 = B1 ^ (B2 & B3)
			E7 = B2 ^ (B3 | N4)
			E8 = B3 ^ (B4 | B0)
			E9 = B4 ^ (B0 & B1)
			B0 = bits.RotateLeft64(A1^D1, 1)
			B1 = bits.RotateLeft64(A7^D2, 6)
			B2 = bits.RotateLeft64(A13^D3, 25)
			B3 = bits.RotateLeft64(A19^D4, 8)
			B4 = bits.RotateLeft64(A20^D0, 18)
			N3 = ^B3
			E10 = B0 ^ (B1 | B2)
			E11 = B1 ^ (B2 & B3)
			E12 = B2 ^ (N3 & B4)
			E13 = N3 ^ (B4 | B0)
			E14 = B4 ^ (B0 & B1)
			B0 = bits.RotateLeft64(A4^D4, 27)
			B1 = bits.RotateLeft64(A5^D0, 36)
			B2 = bits.RotateLeft64(A11^D1, 10)
			B3 = bits.RotateLeft64(A17^D2, 15)
			B4 = bits.RotateLeft64(A23^D3, 56)
			N3 = ^B3
			E15 = B0 ^ (B1 & B2)
			E16 = B1 ^ (B2 | B3)
			E17 = B2 ^ (N3 | B4)
			E18 = N3 ^ (B4 & B0)
			E19 = B4 ^ (B0 | B1)
			B0 = bits.RotateLeft64(A2^D2, 62)
			B1 = bits.RotateLeft64(A8^D3, 55)
			B2 = bits.RotateLeft64(A14^D4, 39)
			B3 = bits.RotateLeft64(A15^D0, 41)
			B4 = bits.RotateLeft64(A21^D1, 2)
			N1 = ^B1
			E20 = B0 ^ (N1 & B2)
			E21 = N1 ^ (B2 | B3)
			E22 = B2 ^ (B3 & B4)
			E23 = B3 ^ (B4 | B0)
			E24 = B4 ^ (B0 & B1)
		}

		// round 23: only lanes 0..3 are squeezed
		C0 = E0 ^ E5 ^ E10 ^ E15 ^ E20
		C1 = E1 ^ E6 ^ E11 ^ E16 ^ E21
		C2 = E2 ^ E7 ^ E12 ^ E17 ^ E22
		C3 = E3 ^ E8 ^ E13 ^ E18 ^ E23
		C4 = E4 ^ E9 ^ E14 ^ E19 ^ E24
		D0 = C4 ^ bits.RotateLeft64(C1, 1)
		D1 = C0 ^ bits.RotateLeft64(C2, 1)
		D2 = C1 ^ bits.RotateLeft64(C3, 1)
		D3 = C2 ^ bits.RotateLeft64(C4, 1)
		D4 = C3 ^ bits.RotateLeft64(C0, 1)
		B0 = E0 ^ D0
		B1 = bits.RotateLeft64(E6^D1, 44)
		B2 = bits.RotateLeft64(E12^D2, 43)
		B3 = bits.RotateLeft64(E18^D3, 21)
		B4 = bits.RotateLeft64(E24^D4, 14)
		N2 = ^B2
		A0 = B0 ^ (B1 | B2) ^ 0x8000000080008008
		A1 = B1 ^ (N2 | B3)
		A2 = B2 ^ (B3 & B4)
		A3 = B3 ^ (B4 | B0)
		A4 = B4 ^ (B0 & B1)

		d := &digests[i/2]
		binary.LittleEndian.PutUint64(d[0:8], A0)
		binary.LittleEndian.PutUint64(d[8:16], ^A1)
		binary.LittleEndian.PutUint64(d[16:24], ^A2)
		binary.LittleEndian.PutUint64(d[24:32], A3)
	}
}
