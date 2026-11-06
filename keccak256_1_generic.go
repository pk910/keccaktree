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

var keccakRC = [24]uint64{
	0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
	0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
	0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
	0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
	0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
	0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
}

// rho offsets and pi destinations along pi's 24-cycle starting at lane 1
var keccakRho = [24]int{1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44}
var keccakPi = [24]int{10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1}

func keccakF1600(a *[25]uint64) {
	var c [5]uint64
	for r := 0; r < 24; r++ {
		// theta
		for x := 0; x < 5; x++ {
			c[x] = a[x] ^ a[x+5] ^ a[x+10] ^ a[x+15] ^ a[x+20]
		}
		for x := 0; x < 5; x++ {
			d := c[(x+4)%5] ^ bits.RotateLeft64(c[(x+1)%5], 1)
			for y := 0; y < 25; y += 5 {
				a[y+x] ^= d
			}
		}
		// rho and pi
		t := a[1]
		for i := 0; i < 24; i++ {
			j := keccakPi[i]
			a[j], t = bits.RotateLeft64(t, keccakRho[i]), a[j]
		}
		// chi
		for y := 0; y < 25; y += 5 {
			copy(c[:], a[y:y+5])
			for x := 0; x < 5; x++ {
				a[y+x] = c[x] ^ (^c[(x+1)%5] & c[(x+2)%5])
			}
		}
		// iota
		a[0] ^= keccakRC[r]
	}
}

// keccak256_1_generic computes digests[i] = keccak256(chunks[2i] || chunks[2i+1]).
func keccak256_1_generic(digests [][32]byte, chunks [][32]byte) {
	for i := 0; i+1 < len(chunks); i += 2 {
		var a [25]uint64
		for j := 0; j < 4; j++ {
			a[j] = binary.LittleEndian.Uint64(chunks[i][8*j:])
			a[j+4] = binary.LittleEndian.Uint64(chunks[i+1][8*j:])
		}
		a[8] = 0x01
		a[16] = 0x8000000000000000
		keccakF1600(&a)
		d := &digests[i/2]
		for j := 0; j < 4; j++ {
			binary.LittleEndian.PutUint64(d[8*j:], a[j])
		}
	}
}
