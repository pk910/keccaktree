// Package keccaktree hashes Merkle tree layers with keccak256 (Ethereum
// Keccak-256, pad 0x01). It is a drop-in replacement for
// github.com/pk910/hashtree-bindings: same functions, same errors, same
// chunk layout, only the hash function differs.
package keccaktree

import (
	"errors"
	"fmt"
	"unsafe"
)

var (
	// ErrOddChunks is returned when the number of chunks is odd.
	ErrOddChunks = errors.New("odd number of chunks")
	// ErrNotEnoughDigests is returned when the number of digests is not enough.
	ErrNotEnoughDigests = errors.New("not enough digest length")
	// ErrChunksNotMultipleOf64 is returned when the chunks are not multiple of 64 bytes.
	ErrChunksNotMultipleOf64 = errors.New("chunks not multiple of 64 bytes")
	// ErrDigestsNotMultipleOf32 is returned when the digests are not multiple of 32 bytes.
	ErrDigestsNotMultipleOf32 = errors.New("digests not multiple of 32 bytes")
)

var supportedCPU = false
var keccaktreeHash func(output *byte, input *byte, count uint64)

const (
	chunksPerAsmIter = 16 // widest dispatch path (AVX-512, 8 pairs), so no path is left a scalar tail
	maxAsmIters      = 128
	maxAsmChunks     = chunksPerAsmIter * maxAsmIters
)

// hashChunked bounds how many chunks reach a single keccaktreeHash call: the
// native code is not asynchronously preemptible, so hashing a whole layer in
// one call blocks every GC for its duration.
func hashChunked(digests [][32]byte, chunks [][32]byte) {
	for len(chunks) > maxAsmChunks {
		keccaktreeHash(&digests[0][0], &chunks[0][0], maxAsmChunks/2)
		chunks = chunks[maxAsmChunks:]
		digests = digests[maxAsmChunks/2:]
	}
	if len(chunks) > 1 {
		keccaktreeHash(&digests[0][0], &chunks[0][0], uint64(len(chunks)/2))
	}
}

// Hash hashes the chunks two at the time and outputs the digests on the first
// argument: digests[i] = keccak256(chunks[2i] || chunks[2i+1]). It does check
// for lengths on the inputs. digests may alias the start of chunks.
func Hash(digests [][32]byte, chunks [][32]byte) error {
	if len(chunks) == 0 {
		return nil
	}

	if len(chunks)%2 == 1 {
		return ErrOddChunks
	}
	if len(digests) < len(chunks)/2 {
		return fmt.Errorf("%w: need at least %v, got %v", ErrNotEnoughDigests, len(chunks)/2, len(digests))
	}
	if supportedCPU {
		hashChunked(digests, chunks)
	} else {
		keccak256_1_generic(digests, chunks)
	}
	return nil
}

// HashByteSlice is the same as hash but it takes byte slices instead of slices of arrays.
func HashByteSlice(digests []byte, chunks []byte) error {
	if len(chunks) == 0 {
		return nil
	}

	if len(chunks)%64 != 0 {
		return ErrChunksNotMultipleOf64
	}

	if len(digests)%32 != 0 {
		return ErrDigestsNotMultipleOf32
	}

	if len(digests) < len(chunks)/2 {
		return fmt.Errorf("%w: need at least %v, got %v", ErrNotEnoughDigests, len(chunks)/2, len(digests))
	}
	// We use an unsafe pointer to cast []byte to [][32]byte. The length and
	// capacity of the slice need to be divided accordingly by 32.
	sizeChunks := (len(chunks) >> 5)
	chunkedChunks := unsafe.Slice((*[32]byte)(unsafe.Pointer(&chunks[0])), sizeChunks)

	sizeDigests := (len(digests) >> 5)
	chunkedDigest := unsafe.Slice((*[32]byte)(unsafe.Pointer(&digests[0])), sizeDigests)
	return Hash(chunkedDigest, chunkedChunks)
}
