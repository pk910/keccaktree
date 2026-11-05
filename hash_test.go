package keccaktree

import (
	"bytes"
	"encoding/hex"
	"errors"
	"fmt"
	"math/rand"
	"os"
	"testing"

	"golang.org/x/crypto/sha3"
)

// referenceParent returns the expected Merkle parent for a 64-byte pair,
// computed with golang.org/x/crypto/sha3's legacy Keccak-256, an independent
// implementation used as the known-answer oracle.
func referenceParent(left, right [32]byte) [32]byte {
	h := sha3.NewLegacyKeccak256()
	h.Write(left[:])
	h.Write(right[:])
	var out [32]byte
	h.Sum(out[:0])
	return out
}

// genChunks deterministically generates 2*pairs chunks from a seed.
func genChunks(pairs int, seed int64) [][32]byte {
	r := rand.New(rand.NewSource(seed))
	chunks := make([][32]byte, 2*pairs)
	for i := range chunks {
		r.Read(chunks[i][:])
	}
	return chunks
}

// verifyHash checks Hash against the x/crypto oracle, against the pure-Go
// fallback, for determinism, for HashByteSlice parity and for in-place use.
func verifyHash(t *testing.T, chunks [][32]byte) {
	t.Helper()
	pairs := len(chunks) / 2

	digests := make([][32]byte, pairs)
	if err := Hash(digests, chunks); err != nil {
		t.Fatalf("Hash returned error: %v", err)
	}

	for i := 0; i < pairs; i++ {
		if want := referenceParent(chunks[2*i], chunks[2*i+1]); digests[i] != want {
			t.Fatalf("pair %d/%d: digest mismatch vs x/crypto keccak256\n got  %x\n want %x",
				i, pairs, digests[i], want)
		}
	}

	ref := make([][32]byte, pairs)
	keccak256_1_generic(ref, chunks)
	for i := 0; i < pairs; i++ {
		if digests[i] != ref[i] {
			t.Fatalf("pair %d/%d: optimized path != pure-Go generic\n opt %x\n gen %x",
				i, pairs, digests[i], ref[i])
		}
	}

	again := make([][32]byte, pairs)
	if err := Hash(again, chunks); err != nil {
		t.Fatalf("Hash (2nd call) error: %v", err)
	}
	for i := 0; i < pairs; i++ {
		if again[i] != digests[i] {
			t.Fatalf("pair %d: non-deterministic output\n 1st %x\n 2nd %x", i, digests[i], again[i])
		}
	}

	if pairs > 0 {
		flatChunks := make([]byte, 0, pairs*64)
		for _, c := range chunks {
			flatChunks = append(flatChunks, c[:]...)
		}
		flatDigests := make([]byte, pairs*32)
		if err := HashByteSlice(flatDigests, flatChunks); err != nil {
			t.Fatalf("HashByteSlice error: %v", err)
		}
		for i := 0; i < pairs; i++ {
			if !bytes.Equal(flatDigests[32*i:32*i+32], digests[i][:]) {
				t.Fatalf("pair %d: HashByteSlice != Hash\n bs  %x\n h   %x",
					i, flatDigests[32*i:32*i+32], digests[i][:])
			}
		}

		// In place: the digests overwrite the first half of the chunk buffer.
		inplace := append([][32]byte(nil), chunks...)
		if err := Hash(inplace, inplace); err != nil {
			t.Fatalf("in-place Hash error: %v", err)
		}
		for i := 0; i < pairs; i++ {
			if inplace[i] != digests[i] {
				t.Fatalf("pair %d: in-place result differs\n got  %x\n want %x", i, inplace[i], digests[i])
			}
		}
	}
}

// sizeSet covers boundaries around every SIMD lane width (x1/x2/x4/x8) and the
// per-call chunk bound, so the batch loops and their tails are all exercised.
var sizeSet = []int{
	0, 1, 2, 3, 4, 5, 7, 8, 9, 12, 15, 16, 17, 31, 32, 33,
	63, 64, 65, 127, 128, 129, 255, 256, 257, 1000, 1023, 1024, 1025, 2049,
}

func TestHashSizes(t *testing.T) {
	for _, n := range sizeSet {
		t.Run(fmt.Sprintf("pairs=%d", n), func(t *testing.T) {
			verifyHash(t, genChunks(n, int64(n)+1))
		})
	}
}

func TestHashLarge(t *testing.T) {
	verifyHash(t, genChunks(10000, 0x5eed))
}

func TestHashStructured(t *testing.T) {
	mk := func(pairs int, fill func(i int) [32]byte) [][32]byte {
		c := make([][32]byte, 2*pairs)
		for i := range c {
			c[i] = fill(i)
		}
		return c
	}
	cases := map[string][][32]byte{
		"zeros": mk(64, func(int) [32]byte { return [32]byte{} }),
		"ones": mk(64, func(int) [32]byte {
			var b [32]byte
			for j := range b {
				b[j] = 0xff
			}
			return b
		}),
		"seq": mk(64, func(i int) [32]byte {
			var b [32]byte
			for j := range b {
				b[j] = byte(i + j)
			}
			return b
		}),
	}
	for name, chunks := range cases {
		t.Run(name, func(t *testing.T) { verifyHash(t, chunks) })
	}
}

// TestZeroHashChain validates chained use (Merkle zero-subtree hashes) against
// the oracle and a hardcoded canonical anchor.
func TestZeroHashChain(t *testing.T) {
	// keccak256(0^64): zero-subtree hash at depth 1 of keccak Merkle trees.
	const z1Hex = "ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5"

	var z [32]byte
	for k := 1; k <= 40; k++ {
		d := make([][32]byte, 1)
		if err := Hash(d, [][32]byte{z, z}); err != nil {
			t.Fatalf("level %d: %v", k, err)
		}
		if want := referenceParent(z, z); d[0] != want {
			t.Fatalf("level %d: %x != oracle %x", k, d[0], want)
		}
		if k == 1 {
			if got := hex.EncodeToString(d[0][:]); got != z1Hex {
				t.Fatalf("zerohash[1] = %s, want %s", got, z1Hex)
			}
		}
		z = d[0]
	}
}

func TestErrors(t *testing.T) {
	if err := Hash(make([][32]byte, 1), make([][32]byte, 3)); !errors.Is(err, ErrOddChunks) {
		t.Errorf("odd chunks: got %v, want ErrOddChunks", err)
	}
	if err := Hash(make([][32]byte, 1), make([][32]byte, 4)); !errors.Is(err, ErrNotEnoughDigests) {
		t.Errorf("short digests: got %v, want ErrNotEnoughDigests", err)
	}
	if err := Hash(nil, nil); err != nil {
		t.Errorf("empty: got %v, want nil", err)
	}
	if err := HashByteSlice(make([]byte, 32), make([]byte, 63)); !errors.Is(err, ErrChunksNotMultipleOf64) {
		t.Errorf("chunks not mult 64: got %v, want ErrChunksNotMultipleOf64", err)
	}
	if err := HashByteSlice(make([]byte, 31), make([]byte, 64)); !errors.Is(err, ErrDigestsNotMultipleOf32) {
		t.Errorf("digests not mult 32: got %v, want ErrDigestsNotMultipleOf32", err)
	}
	if err := HashByteSlice(make([]byte, 32), make([]byte, 128)); !errors.Is(err, ErrNotEnoughDigests) {
		t.Errorf("byteslice short digests: got %v, want ErrNotEnoughDigests", err)
	}
}

// forcedCase forces a specific implementation by temporarily overriding the
// detection state; supported reports whether the host CPU can run that path.
// The cases per architecture live in the hash_<arch>_test.go files.
type forcedCase struct {
	name      string
	supported bool
	apply     func() (restore func())
}

// TestForcedPaths runs the functional core against every dispatch branch the
// host CPU can execute, regardless of what detection would pick.
func TestForcedPaths(t *testing.T) {
	for _, fc := range forcedCases {
		t.Run(fc.name, func(t *testing.T) {
			if !fc.supported {
				t.Skipf("host CPU does not support the %q path", fc.name)
			}
			restore := fc.apply()
			defer restore()
			for _, n := range []int{1, 2, 3, 5, 8, 17, 100, 1000} {
				verifyHash(t, genChunks(n, int64(n)*7+1))
			}
		})
	}
}

// TestActivePathMatchesEnv asserts the naturally selected implementation
// matches KECCAKTREE_EXPECT_PATH (set per emulated -cpu by the CI matrix).
func TestActivePathMatchesEnv(t *testing.T) {
	want := os.Getenv("KECCAKTREE_EXPECT_PATH")
	if want == "" {
		t.Skip("KECCAKTREE_EXPECT_PATH not set")
	}
	if got := activePath(); got != want {
		t.Fatalf("active path = %q, want %q (CPU detection / -cpu mismatch)", got, want)
	}
	t.Logf("active path = %q (supportedCPU=%v)", want, supportedCPU)
}
