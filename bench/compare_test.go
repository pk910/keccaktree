// Package bench compares keccaktree with the sha256 hashtree bindings it
// replaces. It is a separate module so the library itself does not depend on
// hashtree-bindings. Run from this directory: go test -bench . -benchtime 2s
package bench

import (
	"crypto/sha256"
	"fmt"
	"math/rand"
	"testing"

	hashtree "github.com/pk910/hashtree-bindings"
	"github.com/pk910/keccaktree"
	"golang.org/x/crypto/sha3"
)

type hashFn func(digests [][32]byte, chunks [][32]byte) error

var libs = []struct {
	name string
	fn   hashFn
}{
	{"sha256-hashtree", hashtree.Hash},
	{"keccak256-keccaktree", keccaktree.Hash},
}

func chunks(pairs int) [][32]byte {
	r := rand.New(rand.NewSource(int64(pairs)))
	c := make([][32]byte, 2*pairs)
	for i := range c {
		r.Read(c[i][:])
	}
	return c
}

// BenchmarkLayer hashes one tree layer of the given number of pairs.
func BenchmarkLayer(b *testing.B) {
	for _, pairs := range []int{1, 4, 8, 16, 64, 1024, 200000} {
		in := chunks(pairs)
		out := make([][32]byte, pairs)
		for _, l := range libs {
			b.Run(fmt.Sprintf("pairs=%d/%s", pairs, l.name), func(b *testing.B) {
				b.SetBytes(int64(64 * pairs))
				for i := 0; i < b.N; i++ {
					l.fn(out, in)
				}
				b.ReportMetric(float64(b.Elapsed().Nanoseconds())/float64(b.N*pairs), "ns/pair")
			})
		}
	}
}

// BenchmarkTreeRoot computes the root of a full binary tree of 2^20 leaves
// layer by layer, in place, the way SSZ merkleization uses these libraries.
func BenchmarkTreeRoot(b *testing.B) {
	const leaves = 1 << 20
	src := chunks(leaves / 2)
	buf := make([][32]byte, leaves)
	for _, l := range libs {
		b.Run(l.name, func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				copy(buf, src)
				layer := buf
				for len(layer) > 1 {
					l.fn(layer, layer)
					layer = layer[:len(layer)/2]
				}
			}
			b.ReportMetric(float64(b.Elapsed().Nanoseconds())/float64(b.N*(leaves-1)), "ns/node")
		})
	}
}

// BenchmarkStdlibOnePair is the no-library baseline: one pair through the
// standard hashers.
func BenchmarkStdlibOnePair(b *testing.B) {
	var in [64]byte
	var out [32]byte
	b.Run("sha256-crypto", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			out = sha256.Sum256(in[:])
		}
	})
	b.Run("keccak256-x-crypto", func(b *testing.B) {
		h := sha3.NewLegacyKeccak256()
		for i := 0; i < b.N; i++ {
			h.Reset()
			h.Write(in[:])
			h.Sum(out[:0])
		}
	})
	_ = out
}
