package keccaktree

import (
	"fmt"
	"testing"
)

func benchHash(b *testing.B, pairs int, generic bool) {
	chunks := genChunks(pairs, 1)
	digests := make([][32]byte, pairs)
	b.SetBytes(int64(pairs * 64))
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if generic {
			keccak256_1_generic(digests, chunks)
		} else {
			Hash(digests, chunks)
		}
	}
	b.ReportMetric(float64(b.Elapsed().Nanoseconds())/float64(b.N*pairs), "ns/pair")
}

func BenchmarkHash(b *testing.B) {
	for _, n := range []int{1, 4, 8, 16, 64, 1024, 200000} {
		b.Run(fmt.Sprintf("pairs=%d", n), func(b *testing.B) { benchHash(b, n, false) })
	}
}

func BenchmarkHashGeneric(b *testing.B) {
	for _, n := range []int{1, 1024} {
		b.Run(fmt.Sprintf("pairs=%d", n), func(b *testing.B) { benchHash(b, n, true) })
	}
}
