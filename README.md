# keccaktree (prototype)

Batched **keccak256** (Ethereum Keccak, pad `0x01`, not NIST SHA3-256) for
Merkle trees, with the same calling convention as `hashtree`:

```c
void keccaktree_hash(unsigned char *output, const unsigned char *input, uint64_t count);
```

`input` holds `count` 64-byte nodes (two 32-byte children), `output` receives
`count` 32-byte digests, `digest[i] = keccak256(input[64*i .. 64*i+63])`.
`output == input` (in-place layer reduction) is allowed. Define
`KECCAKTREE_HASHTREE_COMPAT` before including `keccaktree.h` to get the
`hashtree_*` names.

| backend | ISA | nodes per batch |
|---|---|---|
| `keccaktree_keccak256_generic` | portable C, any endianness | 1 |
| `keccaktree_keccak256_avx2_x4` | x86-64 AVX2 | 4 |
| `keccaktree_keccak256_avx512vl_x4` | AVX-512F+VL on ymm | 4 |
| `keccaktree_keccak256_avx512_x8` | AVX-512F on zmm | 8 |
| `keccaktree_keccak256_neon_x2` | AArch64 ASIMD | 2 |
| `keccaktree_keccak256_sha3_x2` | AArch64 FEAT_SHA3 (EOR3/RAX1/XAR/BCAX) | 2 |

All backends share one generated, fully unrolled permutation
(`src/keccak256_core*.inc`, from `tools/gen_core.py`) specialised for the
single-block 64-byte case: absorbing is free, round 0 skips the zero lanes and
round 23 only computes the four output lanes.

```shell
cd src
make test                    # ../build/test
make bench HASHTREE=1 HASHTREE_DIR=/path/to/hashtree   # side-by-side with sha256
make CC=aarch64-linux-gnu-gcc AR=aarch64-linux-gnu-ar OUT_DIR=$PWD/../build-arm64 test
```

Tests check the reference sponge against published keccak256/SHA3-256
vectors, then every backend against it for counts 0..300, unaligned buffers
and in-place use. The library output was also cross-checked against Go's
`golang.org/x/crypto/sha3.NewLegacyKeccak256`.
