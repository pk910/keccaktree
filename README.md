# keccaktree

Batched **keccak256** (Ethereum Keccak-256, pad `0x01`, not NIST SHA3-256)
for Merkle trees. It is a drop-in replacement for
[hashtree](https://github.com/OffchainLabs/hashtree) and its Go bindings
[hashtree-bindings](https://github.com/pk910/hashtree-bindings): same calls,
same chunk layout, only the hash function changes.

`digest[i] = keccak256(chunk[2i] || chunk[2i+1])`

## Go

```go
import keccaktree "github.com/pk910/keccaktree"

digests := make([][32]byte, len(chunks)/2)
err := keccaktree.Hash(digests, chunks)        // or HashByteSlice(digestBytes, chunkBytes)
```

`Hash`, `HashByteSlice` and the error values match hashtree-bindings, so
switching is an import change. `digests` may alias `chunks` (in-place layer
reduction).

The bindings follow the hashtree-bindings layout: the `cgo` subpackage links a
prebuilt static library from `lib/<platform>/`, and small Go assembly wrappers
call the best kernel directly, chosen with `klauspost/cpuid`:

| Platform | Kernels |
|---|---|
| linux/amd64, windows/amd64 | AVX-512 x8 (ymm x4 on Intel client cores), AVX2 x4 |
| linux/arm64 | SHA3+scalar hybrid x3 (Neoverse N2/V1/V2, Graviton 3/4), SHA3 x2 (other FEAT_SHA3 cores), scalar x1 (Neoverse N1, Graviton 2), NEON x2 |
| darwin/arm64 | ARMv8.2 SHA3 x2 (Apple M-series) |
| everything else, or `CGO_ENABLED=0` | pure Go (generated from the same core) |

`lib/` is rebuilt and committed by the *Update Static Libraries* workflow
whenever `src/` changes on `main`.

## C

```c
#include "keccaktree.h"
void keccaktree_hash(unsigned char *output, const unsigned char *input, uint64_t count);
```

`input` holds `count` 64-byte nodes, `output` receives `count` 32-byte
digests. Define `KECCAKTREE_HASHTREE_COMPAT` before including the header to
get the `hashtree_*` names. The SIMD and scalar kernels are hand-written
assembly in `src/asm/`, one file per kernel on top of shared round and frame
macros (`keccak256_avx512.inc`, `keccak256_neon.inc`, `keccak256_scalar.inc`):
the 25 lanes stay in registers, every round names each lane's register, so
pi is register renaming, and the first and last rounds skip the zero lanes
and the unused output lanes. The AArch64 files assemble for ELF and Mach-O.
The generic C fallback (and the pure Go one) come from one generated,
fully unrolled permutation (`tools/gen_core.py`) specialised for the
single-block 64-byte case.

Performance notes:

- **x86-64.** The AVX-512 x8 kernel issues 90 vector instructions per round
  plus 10 register copies (`vpternlogq` is destructive), keeps lanes 0..4 in
  memory to fit the 32 registers, and runs at the limit of the two 512-bit
  ports (~100 cycles per node on Ice Lake server). AVX2 x4 keeps the state in
  two stack buffers (16 registers) and is likewise bound by its three vector
  ports. Interleaving a scalar BMI2 stream with either (as on ARM) was
  measured at 2x slower: with 16 general registers the scalar state spills.
  Intel client cores with AVX-512 (Ice/Tiger/Rocket Lake) have only one
  512-bit ALU port, so dispatch picks the 256-bit `avx512vl_x4` kernel there.
  A single-node AVX2 call goes to the scalar code (25% faster on Zen 3).
- **AArch64.** `sha3_x2` is 67 instructions per round with no moves or
  spills (EOR3, RAX1, XAR, BCAX). `scalar_x1` keeps every lane in a lazily
  rotated form, with the rotation offsets tracked by the assembler: rho costs
  nothing, because EOR and BIC rotate their second operand for free, leaving
  106 instructions per round in 30 general registers. `sha3_x3`
  interleaves that scalar stream with the SHA3 x2 vector stream, so the
  integer ALUs work while the vector pipes are busy. Neoverse cores issue
  every SHA3 instruction on a single vector pipe, one per cycle, so
  `sha3_x3` additionally computes four of the five chi outputs of each row
  as BIC + EOR for the second pipe and pipelines the round (row 4's chi
  overlaps the next theta, each row's chi the next row's rho) to keep both
  pipes fed. On Neoverse N2 (GitHub `ubuntu-24.04-arm`): sha3_x3 122
  ns/node vs sha3_x2 220 (1.8x), scalar_x1 195 vs 322 for plain C. Apple
  cores execute a rotated operand slowly (scalar_x1 is 2x slower than plain
  C on M1) and run SHA3 instructions on every pipe, so they keep sha3_x2;
  the choice is made from the MIDR implementer.

`.github/workflows/bench.yml` runs `bench` (all kernels next to hashtree's
sha256 kernels) on GitHub's Apple M1, Neoverse N2 and x86-64 runners; start it
by hand or push to a `bench/**` branch.

```shell
make -C src test && ./build/test
make -C src bench HASHTREE=1 HASHTREE_DIR=/path/to/hashtree && ./build/bench
```

## Benchmarks

`bench/` is a separate Go module comparing keccaktree with hashtree-bindings:

```shell
cd bench && go test -bench . -count 6
```

## Tests

- C: reference sponge checked against published keccak256 / SHA3-256 vectors,
  then every backend for counts 0..300, unaligned buffers and in-place use.
- Go: every result checked against `golang.org/x/crypto/sha3`
  `NewLegacyKeccak256`, every dispatch path forced, plus a qemu CPU matrix
  (`.github/scripts/test-matrix.sh`).
