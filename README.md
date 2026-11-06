# keccaktree

keccaktree is a keccak256 library optimized for Merkle tree computation. It is
a drop-in replacement for [hashtree](https://github.com/OffchainLabs/hashtree)
and its Go bindings: same calls, same chunk layout, only the hash changes from
SHA256 to Ethereum keccak256 (padding `0x01`, not NIST SHA3-256).

```c
void keccaktree_hash(unsigned char *output, const unsigned char *input, uint64_t count);
```

`input` holds `count` chunks of 64 bytes, `output` receives the `count`
32-byte digests, `digest[i] = keccak256(input[64*i .. 64*i+63])`. `output`
may alias `input` for in-place layer reduction. As in hashtree, there are no
length checks. Define `KECCAKTREE_HASHTREE_COMPAT` before including
`keccaktree.h` to get the `hashtree_*` names.

The first call picks the kernel: it probes the CPU features (CPUID, `AT_HWCAP`,
`hw.optional` sysctl, `riscv_hwprobe`), and where more than one kernel is
supported it times them once on a small batch (well under a millisecond) and
keeps the fastest. `keccaktree_init(fn)` sets one explicitly.

## Kernels

All kernels are hand-written assembly in `src/`, one `.S` per kernel on shared
round and frame macros (`.inc`). The header of each file explains its design.

| Platform | Kernels | ns per 64-byte chunk |
|---|---|---|
| x86-64 AVX-512 + BMI2 | `avx512_x9` (avx512_x8 plus one node in the integer registers; Zen 4: +5.5%), `avx512_x8`, `avx512vl_x4` (cores with one 512-bit port); four-round loop bodies (Ice Lake avx512vl_x4 1.3x) | 25 (Xeon; hashtree avx512_x16: 18) |
| x86-64 AVX2 + BMI2 | `avx2_x10`, `avx2_x9`, `avx2_x6`, `avx2_x5`: the AVX2 batches plus one or two nodes hashed in the integer registers (rorx, andn) in the gaps of the vector rounds; picked where the integer ALUs are separate from the vector pipes (Zen 3: x10, Gracemont: x6) | 67 (Zen 3; hashtree avx2_x8: 78, shani: 42) |
| x86-64 AVX2 | `avx2_x8`, `avx2_x4`, `avx2_x2` (2 remaining nodes) | 81 (Zen 3, avx2_x8) |
| x86-64 BMI2 | `x86_x1` (a single node; the single-node tail of the AVX2 kernels) | 219 (Zen 3; hashtree shani: 44) |
| AArch64 FEAT_SHA3 | `sha3_x3` (Neoverse), `sha3_x3r` (Apple), `sha3_x2` | 122 (Neoverse N2), 66 (Apple M1) |
| AArch64 | `neon_x3` (Neoverse N1), `scalar_x1`, `neon_x2` | 216 (Neoverse N1; hashtree neon_x4: 257) |
| RISC-V 64 | `rvv_zvkb`, `rvv`, `zbb_x1`, `rv64_x1` | not measured on hardware |
| any | `generic` (portable C, lane-complemented rounds) | 220 (Zen 3), 350 (Neoverse N1) |

Every kernel can also be called directly (`keccaktree_keccak256_<kernel>`).
Calling a kernel on a CPU that does not support it is undefined behavior.

## Building

The only build dependency is a GCC or clang compatible compiler and assembler.

```shell
make          # build/lib/libkeccaktree.a, build/test, build/bench
make test && ./build/test
make bench && ./build/bench
make bench HASHTREE=1 HASHTREE_DIR=/path/to/hashtree   # also bench hashtree (built in build/)
```

Cross compile with `CC`, e.g. `CC=aarch64-linux-gnu-gcc make` or
`CC=x86_64-w64-mingw32-gcc make test`.

## Bindings

Prebuilt static libraries for linux amd64/arm64/riscv64, darwin arm64 and
windows amd64 are in [`lib/`](lib/README.md). CI builds them on native
runners and attests their provenance. All bindings link these libraries.

- **Go** (`github.com/pk910/keccaktree`): `Hash(digests, chunks)` and
  `HashByteSlice`, with the same signatures and errors as hashtree-bindings,
  so switching is an import change. Other platforms and `CGO_ENABLED=0` use
  a pure-Go fallback (the unrolled generic round in Go). `bench/` compares it with hashtree-bindings.
- **Rust** (`Cargo.toml`, `src/lib.rs`): `keccaktree::hash(&mut out, &chunks, count)`
  with the hashtree-rs signature, `hash_in_place`, `hash_chunks`, `Backend`.
  `--features build-from-source` compiles `src/` instead of linking `lib/`.
- **Nim** (`keccaktree_abi.nimble`): `import keccaktree_abi`, like hashtree's
  `hashtree_abi`. `-d:keccaktreeFromSource` compiles `src/`.
- **Java** (`java/`, JNI, Java 11+): `Keccaktree.hash(out, in)`, with offsets,
  in-place and direct `ByteBuffer` variants. `java/build-native.sh` builds
  the JNI library from `lib/`.

## Contributing

CI tests pull requests against the libraries committed in `lib/`, so a pull
request that changes `src/` must commit rebuilt libraries. Run
`.github/scripts/build-pr-libs.sh` to cross-compile all of them with zig.
These are temporary: after the merge, CI rebuilds them on main with native
toolchains and attests them.

`.github/workflows/bench.yml` runs `build/bench` on GitHub's x86-64, Neoverse
N2 and Apple M1 runners. Start it by hand or push to a `bench/**` branch.
