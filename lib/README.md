# Static libraries

Built from `src/` and attested by the *Update Static Libraries* workflow
(`.github/workflows/build-static-libs.yml`). Each platform directory has
`libkeccaktree.a`, its `.sha256`, and, for CI builds, a `.buildinfo` with the
exact compiler. `SOURCE_COMMIT` names the commit the libraries were built from.

| Platform | Toolchain (CI) | Kernels |
|---|---|---|
| linux_amd64 | ubuntu-22.04 gcc | avx512_x8, avx512vl_x4, avx2_x8, avx2_x4, generic |
| linux_arm64 | ubuntu-22.04-arm gcc | sha3_x3, sha3_x3r, sha3_x2, scalar_x1, neon_x2, generic |
| darwin_arm64 | macos-15 Apple clang | sha3_x3, sha3_x3r, sha3_x2, scalar_x1, neon_x2, generic |
| windows_amd64 | MSYS2 MINGW64 gcc | avx512_x8, avx512vl_x4, avx2_x8, avx2_x4, generic |

Builds use `SOURCE_DATE_EPOCH` and `-ffile-prefix-map`, then
`strip --strip-debug` and `ranlib` (macOS additionally zeroes `ar` member
metadata), so a rebuild with the same compiler is byte-identical.

## Pull requests

The libraries on main are always built by CI with the native toolchains in
the table above and carry a GitHub build provenance attestation. A pull
request cannot produce those, but its CI tests the Go bindings against the
libraries committed here, so a PR that changes `src/` commits **temporary**
libraries of its own:

- `.github/scripts/build-libs.sh` cross-compiles all four on one host with
  `zig cc`. Zig is used for nothing else: it is only a convenience for these
  throwaway PR builds, so a contributor needs no Mac or Windows machine.
- or `.github/scripts/fetch-ci-libs.sh` copies the artifacts of a *Build &
  Test* run on the PR branch (`gh workflow run build.yml --ref <branch>`).

After the merge, *Update Static Libraries* rebuilds every library on main
with the native toolchains, replaces the PR's temporary copies, and records
the attestation:

    gh attestation verify lib/linux_amd64/libkeccaktree.a -R pk910/keccaktree
