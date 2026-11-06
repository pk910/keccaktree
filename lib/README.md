# Static libraries

Built from `src/` and attested by the *Update Static Libraries* workflow
(`.github/workflows/build-static-libs.yml`). Each platform directory has
`libkeccaktree.a`, its `.sha256`, and, for CI builds, a `.buildinfo` with the
exact compiler. `SOURCE_COMMIT` names the commit the libraries were built from.

| Platform | Toolchain (CI) | Kernels |
|---|---|---|
| linux_amd64 | ubuntu-22.04 gcc | avx512_x8, avx512vl_x4, avx2_x4, generic |
| linux_arm64 | ubuntu-22.04 gcc-aarch64-linux-gnu | sha3_x2, neon_x2, generic |
| darwin_arm64 | macos-15 Apple clang | sha3_x2, neon_x2, generic |
| windows_amd64 | MSYS2 MINGW64 gcc | avx512_x8, avx512vl_x4, avx2_x4, generic |

Builds use `SOURCE_DATE_EPOCH` and `-ffile-prefix-map`, then
`strip --strip-debug` and `ranlib` (macOS additionally zeroes `ar` member
metadata), so a rebuild with the same compiler is byte-identical.

## Pull requests

PR CI tests the Go bindings against the libraries committed here, so a PR
that changes `src/` has to bring rebuilt libraries along. Either build all
four on one host with zig (`.github/scripts/build-libs.sh`), or run *Build &
Test* on your branch (`gh workflow run build.yml --ref <branch>`) and copy
its artifacts with `.github/scripts/fetch-ci-libs.sh`. Commit them with the
change.

After the merge, *Update Static Libraries* rebuilds every library on main,
replaces the PR's copies, and records a build provenance attestation:

    gh attestation verify lib/linux_amd64/libkeccaktree.a -R pk910/keccaktree
