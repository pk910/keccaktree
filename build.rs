//! Builds the keccaktree C library for the Rust bindings.
//!
//! By default the sources in src/ are compiled with the `cc` crate: the
//! generic C core and dispatcher everywhere, plus the hand-written assembly
//! kernels on x86-64 and AArch64. The kernels are GNU-assembler syntax, which
//! MSVC cannot assemble, so MSVC x86-64 targets link the CI-built library from
//! lib/windows_amd64/ instead (it has no C runtime dependencies). The
//! `prebuilt` feature does the same on every platform that has a library in
//! lib/.

use std::env;
use std::path::{Path, PathBuf};

const X86_64_KERNELS: &[&str] = &["avx512_x8", "avx512vl_x4", "avx2_x4"];
const AARCH64_KERNELS: &[&str] = &["neon_x2", "sha3_x2", "scalar_x1", "sha3_x3", "sha3_x3r"];

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let src = manifest_dir.join("src");
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=lib");
    println!("cargo:include={}", src.display());

    let platform = match (os.as_str(), arch.as_str()) {
        ("linux", "x86_64") => Some("linux_amd64"),
        ("linux", "aarch64") => Some("linux_arm64"),
        ("macos", "aarch64") => Some("darwin_arm64"),
        ("windows", "x86_64") => Some("windows_amd64"),
        _ => None,
    };
    let msvc = target_env == "msvc";
    let want_prebuilt = env::var_os("CARGO_FEATURE_PREBUILT").is_some() || (msvc && arch == "x86_64");

    if want_prebuilt {
        match platform {
            Some(p) => return link_prebuilt(&manifest_dir.join("lib").join(p), msvc),
            None => println!(
                "cargo:warning=keccaktree: no prebuilt library for {}-{}, building from source",
                os, arch
            ),
        }
    }

    let mut build = cc::Build::new();
    build
        .include(&src)
        .opt_level(3)
        .warnings(false)
        .file(src.join("keccak256_generic.c"))
        .file(src.join("keccaktree.c"));

    // Assembly kernels need a GNU-compatible assembler (gcc or clang).
    let kernels: &[&str] = match arch.as_str() {
        _ if msvc => &[],
        "x86_64" => X86_64_KERNELS,
        "aarch64" => AARCH64_KERNELS,
        _ => &[],
    };
    for k in kernels {
        build.file(src.join("asm").join(format!("keccak256_{}.S", k)));
    }
    if os == "windows" && build.get_compiler().is_like_gnu() {
        // same as src/Makefile: gcc on Windows does not realign the stack for
        // 32/64-byte vector spills
        build.flag("-Wa,-muse-unaligned-vector-move");
    }
    build.compile("keccaktree");
}

fn link_prebuilt(dir: &Path, msvc: bool) {
    let lib = dir.join("libkeccaktree.a");
    if !lib.exists() {
        panic!("keccaktree: {} is missing", lib.display());
    }
    if msvc {
        // link.exe reads the GNU ar archive, but rustc looks for keccaktree.lib
        let out = PathBuf::from(env::var("OUT_DIR").unwrap());
        std::fs::copy(&lib, out.join("keccaktree.lib")).expect("copy prebuilt library");
        println!("cargo:rustc-link-search=native={}", out.display());
    } else {
        println!("cargo:rustc-link-search=native={}", dir.display());
    }
    println!("cargo:rustc-link-lib=static=keccaktree");
}
