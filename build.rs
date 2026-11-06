//! Links the keccaktree C library for the Rust bindings.
//!
//! On linux x86-64/aarch64/riscv64, macOS aarch64 and Windows x86-64 (GNU and MSVC)
//! this links the CI-built, attested static library from lib/<platform>/,
//! the same one the Go bindings use (the Windows library has no C runtime
//! dependencies, so MSVC's linker takes it too).
//!
//! Other targets, or any target with the `build-from-source` feature, compile
//! src/ with the `cc` crate instead: the generic C core and dispatcher
//! everywhere, plus the assembly kernels on x86-64, AArch64 and RISC-V with a
//! GNU-compatible compiler (MSVC cannot assemble them).

use std::env;
use std::path::{Path, PathBuf};

const X86_64_KERNELS: &[&str] = &["avx512_x8", "avx512vl_x4", "avx2_x8", "avx2_x4", "avx2_x9", "avx2_x10"];
const AARCH64_KERNELS: &[&str] = &["neon_x2", "sha3_x2", "scalar_x1", "sha3_x3", "sha3_x3r"];
// keccaktree.c dispatches to these on riscv64, so they are always needed there
const RISCV64_KERNELS: &[&str] = &["rv64_x1", "zbb_x1", "rvv", "rvv_zvkb"];

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
    // keccaktree_asm: the x86-64 / AArch64 kernels are linked
    println!("cargo:rustc-check-cfg=cfg(keccaktree_asm)");

    let platform = match (os.as_str(), arch.as_str()) {
        ("linux", "x86_64") => Some("linux_amd64"),
        ("linux", "aarch64") => Some("linux_arm64"),
        ("macos", "aarch64") => Some("darwin_arm64"),
        ("linux", "riscv64") => Some("linux_riscv64"),
        ("windows", "x86_64") => Some("windows_amd64"),
        _ => None,
    };
    let msvc = target_env == "msvc";
    let from_source = env::var_os("CARGO_FEATURE_BUILD_FROM_SOURCE").is_some();

    if let (Some(p), false) = (platform, from_source) {
        println!("cargo:rustc-cfg=keccaktree_asm");
        return link_prebuilt(&manifest_dir.join("lib").join(p), msvc);
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
        "riscv64" => RISCV64_KERNELS,
        _ => &[],
    };
    if !kernels.is_empty() {
        println!("cargo:rustc-cfg=keccaktree_asm");
    }
    for k in kernels {
        build.file(src.join(format!("keccak256_{}.S", k)));
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
