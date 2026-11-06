//! Rust bindings for keccaktree: batched keccak256 for Merkle trees.
//!
//! keccaktree hashes many 64-byte nodes (two 32-byte children) at once with
//! hand-written SIMD kernels (AVX-512, AVX2, NEON, Armv8 SHA3). It has the
//! same API as [hashtree](https://github.com/OffchainLabs/hashtree) and its
//! `hashtree-rs` crate, with Ethereum keccak256 (pad `0x01`, not NIST
//! SHA3-256) in place of SHA-256:
//!
//! `digest[i] = keccak256(chunks[64*i .. 64*i + 64])`
//!
//! ```
//! let chunks = [0u8; 64 * 4];          // 4 nodes = 8 children
//! let mut digests = [0u8; 32 * 4];
//! keccaktree::hash(&mut digests, &chunks, 4);
//! ```
//!
//! The best kernel for the CPU is picked on the first call (or by [`init`]).
//! [`Backend`] calls one kernel directly, for tests and benchmarks.

use std::fmt;

/// Raw C API (`src/keccaktree.h`).
pub mod ffi {
    /// `digest[i] = keccak256(input[64*i .. 64*i+64])` for `i < count`;
    /// `output` may alias `input`.
    pub type HashFn = unsafe extern "C" fn(output: *mut u8, input: *const u8, count: u64);

    extern "C" {
        /// Select the implementation, or detect it from the CPU when `None`.
        pub fn keccaktree_init(override_: Option<HashFn>);
        pub fn keccaktree_hash(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_generic(output: *mut u8, input: *const u8, count: u64);
    }

    #[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
    extern "C" {
        pub fn keccaktree_keccak256_avx2_x4(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_avx2_x8(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_avx2_x5(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_avx2_x9(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_avx2_x10(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_avx512vl_x4(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_avx512_x8(output: *mut u8, input: *const u8, count: u64);
    }

    #[cfg(all(keccaktree_asm, target_arch = "aarch64"))]
    extern "C" {
        pub fn keccaktree_keccak256_neon_x2(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_sha3_x2(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_scalar_x1(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_sha3_x3(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_sha3_x3r(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_neon_x3(output: *mut u8, input: *const u8, count: u64);
    }

    #[cfg(all(keccaktree_asm, target_arch = "riscv64"))]
    extern "C" {
        pub fn keccaktree_keccak256_rv64_x1(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_zbb_x1(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_rvv(output: *mut u8, input: *const u8, count: u64);
        pub fn keccaktree_keccak256_rvv_zvkb(output: *mut u8, input: *const u8, count: u64);
    }
}

/// Selects the kernel for this CPU now instead of on the first hash call.
/// Optional, and safe to call more than once.
pub fn init() {
    unsafe { ffi::keccaktree_init(None) }
}

#[inline]
fn check(out_len: usize, in_len: usize, count: usize) {
    let need_in = count.checked_mul(64).expect("count overflows");
    assert!(in_len >= need_in, "chunks holds {} bytes, {} nodes need {}", in_len, count, need_in);
    assert!(out_len >= count * 32, "out holds {} bytes, {} digests need {}", out_len, count, count * 32);
}

/// Hashes `count` 64-byte nodes from `chunks` into `count` consecutive
/// 32-byte digests in `out`. Same signature as `hashtree_rs::hash`.
///
/// # Panics
/// If `chunks` is shorter than `64 * count` or `out` shorter than `32 * count`.
pub fn hash(out: &mut [u8], chunks: &[u8], count: usize) {
    check(out.len(), chunks.len(), count);
    unsafe { ffi::keccaktree_hash(out.as_mut_ptr(), chunks.as_ptr(), count as u64) }
}

/// Hashes `count` nodes of `buf` in place: digest `i` overwrites bytes
/// `32*i .. 32*i+32`, so one call reduces a tree layer to the next one in
/// the first half of the buffer.
///
/// # Panics
/// If `buf` is shorter than `64 * count`.
pub fn hash_in_place(buf: &mut [u8], count: usize) {
    check(buf.len(), buf.len(), count);
    let p = buf.as_mut_ptr();
    unsafe { ffi::keccaktree_hash(p, p, count as u64) }
}

/// Hashes pairs of 32-byte children: `digests[i] = keccak256(chunks[2i] || chunks[2i+1])`,
/// like `Hash` in the Go bindings.
///
/// # Panics
/// If `chunks` has an odd length or `digests` holds fewer than `chunks.len() / 2` entries.
pub fn hash_chunks(digests: &mut [[u8; 32]], chunks: &[[u8; 32]]) {
    assert!(chunks.len() & 1 == 0, "odd number of chunks: {}", chunks.len());
    let count = chunks.len() / 2;
    assert!(digests.len() >= count, "{} digests do not fit {} results", digests.len(), count);
    unsafe { ffi::keccaktree_hash(digests.as_mut_ptr().cast(), chunks.as_ptr().cast(), count as u64) }
}

/// One keccaktree kernel. [`Backend::hash`] calls it directly, bypassing the
/// automatic selection.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Backend {
    /// Portable C, one node at a time.
    Generic,
    /// x86-64 AVX2, 4 nodes per batch.
    Avx2X4,
    /// x86-64 AVX2, two interleaved 4-node batches.
    Avx2X8,
    /// x86-64 AVX2 x4 plus one node in the integer registers (BMI1, BMI2).
    Avx2X5,
    /// x86-64 AVX2 x8 plus one node in the integer registers (BMI1, BMI2).
    Avx2X9,
    /// x86-64 AVX2 x8 plus two nodes in the integer registers (BMI1, BMI2).
    Avx2X10,
    /// x86-64 AVX-512VL on ymm registers, 4 nodes per batch.
    Avx512VlX4,
    /// x86-64 AVX-512 on zmm registers, 8 nodes per batch.
    Avx512X8,
    /// AArch64 Advanced SIMD, 2 nodes per batch.
    NeonX2,
    /// AArch64 FEAT_SHA3, 2 nodes per batch.
    Sha3X2,
    /// AArch64 scalar with lazy rotations, 1 node.
    ScalarX1,
    /// AArch64 SHA3 x2 interleaved with a lazy-rotation scalar node (Arm cores).
    Sha3X3,
    /// AArch64 SHA3 x2 interleaved with a ROR scalar node (Apple cores).
    Sha3X3r,
    /// AArch64 Advanced SIMD x2 interleaved with a lazy-rotation scalar node.
    NeonX3,
    /// RISC-V RV64 base scalar, 1 node.
    Rv64X1,
    /// RISC-V scalar with Zbb rotates, 1 node.
    ZbbX1,
    /// RISC-V Vector (RVV 1.0).
    Rvv,
    /// RISC-V Vector with Zvkb vector rotates.
    RvvZvkb,
}

/// Returned by [`Backend::hash`] when the kernel is not built for this
/// target or the CPU lacks its instructions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unsupported(pub Backend);

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "keccaktree backend {} is not supported on this CPU", self.0.name())
    }
}

impl Backend {
    /// Every backend, in no particular order.
    pub const ALL: [Backend; 18] = [
        Backend::Generic,
        Backend::Avx2X4,
        Backend::Avx2X8,
        Backend::Avx2X5,
        Backend::Avx2X9,
        Backend::Avx2X10,
        Backend::Avx512VlX4,
        Backend::Avx512X8,
        Backend::NeonX2,
        Backend::Sha3X2,
        Backend::ScalarX1,
        Backend::Sha3X3,
        Backend::Sha3X3r,
        Backend::NeonX3,
        Backend::Rv64X1,
        Backend::ZbbX1,
        Backend::Rvv,
        Backend::RvvZvkb,
    ];

    /// The kernel's name in the C library (`keccaktree_keccak256_<name>`).
    pub fn name(self) -> &'static str {
        match self {
            Backend::Generic => "generic",
            Backend::Avx2X4 => "avx2_x4",
            Backend::Avx2X8 => "avx2_x8",
            Backend::Avx2X5 => "avx2_x5",
            Backend::Avx2X9 => "avx2_x9",
            Backend::Avx2X10 => "avx2_x10",
            Backend::Avx512VlX4 => "avx512vl_x4",
            Backend::Avx512X8 => "avx512_x8",
            Backend::NeonX2 => "neon_x2",
            Backend::Sha3X2 => "sha3_x2",
            Backend::ScalarX1 => "scalar_x1",
            Backend::Sha3X3 => "sha3_x3",
            Backend::Sha3X3r => "sha3_x3r",
            Backend::NeonX3 => "neon_x3",
            Backend::Rv64X1 => "rv64_x1",
            Backend::ZbbX1 => "zbb_x1",
            Backend::Rvv => "rvv",
            Backend::RvvZvkb => "rvv_zvkb",
        }
    }

    /// The C function, if the kernel is built for this target and the CPU
    /// can run it.
    pub fn function(self) -> Option<ffi::HashFn> {
        match self {
            Backend::Generic => Some(ffi::keccaktree_keccak256_generic),
            #[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
            Backend::Avx2X4 if x86::avx2() => Some(ffi::keccaktree_keccak256_avx2_x4),
            #[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
            Backend::Avx2X8 if x86::avx2() => Some(ffi::keccaktree_keccak256_avx2_x8),
            #[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
            Backend::Avx2X5 if x86::avx2() && x86::bmi() => Some(ffi::keccaktree_keccak256_avx2_x5),
            #[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
            Backend::Avx2X9 if x86::avx2() && x86::bmi() => Some(ffi::keccaktree_keccak256_avx2_x9),
            #[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
            Backend::Avx2X10 if x86::avx2() && x86::bmi() => Some(ffi::keccaktree_keccak256_avx2_x10),
            #[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
            Backend::Avx512VlX4 if x86::avx512() => Some(ffi::keccaktree_keccak256_avx512vl_x4),
            #[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
            Backend::Avx512X8 if x86::avx512() => Some(ffi::keccaktree_keccak256_avx512_x8),
            #[cfg(all(keccaktree_asm, target_arch = "aarch64"))]
            Backend::NeonX2 => Some(ffi::keccaktree_keccak256_neon_x2),
            #[cfg(all(keccaktree_asm, target_arch = "aarch64"))]
            Backend::ScalarX1 => Some(ffi::keccaktree_keccak256_scalar_x1),
            #[cfg(all(keccaktree_asm, target_arch = "aarch64"))]
            Backend::Sha3X2 if arm::sha3() => Some(ffi::keccaktree_keccak256_sha3_x2),
            #[cfg(all(keccaktree_asm, target_arch = "aarch64"))]
            Backend::Sha3X3 if arm::sha3() => Some(ffi::keccaktree_keccak256_sha3_x3),
            #[cfg(all(keccaktree_asm, target_arch = "aarch64"))]
            Backend::Sha3X3r if arm::sha3() => Some(ffi::keccaktree_keccak256_sha3_x3r),
            #[cfg(all(keccaktree_asm, target_arch = "aarch64"))]
            Backend::NeonX3 => Some(ffi::keccaktree_keccak256_neon_x3),
            #[cfg(all(keccaktree_asm, target_arch = "riscv64"))]
            Backend::Rv64X1 => Some(ffi::keccaktree_keccak256_rv64_x1),
            #[cfg(all(keccaktree_asm, target_arch = "riscv64"))]
            Backend::ZbbX1 if riscv::ext() & riscv::ZBB != 0 => Some(ffi::keccaktree_keccak256_zbb_x1),
            #[cfg(all(keccaktree_asm, target_arch = "riscv64"))]
            Backend::Rvv if riscv::ext() & riscv::V != 0 => Some(ffi::keccaktree_keccak256_rvv),
            #[cfg(all(keccaktree_asm, target_arch = "riscv64"))]
            Backend::RvvZvkb if riscv::ext() & (riscv::V | riscv::ZVKB) == riscv::V | riscv::ZVKB => {
                Some(ffi::keccaktree_keccak256_rvv_zvkb)
            }
            _ => None,
        }
    }

    /// Whether [`Backend::hash`] can run this kernel here.
    pub fn is_supported(self) -> bool {
        self.function().is_some()
    }

    /// Like [`hash`], with this kernel.
    ///
    /// # Panics
    /// If `chunks` is shorter than `64 * count` or `out` shorter than `32 * count`.
    pub fn hash(self, out: &mut [u8], chunks: &[u8], count: usize) -> Result<(), Unsupported> {
        let f = self.function().ok_or(Unsupported(self))?;
        check(out.len(), chunks.len(), count);
        unsafe { f(out.as_mut_ptr(), chunks.as_ptr(), count as u64) };
        Ok(())
    }

    /// Makes [`hash`] and the C `keccaktree_hash` use this kernel from now on
    /// (process-wide). [`init`] goes back to automatic selection.
    pub fn select(self) -> Result<(), Unsupported> {
        let f = self.function().ok_or(Unsupported(self))?;
        unsafe { ffi::keccaktree_init(Some(f)) };
        Ok(())
    }
}

impl fmt::Display for Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

// Same conditions as the C dispatcher (src/keccaktree.c); the std macros
// also check that the OS saves the ymm/zmm state.
#[cfg(all(keccaktree_asm, target_arch = "x86_64"))]
mod x86 {
    pub fn avx2() -> bool {
        is_x86_feature_detected!("avx2")
    }

    pub fn avx512() -> bool {
        is_x86_feature_detected!("avx512f") && is_x86_feature_detected!("avx512vl")
    }

    /// andn and rorx, for the scalar nodes of the hybrid kernels
    pub fn bmi() -> bool {
        is_x86_feature_detected!("bmi1") && is_x86_feature_detected!("bmi2")
    }
}

#[cfg(all(keccaktree_asm, target_arch = "aarch64"))]
mod arm {
    pub fn sha3() -> bool {
        std::arch::is_aarch64_feature_detected!("sha3")
    }
}

// riscv_hwprobe(RISCV_HWPROBE_KEY_IMA_EXT_0), as in src/keccaktree.c; std's
// is_riscv_feature_detected! is not stable for V and Zvkb yet.
#[cfg(all(keccaktree_asm, target_arch = "riscv64"))]
mod riscv {
    pub const V: u64 = 1 << 2;
    pub const ZBB: u64 = 1 << 4;
    pub const ZVKB: u64 = 1 << 19;

    #[cfg(target_os = "linux")]
    pub fn ext() -> u64 {
        const KEY_IMA_EXT_0: u64 = 4;
        let mut probe: [u64; 2] = [KEY_IMA_EXT_0, 0];
        let ret: isize;
        // riscv_hwprobe(pairs, pair_count, cpusetsize, cpus, flags), Linux 6.4+
        unsafe {
            core::arch::asm!(
                "ecall",
                inlateout("a0") probe.as_mut_ptr() as isize => ret,
                in("a1") 1usize,
                in("a2") 0usize,
                in("a3") 0usize,
                in("a4") 0usize,
                in("a7") 258usize,
                options(nostack),
            );
        }
        if ret == 0 && probe[0] == KEY_IMA_EXT_0 {
            probe[1]
        } else {
            0
        }
    }

    #[cfg(not(target_os = "linux"))]
    pub fn ext() -> u64 {
        0
    }
}
