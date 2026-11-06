//! Every kernel this CPU supports, checked against the `sha3` crate's
//! Keccak256 for 0..=300 nodes, unaligned buffers and in-place hashing.

use keccaktree::Backend;
use sha3::{Digest, Keccak256};

fn input(nodes: usize, offset: usize) -> Vec<u8> {
    let mut v = vec![0u8; nodes * 64 + offset];
    let mut x: u32 = 0x9e37_79b9 ^ nodes as u32;
    for b in v.iter_mut() {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        *b = x as u8;
    }
    v
}

fn reference(chunks: &[u8]) -> Vec<u8> {
    chunks.chunks(64).flat_map(|node| Keccak256::digest(node).to_vec()).collect()
}

fn supported() -> Vec<Backend> {
    Backend::ALL.iter().copied().filter(|b| b.is_supported()).collect()
}

#[test]
fn known_vector() {
    // keccak256 of 64 zero bytes
    let mut out = [0u8; 32];
    keccaktree::hash(&mut out, &[0u8; 64], 1);
    let expect = "ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5";
    let got: String = out.iter().map(|b| format!("{:02x}", b)).collect();
    assert_eq!(got, expect);
}

#[test]
fn every_backend_matches_reference() {
    let backends = supported();
    println!("supported: {:?}", backends);
    assert!(backends.contains(&Backend::Generic));
    for &b in &backends {
        for nodes in 0..=300 {
            for offset in [0usize, 1, 7] {
                let buf = input(nodes, offset);
                let chunks = &buf[offset..];
                let expect = reference(chunks);
                let mut out = vec![0u8; nodes * 32 + offset];
                b.hash(&mut out[offset..], chunks, nodes).unwrap();
                assert_eq!(&out[offset..], &expect[..], "{} nodes={} offset={}", b, nodes, offset);
            }
        }
    }
}

#[test]
fn dispatch_and_in_place() {
    keccaktree::init();
    for nodes in [0usize, 1, 2, 3, 5, 8, 17, 64, 255, 256] {
        let mut buf = input(nodes, 0);
        let expect = reference(&buf);
        let mut out = vec![0u8; nodes * 32];
        keccaktree::hash(&mut out, &buf, nodes);
        assert_eq!(out, expect, "dispatch nodes={}", nodes);
        keccaktree::hash_in_place(&mut buf, nodes);
        assert_eq!(&buf[..nodes * 32], &expect[..], "in place nodes={}", nodes);
    }
}

#[test]
fn hash_chunks_pairs() {
    let chunks: Vec<[u8; 32]> = (0..34u8).map(|i| [i; 32]).collect();
    let mut digests = vec![[0u8; 32]; 17];
    keccaktree::hash_chunks(&mut digests, &chunks);
    for (i, d) in digests.iter().enumerate() {
        let mut h = Keccak256::new();
        h.update(chunks[2 * i]);
        h.update(chunks[2 * i + 1]);
        assert_eq!(&d[..], &h.finalize()[..]);
    }
}

#[test]
fn unsupported_backends_are_rejected() {
    for &b in Backend::ALL.iter().filter(|b| !b.is_supported()) {
        assert_eq!(b.hash(&mut [0u8; 32], &[0u8; 64], 1), Err(keccaktree::Unsupported(b)));
    }
}

#[test]
#[should_panic]
fn short_output_panics() {
    keccaktree::hash(&mut [0u8; 31], &[0u8; 64], 1);
}
