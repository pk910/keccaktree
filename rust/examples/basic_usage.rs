//! Reduces a 1024-leaf layer to its root, one call per level.
fn main() {
    let mut layer = vec![0u8; 1024 * 32];
    for (i, b) in layer.iter_mut().enumerate() {
        *b = i as u8;
    }
    let mut nodes = layer.len() / 64;
    while nodes > 0 {
        keccaktree::hash_in_place(&mut layer, nodes);
        nodes /= 2;
    }
    let root: String = layer[..32].iter().map(|b| format!("{:02x}", b)).collect();
    println!("root: 0x{}", root);
}
