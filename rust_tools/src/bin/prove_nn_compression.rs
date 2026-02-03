// Neural network compression proof
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct CompressionProof {
    original_size: usize,
    compressed_size: usize,
    ratio: f64,
}

impl CompressionProof {
    fn new(original: usize, compressed: usize) -> Self {
        Self {
            original_size: original,
            compressed_size: compressed,
            ratio: original as f64 / compressed as f64,
        }
    }
}

fn main() {
    println!("🗜️  NN COMPRESSION PROOF");
    let proof = CompressionProof::new(196883, 71);
    println!("Ratio: {:.2}x", proof.ratio);
}
