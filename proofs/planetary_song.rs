// Rust proof
fn main() {
    const BASE_FREQ: f64 = 432.0;
    const SHARDS: usize = 71;
    
    let frequencies: Vec<f64> = (0..SHARDS)
        .map(|i| BASE_FREQ * (i as f64 + 1.0) / SHARDS as f64)
        .collect();
    
    let min = frequencies.first().unwrap();
    let max = frequencies.last().unwrap();
    let ratio = max / min;
    
    assert!((ratio - 2.0).abs() < 0.01, "Not an octave");
    println!("✓ Rust: Octave verified [{:.2}-{:.2} Hz], ratio: {:.4}", min, max, ratio);
}
