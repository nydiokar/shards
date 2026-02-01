use ndarray::Array2;
use rayon::prelude::*;

pub struct ShardNN {
    weights: [Array2<f32>; 71],
}

impl ShardNN {
    pub fn new() -> Self {
        Self {
            weights: std::array::from_fn(|_| Array2::zeros((71, 71))),
        }
    }

    pub fn forward(&self, hashes: &[u64; 71]) -> u8 {
        let input: Vec<f32> = hashes.iter().map(|&h| (h % 71) as f32).collect();
        let sums: Vec<u64> = (0..71)
            .into_par_iter()
            .map(|shard| {
                input.iter().zip(&self.weights[shard]).map(|(i, w)| (*i * w[(0, 0)]) as u64).sum()
            })
            .collect();
        (sums.iter().sum::<u64>() % 71) as u8
    }
}
