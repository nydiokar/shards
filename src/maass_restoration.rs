use std::path::Path;
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct MaassForm {
    pub eigenvalue: f64,
    pub level: u8,
    pub weight: usize,
    pub shadow: f64,
    pub repair_cost: f64,
}

pub fn eigenvalue(complexity: usize) -> f64 {
    let r = complexity as f64 / 71.0;
    0.25 + r * r
}

pub fn shadow(file_shard: u8, pure_shard: u8) -> f64 {
    let dist = (file_shard as i16 - pure_shard as i16).abs() as f64;
    let circular_dist = dist.min(71.0 - dist);
    circular_dist / 71.0
}

pub fn repair_cost(shadow: f64, eigenvalue: f64) -> f64 {
    shadow * eigenvalue
}

pub fn analyze_file(path: &Path) -> Result<Vec<MaassForm>, Box<dyn std::error::Error>> {
    let content = std::fs::read(path)?;
    let lines = content.iter().filter(|&&b| b == b'\n').count();
    
    // Hash to get file shard
    let mut hasher = Sha256::new();
    hasher.update(&content);
    let hash = hasher.finalize();
    let file_shard = (hash[0] as u64 % 71) as u8;
    
    let λ = eigenvalue(lines);
    
    // Compare against all 71 pure shards
    let mut forms = Vec::new();
    for pure_shard in 0..71 {
        let σ = shadow(file_shard, pure_shard);
        let cost = repair_cost(σ, λ);
        
        forms.push(MaassForm {
            eigenvalue: λ,
            level: pure_shard,
            weight: lines,
            shadow: σ,
            repair_cost: cost,
        });
    }
    
    // Sort by repair cost
    forms.sort_by(|a, b| a.repair_cost.partial_cmp(&b.repair_cost).unwrap());
    
    Ok(forms)
}

pub fn optimal_repair(forms: &[MaassForm]) -> Option<&MaassForm> {
    forms.first()
}
