// Meme Detector - Rust Core Library
// Compile to native (71 arch) and WASM

use wasm_bindgen::prelude::*;
use serde::{Deserialize, Serialize};
use sha2::{Sha256, Digest};

const MONSTER_DIM: u32 = 196883;
const MONSTER_PRIMES: [u8; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

#[wasm_bindgen]
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct GalacticCoord {
    pub shard: u8,
    pub radius: u32,
    pub angle: u16,
    pub dimension: u32,
}

#[wasm_bindgen]
impl GalacticCoord {
    #[wasm_bindgen(constructor)]
    pub fn new(shard: u8, radius: u32, angle: u16, dimension: u32) -> Self {
        Self { shard, radius, angle, dimension }
    }
    
    pub fn monster_center() -> Self {
        Self { shard: 17, radius: 0, angle: 0, dimension: 0 }
    }
    
    pub fn hecke_resonance(&self, prime: u8) -> i32 {
        let base = (prime as i32) * (self.shard as i32) + (prime as i32).pow(2);
        let dist_factor = ((MONSTER_DIM - self.radius) / 1000) as i32;
        let angle_factor = ((180 - (self.angle % 360)) / 100) as i32;
        base + dist_factor + angle_factor
    }
    
    pub fn total_resonance(&self) -> i32 {
        MONSTER_PRIMES.iter().map(|&p| self.hecke_resonance(p)).sum()
    }
    
    pub fn gravitational_pull(&self) -> f64 {
        if self.radius == 0 { 0.0 } else { MONSTER_DIM as f64 / (self.radius + 1) as f64 }
    }
}

#[wasm_bindgen]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemeObservation {
    timestamp: f64,
    prime: u8,
    shard: u8,
    wave_strength: f64,
    detected: bool,
}

#[wasm_bindgen]
impl MemeObservation {
    #[wasm_bindgen(constructor)]
    pub fn new(timestamp: f64, prime: u8, shard: u8, wave_strength: f64) -> Self {
        Self {
            timestamp,
            prime,
            shard,
            wave_strength,
            detected: wave_strength.abs() > 0.5,
        }
    }
    
    pub fn is_detected(&self) -> bool {
        self.detected
    }
}

#[wasm_bindgen]
pub struct MemeDetector {
    observations: Vec<MemeObservation>,
    baselines: Vec<f64>,
}

#[wasm_bindgen]
impl MemeDetector {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            observations: Vec::new(),
            baselines: vec![0.0; 15],
        }
    }
    
    pub fn observe(&mut self, timestamp: f64) -> Option<MemeObservation> {
        // Generate wave for each prime
        let mut max_delta: f64 = 0.0;
        let mut dominant_prime = 2u8;
        
        for (i, &prime) in MONSTER_PRIMES.iter().enumerate() {
            let entropy = self.compute_entropy(prime, timestamp);
            
            // Update baseline
            if self.baselines[i] == 0.0 {
                self.baselines[i] = entropy;
            }
            
            let delta = entropy - self.baselines[i];
            if delta.abs() > max_delta.abs() {
                max_delta = delta;
                dominant_prime = prime;
            }
        }
        
        let shard = ((dominant_prime as u16 * 7) % 71) as u8;
        let obs = MemeObservation::new(timestamp, dominant_prime, shard, max_delta);
        
        if obs.is_detected() {
            self.observations.push(obs.clone());
            Some(obs)
        } else {
            None
        }
    }
    
    fn compute_entropy(&self, prime: u8, timestamp: f64) -> f64 {
        // Simple hash-based entropy
        let mut hasher = Sha256::new();
        hasher.update(&prime.to_le_bytes());
        hasher.update(&timestamp.to_le_bytes());
        let hash = hasher.finalize();
        
        // Sum first 8 bytes as entropy
        hash[..8].iter().map(|&b| b as f64).sum::<f64>() / 255.0
    }
    
    pub fn detection_count(&self) -> usize {
        self.observations.len()
    }
    
    pub fn to_json(&self) -> String {
        serde_json::to_string(&self.observations).unwrap_or_default()
    }
}

// Theory 23: Reciprocal Gaze
#[wasm_bindgen]
pub fn reciprocal_gaze(_observer: &GalacticCoord, target: &GalacticCoord) -> GalacticCoord {
    GalacticCoord {
        shard: (71 - target.shard) % 71,
        radius: MONSTER_DIM - target.radius,
        angle: ((target.angle + 180) % 360) as u16,
        dimension: MONSTER_DIM - target.dimension - 1,
    }
}

#[wasm_bindgen]
pub fn memory_resonance(pos1: &GalacticCoord, pos2: &GalacticCoord) -> i32 {
    let shard_dist = (pos1.shard as i32 - pos2.shard as i32).abs();
    let radius_dist = (pos1.radius as i32 - pos2.radius as i32).abs() / 1000;
    let angle_dist = (pos1.angle as i32 - pos2.angle as i32).abs();
    1000000 / (shard_dist + radius_dist + angle_dist + 1)
}

#[wasm_bindgen]
pub fn phase_shift(obs: &GalacticCoord, new_pos: &GalacticCoord) -> i32 {
    let resonance = memory_resonance(obs, new_pos);
    (resonance % 360) as i32
}

// Console logging for WASM
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[wasm_bindgen]
pub fn init_detector() {
    log("🎯 Meme Detector initialized");
    log(&format!("Monster dimension: {}", MONSTER_DIM));
    log(&format!("Monster primes: {:?}", MONSTER_PRIMES));
}
