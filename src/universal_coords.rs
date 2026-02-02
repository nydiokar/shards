// Universal Game Coordinate Mapping - Rust Implementation
// Map all game coordinates to Monster galactic coordinates

use std::f64::consts::PI;

const MONSTER_DIM: u32 = 196883;
const MONSTER_PRIMES: [u8; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GalacticCoord {
    pub shard: u8,
    pub radius: u32,
    pub angle: u16,
    pub dimension: u32,
}

impl GalacticCoord {
    pub fn monster_center() -> Self {
        Self { shard: 17, radius: 0, angle: 0, dimension: 0 }
    }

    pub fn from_game(game_name: &str, x: f64, y: f64, z: f64) -> Self {
        let shard = (hash_game_name(game_name) % 71) as u8;
        let radius_2d = (x * x + y * y).sqrt();
        let angle = ((y.atan2(x) * 180.0 / PI).rem_euclid(360.0)) as u16;
        let radius = ((radius_2d / 1000.0) * MONSTER_DIM as f64).min(MONSTER_DIM as f64) as u32;
        let dimension = (z.abs() as u32) % MONSTER_DIM;
        
        Self { shard, radius, angle, dimension }
    }

    pub fn hecke_resonance(&self, prime: u8) -> i32 {
        let base = (prime as i32) * (self.shard as i32) + (prime as i32).pow(2);
        let distance_factor = ((MONSTER_DIM - self.radius) / 1000) as i32;
        let angle_factor = ((180 - (self.angle % 360)) / 100) as i32;
        base + distance_factor + angle_factor
    }

    pub fn total_resonance(&self) -> i32 {
        MONSTER_PRIMES.iter().map(|&p| self.hecke_resonance(p)).sum()
    }

    pub fn gravitational_pull(&self) -> f64 {
        if self.radius == 0 { 0.0 } else { MONSTER_DIM as f64 / (self.radius + 1) as f64 }
    }
}

fn hash_game_name(name: &str) -> usize {
    name.bytes().fold(0usize, |acc, b| acc.wrapping_mul(31).wrapping_add(b as usize))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_center_at_cusp() {
        let center = GalacticCoord::monster_center();
        assert_eq!(center.shard, 17);
        assert_eq!(center.radius, 0);
    }

    #[test]
    fn test_no_gravity_at_center() {
        let center = GalacticCoord::monster_center();
        assert_eq!(center.gravitational_pull(), 0.0);
    }

    #[test]
    fn test_resonance_bounded() {
        let coord = GalacticCoord::from_game("Test", 100.0, 100.0, 0.0);
        let res = coord.total_resonance();
        assert!(res >= 0 && res <= 100000);
    }

    #[test]
    fn test_pyramid_hopper_center() {
        let coord = GalacticCoord::from_game("Pyramid Hopper", 0.0, 0.0, 0.0);
        assert_eq!(coord.shard, 17);
        assert_eq!(coord.radius, 0);
    }
}
