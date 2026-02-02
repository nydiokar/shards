use std::collections::HashSet;

/// Mycelium path coordinate: Ξ = (p, σ, ε)
#[derive(Debug, Clone)]
pub struct MyceliumCoordinate {
    /// Prime support: which Monster primes are active on each side
    pub prime_support: (Vec<u64>, Vec<u64>),
    /// Shadow parity: +1 (holomorphic) or -1 (shadow/Maass)
    pub shadow_parity: i8,
    /// Framing residue: conserved structure through the path
    pub framing_residue: u64,
}

/// Mycelium path: A walk through Monster symmetry (not a number!)
#[derive(Debug, Clone)]
pub struct MyceliumPath {
    pub source: u64,
    pub target: u64,
    pub coordinate: MyceliumCoordinate,
}

impl MyceliumPath {
    /// Create the canonical 232 ↔ 323 path
    pub fn path_232_323() -> Self {
        Self {
            source: 232,
            target: 323,
            coordinate: MyceliumCoordinate {
                prime_support: (vec![8, 29], vec![17, 19]),  // 2³, 29 | 17, 19
                shadow_parity: -1,                            // Shadow transition
                framing_residue: 8,                           // 2³ conserved
            },
        }
    }
    
    /// Check if this is a shadow transition (Maass move)
    pub fn is_shadow_transition(&self) -> bool {
        self.coordinate.shadow_parity == -1
    }
    
    /// Get the conserved structure
    pub fn conserved_structure(&self) -> u64 {
        self.coordinate.framing_residue
    }
    
    /// Compose two mycelium paths
    pub fn compose(&self, other: &MyceliumPath) -> Option<MyceliumPath> {
        if self.target != other.source {
            return None;
        }
        
        // Combine prime supports
        let mut left_primes: HashSet<u64> = self.coordinate.prime_support.0.iter().copied().collect();
        left_primes.extend(&other.coordinate.prime_support.0);
        
        let mut right_primes: HashSet<u64> = self.coordinate.prime_support.1.iter().copied().collect();
        right_primes.extend(&other.coordinate.prime_support.1);
        
        // Multiply shadow parities
        let combined_parity = self.coordinate.shadow_parity * other.coordinate.shadow_parity;
        
        // GCD of framing residues
        let combined_residue = gcd(self.coordinate.framing_residue, other.coordinate.framing_residue);
        
        Some(MyceliumPath {
            source: self.source,
            target: other.target,
            coordinate: MyceliumCoordinate {
                prime_support: (
                    left_primes.into_iter().collect(),
                    right_primes.into_iter().collect()
                ),
                shadow_parity: combined_parity,
                framing_residue: combined_residue,
            },
        })
    }
    
    /// Check if path forms a closed loop
    pub fn is_closed_loop(&self) -> bool {
        self.source == self.target
    }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_232_323_path() {
        let path = MyceliumPath::path_232_323();
        assert_eq!(path.source, 232);
        assert_eq!(path.target, 323);
        assert!(path.is_shadow_transition());
        assert_eq!(path.conserved_structure(), 8);
    }
    
    #[test]
    fn test_path_composition() {
        let p1 = MyceliumPath::path_232_323();
        let p2 = MyceliumPath {
            source: 323,
            target: 232,
            coordinate: MyceliumCoordinate {
                prime_support: (vec![17, 19], vec![8, 29]),
                shadow_parity: -1,
                framing_residue: 8,
            },
        };
        
        let composed = p1.compose(&p2).unwrap();
        assert!(composed.is_closed_loop());
    }
}
