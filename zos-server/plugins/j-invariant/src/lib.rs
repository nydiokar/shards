use serde::{Deserialize, Serialize};

const PRIMES: [u64; 20] = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71];
const ITERATIONS: usize = 40320; // 8!

#[derive(Debug, Serialize, Deserialize)]
pub struct JInvariant {
    pub coefficients: Vec<u64>,
    pub chi: u64,
    pub iterations: usize,
}

fn hecke_operator(coeff: u64, prime: u64, iter: usize) -> u64 {
    (coeff * prime + iter as u64) % 71
}

fn maass_eigenvalue(n: usize, iter: usize) -> f64 {
    let r = ((n * iter) % 71) as f64 / 71.0;
    0.25 + r * r
}

fn apply_transformation(state: &[u64], prime: u64, iter: usize) -> Vec<u64> {
    state.iter().enumerate().map(|(i, &coeff)| {
        let hecke = hecke_operator(coeff, prime, iter);
        let eigenvalue = maass_eigenvalue(i, iter);
        ((hecke as f64 * (1.0 + eigenvalue)) as u64) % 71
    }).collect()
}

#[no_mangle]
pub extern "C" fn j_invariant_transform() -> *mut JInvariant {
    let mut state = vec![1, 30, 45, 54, 11]; // j-invariant mod 71
    
    for i in 1..=ITERATIONS {
        let prime = PRIMES[i % PRIMES.len()];
        state = apply_transformation(&state, prime, i);
    }
    
    let chi = state.iter().sum::<u64>() % 71;
    
    Box::into_raw(Box::new(JInvariant {
        coefficients: state,
        chi,
        iterations: ITERATIONS,
    }))
}

#[no_mangle]
pub extern "C" fn free_j_invariant(ptr: *mut JInvariant) {
    if !ptr.is_null() {
        unsafe { Box::from_raw(ptr); }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hecke_operator() {
        assert_eq!(hecke_operator(1, 2, 0), 2);
        assert_eq!(hecke_operator(30, 3, 1), 20);
    }

    #[test]
    fn test_transformation() {
        let state = vec![1, 30, 45, 54, 11];
        let result = apply_transformation(&state, 2, 1);
        assert_eq!(result.len(), 5);
        assert!(result.iter().all(|&x| x < 71));
    }
}
