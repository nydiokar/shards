use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub struct Shard {
    pub level: String,      // "file", "line", "token"
    pub content: String,
    pub hash: u64,
    pub shard_id: u8,       // mod 71
    pub prime: u64,         // 71, 59, or 47
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Arrow {
    pub from: u8,
    pub to: u8,
    pub weight: u64,
}

const CROWN_PRIMES: [u64; 3] = [71, 59, 47];

pub fn shard_file(path: &str) -> Result<Vec<Shard>, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;
    let mut shards = Vec::new();
    
    // Level 1: File shard (prime 71)
    let file_hash = hash_content(&content);
    shards.push(Shard {
        level: "file".to_string(),
        content: path.to_string(),
        hash: file_hash,
        shard_id: (file_hash % 71) as u8,
        prime: 71,
    });
    
    // Level 2: Line shards (prime 59)
    for (i, line) in content.lines().enumerate() {
        let line_hash = hash_content(line);
        shards.push(Shard {
            level: "line".to_string(),
            content: format!("{}:{}", i, line),
            hash: line_hash,
            shard_id: (line_hash % 59) as u8,
            prime: 59,
        });
    }
    
    // Level 3: Token shards (prime 47)
    for line in content.lines() {
        for token in line.split_whitespace() {
            let token_hash = hash_content(token);
            shards.push(Shard {
                level: "token".to_string(),
                content: token.to_string(),
                hash: token_hash,
                shard_id: (token_hash % 47) as u8,
                prime: 47,
            });
        }
    }
    
    Ok(shards)
}

pub fn make_arrows(shards: &[Shard]) -> Vec<Arrow> {
    let mut arrows = Vec::new();
    let mut adjacency: HashMap<(u8, u8), u64> = HashMap::new();
    
    for i in 0..shards.len().saturating_sub(1) {
        let from = shards[i].shard_id;
        let to = shards[i + 1].shard_id;
        *adjacency.entry((from, to)).or_insert(0) += 1;
    }
    
    for ((from, to), weight) in adjacency {
        arrows.push(Arrow { from, to, weight });
    }
    
    arrows
}

fn hash_content(s: &str) -> u64 {
    s.bytes().fold(0u64, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u64))
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_shard_file() {
        let shards = shard_file("SimpleExprMonster.lean").unwrap();
        assert!(shards.iter().any(|s| s.prime == 71));
        assert!(shards.iter().any(|s| s.prime == 59));
        assert!(shards.iter().any(|s| s.prime == 47));
    }
}
