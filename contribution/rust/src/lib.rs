use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Contribution {
    pub author: String,
    pub shard: u8,
    pub sop_id: String,
    pub changes: Vec<String>,
    pub verified: bool,
}

impl Contribution {
    pub fn new(author: String, shard: u8, sop_id: String) -> Self {
        Self {
            author,
            shard,
            sop_id,
            changes: Vec::new(),
            verified: false,
        }
    }
    
    pub fn add_change(&mut self, change: String) {
        self.changes.push(change);
    }
    
    pub fn verify(&mut self) -> bool {
        self.verified = self.shard < 71 && !self.changes.is_empty();
        self.verified
    }
    
    pub fn to_shard(&self) -> u8 {
        (self.sop_id.bytes().sum::<u8>() as usize % 71) as u8
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_contribution() {
        let mut contrib = Contribution::new(
            "alice".to_string(),
            1,
            "SOP-J-INVARIANT-001".to_string()
        );
        contrib.add_change("Implement Hecke operator".to_string());
        assert!(contrib.verify());
        assert_eq!(contrib.shard, 1);
    }
    
    #[test]
    fn test_shard_assignment() {
        let contrib = Contribution::new(
            "bob".to_string(),
            0,
            "SOP-MATHLIB-001".to_string()
        );
        let shard = contrib.to_shard();
        assert!(shard < 71);
    }
}
