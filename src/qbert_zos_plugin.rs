// Q*bert zkOS Plugin
// Handles zkRDF tape loading

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub struct QbertTape {
    pub tape_id: String,
    pub format: String,
    pub encoding: String,
    pub shard: u8,
    pub triples: Vec<(String, String, String)>,
    pub emoji_urls: Vec<String>,
    pub hash: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct QbertState {
    pub position: (u8, u8),
    pub cubes_changed: u8,
    pub monster_coord: u32,
    pub shard: u8,
}

impl QbertState {
    pub fn new() -> Self {
        QbertState {
            position: (0, 0),
            cubes_changed: 0,
            monster_coord: 1000,
            shard: 17,
        }
    }
    
    pub fn make_move(&mut self, move_type: &str) -> Result<(), String> {
        let (row, col) = self.position;
        
        let new_pos = match move_type {
            "down_left" => (row + 1, col),
            "down_right" => (row + 1, col + 1),
            "up_left" => (row.saturating_sub(1), col.saturating_sub(1)),
            "up_right" => (row.saturating_sub(1), col),
            _ => return Err("Invalid move".to_string()),
        };
        
        // Validate
        if new_pos.0 > 6 || new_pos.1 > new_pos.0 {
            return Err("Invalid position".to_string());
        }
        
        self.position = new_pos;
        self.cubes_changed += 1;
        self.monster_coord = 1000 + (new_pos.0 as u32) * 100 + (new_pos.1 as u32) * 10 + (self.cubes_changed % 10) as u32;
        
        Ok(())
    }
    
    pub fn is_won(&self) -> bool {
        self.cubes_changed >= 28
    }
}

pub fn load_tape(tape_json: &str) -> Result<QbertTape, String> {
    serde_json::from_str(tape_json)
        .map_err(|e| format!("Failed to parse tape: {}", e))
}

pub fn create_game_from_tape(tape: &QbertTape) -> Result<QbertState, String> {
    if tape.shard != 17 {
        return Err("Q*bert only plays at shard 17 (cusp)".to_string());
    }
    
    Ok(QbertState::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_qbert_state() {
        let mut state = QbertState::new();
        assert_eq!(state.position, (0, 0));
        assert_eq!(state.shard, 17);
        
        state.make_move("down_left").unwrap();
        assert_eq!(state.position, (1, 0));
        assert_eq!(state.cubes_changed, 1);
    }
}
