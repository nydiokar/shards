// Q*bert Prover - WASM Compilation
// Compile to WASM and encode as data URL

use wasm_bindgen::prelude::*;
use serde::{Deserialize, Serialize};

#[wasm_bindgen]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Position {
    row: u8,
    col: u8,
}

#[wasm_bindgen]
impl Position {
    #[wasm_bindgen(constructor)]
    pub fn new(row: u8, col: u8) -> Position {
        Position { row, col }
    }
    
    pub fn row(&self) -> u8 { self.row }
    pub fn col(&self) -> u8 { self.col }
}

#[wasm_bindgen]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GameState {
    position: Position,
    cubes_changed: u8,
    shard: u8,
}

#[wasm_bindgen]
impl GameState {
    #[wasm_bindgen(constructor)]
    pub fn new() -> GameState {
        GameState {
            position: Position::new(0, 0),
            cubes_changed: 0,
            shard: 17,
        }
    }
    
    pub fn position(&self) -> Position {
        self.position.clone()
    }
    
    pub fn cubes_changed(&self) -> u8 {
        self.cubes_changed
    }
    
    pub fn shard(&self) -> u8 {
        self.shard
    }
    
    pub fn make_move(&mut self, move_type: &str) -> bool {
        let (row, col) = (self.position.row, self.position.col);
        
        let new_pos = match move_type {
            "down_left" => Position::new(row + 1, col),
            "down_right" => Position::new(row + 1, col + 1),
            "up_left" => Position::new(row.saturating_sub(1), col.saturating_sub(1)),
            "up_right" => Position::new(row.saturating_sub(1), col),
            _ => return false,
        };
        
        // Validate
        if new_pos.row > 6 || new_pos.col > new_pos.row {
            return false;
        }
        
        self.position = new_pos;
        self.cubes_changed += 1;
        true
    }
    
    pub fn is_won(&self) -> bool {
        self.cubes_changed >= 28
    }
    
    pub fn monster_coord(&self) -> u32 {
        1000 + (self.position.row as u32) * 100 + (self.position.col as u32) * 10 + (self.cubes_changed % 10) as u32
    }
}

#[wasm_bindgen]
pub struct ZkProver {
    initial_state: GameState,
    current_state: GameState,
    moves: Vec<String>,
}

#[wasm_bindgen]
impl ZkProver {
    #[wasm_bindgen(constructor)]
    pub fn new() -> ZkProver {
        ZkProver {
            initial_state: GameState::new(),
            current_state: GameState::new(),
            moves: Vec::new(),
        }
    }
    
    pub fn add_move(&mut self, move_type: String) -> bool {
        if self.current_state.make_move(&move_type) {
            self.moves.push(move_type);
            true
        } else {
            false
        }
    }
    
    pub fn generate_proof(&self) -> String {
        // Generate zkProof commitment
        let proof_data = format!(
            "{}:{}:{}:{}:{}",
            self.initial_state.position.row,
            self.initial_state.position.col,
            self.current_state.position.row,
            self.current_state.position.col,
            self.moves.len()
        );
        
        // Simple hash (in production, use proper zkSNARK)
        let hash = self.simple_hash(&proof_data);
        format!("{:016x}", hash)
    }
    
    pub fn verify_proof(&self, proof: &str) -> bool {
        let generated = self.generate_proof();
        generated == proof
    }
    
    pub fn get_moves_count(&self) -> usize {
        self.moves.len()
    }
    
    pub fn get_current_position(&self) -> String {
        format!("({},{})", self.current_state.position.row, self.current_state.position.col)
    }
    
    pub fn compress_moves(&self) -> u64 {
        // Compress moves: 2 bits per move
        let mut compressed: u64 = 0;
        for (i, move_str) in self.moves.iter().enumerate() {
            let bits = match move_str.as_str() {
                "down_left" => 0b00,
                "down_right" => 0b01,
                "up_left" => 0b10,
                "up_right" => 0b11,
                _ => 0b00,
            };
            compressed |= (bits as u64) << (i * 2);
        }
        compressed
    }
    
    fn simple_hash(&self, data: &str) -> u64 {
        let mut hash: u64 = 5381;
        for byte in data.bytes() {
            hash = ((hash << 5).wrapping_add(hash)).wrapping_add(byte as u64);
        }
        hash
    }
}

#[wasm_bindgen]
pub fn hecke_eigenvalue(p: u8, shard: u8) -> u32 {
    (p as u32) * (shard as u32) + (p as u32) * (p as u32)
}

#[wasm_bindgen]
pub fn j_invariant(shard: u8) -> u32 {
    744 + 196884 * (shard as u32)
}

#[wasm_bindgen(start)]
pub fn main() {
    console_error_panic_hook::set_once();
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_game_state() {
        let mut state = GameState::new();
        assert_eq!(state.position.row, 0);
        assert_eq!(state.position.col, 0);
        assert_eq!(state.shard, 17);
        
        assert!(state.make_move("down_left"));
        assert_eq!(state.position.row, 1);
        assert_eq!(state.position.col, 0);
    }
    
    #[test]
    fn test_prover() {
        let mut prover = ZkProver::new();
        assert!(prover.add_move("down_left".to_string()));
        assert!(prover.add_move("down_right".to_string()));
        
        let proof = prover.generate_proof();
        assert!(prover.verify_proof(&proof));
    }
    
    #[test]
    fn test_hecke() {
        assert_eq!(hecke_eigenvalue(17, 17), 578);
    }
}
