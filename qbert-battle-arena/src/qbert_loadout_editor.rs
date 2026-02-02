// Q*bert AI Player with Loadout Editor
// Self-modifying AI that updates its own program

use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Loadout {
    pub strategy: Strategy,
    pub weights: Vec<f32>,
    pub mutations: Vec<Mutation>,
    pub version: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Strategy {
    Aggressive,
    Defensive,
    Balanced,
    Adaptive,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Mutation {
    pub gene_index: usize,
    pub old_value: u8,
    pub new_value: u8,
    pub fitness_delta: i32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AIPlayer {
    pub id: String,
    pub genome: Vec<u8>,
    pub loadout: Loadout,
    pub fitness: i32,
    pub generation: u32,
}

impl AIPlayer {
    pub fn new(id: String) -> Self {
        AIPlayer {
            id,
            genome: (0..28).map(|_| rand::random::<u8>() % 4).collect(),
            loadout: Loadout {
                strategy: Strategy::Balanced,
                weights: vec![1.0; 28],
                mutations: Vec::new(),
                version: 1,
            },
            fitness: 0,
            generation: 0,
        }
    }
    
    pub fn choose_move(&self, state: &GameState) -> &'static str {
        let idx = state.cubes_changed as usize % self.genome.len();
        let gene = self.genome[idx];
        let weight = self.loadout.weights[idx];
        
        // Apply strategy modifier
        let modified = match self.loadout.strategy {
            Strategy::Aggressive => (gene as f32 * weight * 1.2) as u8,
            Strategy::Defensive => (gene as f32 * weight * 0.8) as u8,
            Strategy::Balanced => (gene as f32 * weight) as u8,
            Strategy::Adaptive => {
                // Adapt based on fitness
                let factor = 1.0 + (self.fitness as f32 / 100.0);
                (gene as f32 * weight * factor) as u8
            }
        };
        
        match modified % 4 {
            0 => "down_left",
            1 => "down_right",
            2 => "up_left",
            _ => "up_right",
        }
    }
    
    pub fn update_loadout(&mut self, battle_result: &BattleResult) {
        // Record mutation
        if let Some(last_mutation) = self.loadout.mutations.last() {
            let fitness_delta = battle_result.fitness_change;
            
            // If mutation improved fitness, keep it
            if fitness_delta > 0 {
                println!("✓ Mutation improved fitness by {}", fitness_delta);
            } else {
                // Revert mutation
                let idx = last_mutation.gene_index;
                self.genome[idx] = last_mutation.old_value;
                println!("✗ Mutation reverted (fitness delta: {})", fitness_delta);
            }
        }
        
        // Update weights based on performance
        for i in 0..self.loadout.weights.len() {
            if battle_result.moves_used[i] {
                self.loadout.weights[i] *= 1.1; // Increase weight for used moves
            } else {
                self.loadout.weights[i] *= 0.9; // Decrease weight for unused moves
            }
        }
        
        // Adapt strategy
        if self.fitness > 100 {
            self.loadout.strategy = Strategy::Aggressive;
        } else if self.fitness < -50 {
            self.loadout.strategy = Strategy::Defensive;
        }
        
        self.loadout.version += 1;
    }
    
    pub fn save_loadout(&self, path: &str) -> std::io::Result<()> {
        let json = serde_json::to_string_pretty(&self.loadout)?;
        fs::write(path, json)?;
        println!("💾 Loadout saved to {}", path);
        Ok(())
    }
    
    pub fn load_loadout(&mut self, path: &str) -> std::io::Result<()> {
        let json = fs::read_to_string(path)?;
        self.loadout = serde_json::from_str(&json)?;
        println!("📂 Loadout loaded from {}", path);
        Ok(())
    }
    
    pub fn self_modify(&mut self) {
        // AI modifies its own genome
        let idx = rand::random::<usize>() % self.genome.len();
        let old_value = self.genome[idx];
        let new_value = rand::random::<u8>() % 4;
        
        self.loadout.mutations.push(Mutation {
            gene_index: idx,
            old_value,
            new_value,
            fitness_delta: 0, // Will be updated after battle
        });
        
        self.genome[idx] = new_value;
        println!("🧬 Self-modified gene {}: {} → {}", idx, old_value, new_value);
    }
    
    pub fn generate_program(&self) -> String {
        // Generate Rust code for this AI
        let mut code = String::from("// Auto-generated AI Player\n\n");
        code.push_str("pub fn ai_move(cubes_changed: u8) -> &'static str {\n");
        code.push_str("    let genome = vec![");
        
        for (i, gene) in self.genome.iter().enumerate() {
            if i > 0 { code.push_str(", "); }
            code.push_str(&gene.to_string());
        }
        
        code.push_str("];\n");
        code.push_str("    let idx = cubes_changed as usize % genome.len();\n");
        code.push_str("    match genome[idx] % 4 {\n");
        code.push_str("        0 => \"down_left\",\n");
        code.push_str("        1 => \"down_right\",\n");
        code.push_str("        2 => \"up_left\",\n");
        code.push_str("        _ => \"up_right\",\n");
        code.push_str("    }\n");
        code.push_str("}\n");
        
        code
    }
    
    pub fn save_program(&self, path: &str) -> std::io::Result<()> {
        let code = self.generate_program();
        fs::write(path, code)?;
        println!("💻 Program saved to {}", path);
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GameState {
    pub position: (u8, u8),
    pub cubes_changed: u8,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BattleResult {
    pub winner: String,
    pub fitness_change: i32,
    pub moves_used: Vec<bool>,
}

pub struct LoadoutEditor {
    pub players: Vec<AIPlayer>,
}

impl LoadoutEditor {
    pub fn new() -> Self {
        LoadoutEditor {
            players: Vec::new(),
        }
    }
    
    pub fn create_player(&mut self, id: String) -> &mut AIPlayer {
        let player = AIPlayer::new(id);
        self.players.push(player);
        self.players.last_mut().unwrap()
    }
    
    pub fn edit_strategy(&mut self, player_id: &str, strategy: Strategy) {
        if let Some(player) = self.players.iter_mut().find(|p| p.id == player_id) {
            player.loadout.strategy = strategy;
            println!("✏️  Updated {} strategy to {:?}", player_id, strategy);
        }
    }
    
    pub fn edit_weights(&mut self, player_id: &str, weights: Vec<f32>) {
        if let Some(player) = self.players.iter_mut().find(|p| p.id == player_id) {
            player.loadout.weights = weights;
            println!("✏️  Updated {} weights", player_id);
        }
    }
    
    pub fn auto_tune(&mut self, player_id: &str, iterations: u32) {
        if let Some(player) = self.players.iter_mut().find(|p| p.id == player_id) {
            println!("🔧 Auto-tuning {} for {} iterations...", player_id, iterations);
            
            for i in 0..iterations {
                // Self-modify
                player.self_modify();
                
                // Simulate battle
                let result = BattleResult {
                    winner: player_id.to_string(),
                    fitness_change: rand::random::<i32>() % 20 - 10,
                    moves_used: (0..28).map(|_| rand::random()).collect(),
                };
                
                player.fitness += result.fitness_change;
                player.update_loadout(&result);
                
                if i % 10 == 0 {
                    println!("  Iteration {}: Fitness = {}", i, player.fitness);
                }
            }
            
            player.generation += 1;
            println!("✓ Auto-tune complete. Final fitness: {}", player.fitness);
        }
    }
    
    pub fn export_all(&self, dir: &str) -> std::io::Result<()> {
        fs::create_dir_all(dir)?;
        
        for player in &self.players {
            let loadout_path = format!("{}/{}_loadout.json", dir, player.id);
            let program_path = format!("{}/{}_ai.rs", dir, player.id);
            
            player.save_loadout(&loadout_path)?;
            player.save_program(&program_path)?;
        }
        
        println!("📦 Exported {} players to {}", self.players.len(), dir);
        Ok(())
    }
}

pub fn demo_loadout_editor() {
    println!("🎮 Q*BERT AI LOADOUT EDITOR");
    println!("{}", "=".repeat(70));
    
    let mut editor = LoadoutEditor::new();
    
    // Create players
    println!("\n1️⃣  CREATING AI PLAYERS");
    println!("{}", "-".repeat(70));
    
    let player1 = editor.create_player("Alpha".to_string());
    println!("✓ Created player: {}", player1.id);
    
    let player2 = editor.create_player("Beta".to_string());
    println!("✓ Created player: {}", player2.id);
    
    let player3 = editor.create_player("Gamma".to_string());
    println!("✓ Created player: {}", player3.id);
    
    // Edit strategies
    println!("\n2️⃣  EDITING STRATEGIES");
    println!("{}", "-".repeat(70));
    
    editor.edit_strategy("Alpha", Strategy::Aggressive);
    editor.edit_strategy("Beta", Strategy::Defensive);
    editor.edit_strategy("Gamma", Strategy::Adaptive);
    
    // Auto-tune
    println!("\n3️⃣  AUTO-TUNING");
    println!("{}", "-".repeat(70));
    
    editor.auto_tune("Alpha", 50);
    editor.auto_tune("Beta", 50);
    editor.auto_tune("Gamma", 50);
    
    // Show results
    println!("\n4️⃣  FINAL STATS");
    println!("{}", "-".repeat(70));
    
    for player in &editor.players {
        println!("\n{} (Gen {}):", player.id, player.generation);
        println!("  Strategy: {:?}", player.loadout.strategy);
        println!("  Fitness: {}", player.fitness);
        println!("  Loadout version: {}", player.loadout.version);
        println!("  Mutations: {}", player.loadout.mutations.len());
    }
    
    // Export
    println!("\n5️⃣  EXPORTING");
    println!("{}", "-".repeat(70));
    
    editor.export_all("data/ai_loadouts").unwrap();
    
    println!("\n{}", "=".repeat(70));
    println!("⊢ Loadout editor complete ∎");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_ai_player() {
        let player = AIPlayer::new("Test".to_string());
        assert_eq!(player.genome.len(), 28);
        assert_eq!(player.generation, 0);
    }
    
    #[test]
    fn test_self_modify() {
        let mut player = AIPlayer::new("Test".to_string());
        let old_genome = player.genome.clone();
        player.self_modify();
        assert_ne!(player.genome, old_genome);
    }
    
    #[test]
    fn test_generate_program() {
        let player = AIPlayer::new("Test".to_string());
        let code = player.generate_program();
        assert!(code.contains("pub fn ai_move"));
    }
}
