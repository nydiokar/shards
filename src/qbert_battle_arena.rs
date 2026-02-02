// Q*bert AI Battle Arena in Rust
// 71 protocols, genetic breeding, multi-user battles

use std::collections::HashMap;
use rand::Rng;
use serde::{Deserialize, Serialize};

// 71 Network Protocols
const PROTOCOLS: [&str; 71] = [
    // Web (0-9)
    "http", "https", "websocket", "webrtc", "sse",
    "http2", "http3", "grpc", "graphql", "rest",
    // P2P (10-19)
    "ipfs", "bittorrent", "libp2p", "dat", "hypercore",
    "scuttlebutt", "matrix", "xmpp", "irc", "mqtt",
    // Blockchain (20-29)
    "ethereum", "solana", "bitcoin", "polkadot", "cosmos",
    "avalanche", "near", "cardano", "algorand", "tezos",
    // Messaging (30-39)
    "smtp", "imap", "pop3", "amqp", "stomp",
    "zeromq", "nanomsg", "nats", "kafka", "rabbitmq",
    // RPC (40-49)
    "jsonrpc", "xmlrpc", "thrift", "protobuf", "msgpack",
    "capnproto", "flatbuffers", "avro", "bson", "cbor",
    // Streaming (50-59)
    "rtmp", "hls", "dash", "webm", "rtp",
    "rtsp", "srt", "udp", "quic", "sctp",
    // Exotic (60-70)
    "dns", "dhcp", "ntp", "snmp", "ldap",
    "radius", "diameter", "sip", "h323", "bluetooth",
    "zigbee"
];

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Position {
    row: u8,
    col: u8,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GameState {
    position: Position,
    cubes_changed: u8,
    shard: u8,
}

impl GameState {
    pub fn new(shard: u8) -> Self {
        GameState {
            position: Position { row: 0, col: 0 },
            cubes_changed: 0,
            shard,
        }
    }
    
    pub fn make_move(&mut self, move_type: &str) -> bool {
        let (row, col) = (self.position.row, self.position.col);
        
        let new_pos = match move_type {
            "down_left" => Position { row: row + 1, col },
            "down_right" => Position { row: row + 1, col: col + 1 },
            "up_left" => Position { row: row.saturating_sub(1), col: col.saturating_sub(1) },
            "up_right" => Position { row: row.saturating_sub(1), col },
            _ => return false,
        };
        
        if new_pos.row > 6 || new_pos.col > new_pos.row {
            return false;
        }
        
        self.position = new_pos;
        self.cubes_changed += 1;
        true
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AIOpponent {
    genome: Vec<u8>,  // 28 genes
    shard: u8,
    fitness: i32,
    wins: u32,
    losses: u32,
}

impl AIOpponent {
    pub fn new(shard: u8) -> Self {
        let mut rng = rand::thread_rng();
        let genome = (0..28).map(|_| rng.gen_range(0..4)).collect();
        
        AIOpponent {
            genome,
            shard,
            fitness: 0,
            wins: 0,
            losses: 0,
        }
    }
    
    pub fn choose_move(&self, state: &GameState) -> &'static str {
        let gene = self.genome[state.cubes_changed as usize % self.genome.len()];
        match gene % 4 {
            0 => "down_left",
            1 => "down_right",
            2 => "up_left",
            _ => "up_right",
        }
    }
    
    pub fn mutate(&mut self, rate: f32) {
        let mut rng = rand::thread_rng();
        for gene in &mut self.genome {
            if rng.gen::<f32>() < rate {
                *gene = rng.gen_range(0..4);
            }
        }
    }
    
    pub fn crossover(&self, other: &AIOpponent) -> AIOpponent {
        let point = self.genome.len() / 2;
        let mut child_genome = self.genome[..point].to_vec();
        child_genome.extend_from_slice(&other.genome[point..]);
        
        let child_shard = (self.shard as u16 + other.shard as u16) / 2;
        
        AIOpponent {
            genome: child_genome,
            shard: child_shard as u8,
            fitness: 0,
            wins: 0,
            losses: 0,
        }
    }
}

#[derive(Debug)]
pub struct BattleArena {
    protocol: String,
    shard: u8,
    players: Vec<Player>,
    leaderboard: Vec<LeaderboardEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Player {
    id: String,
    player_type: PlayerType,
    wins: u32,
    losses: u32,
    elo: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PlayerType {
    Human,
    AI(u8),  // AI shard
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LeaderboardEntry {
    player_id: String,
    wins: u32,
    losses: u32,
    elo: u32,
}

impl BattleArena {
    pub fn new(protocol: &str, shard: u8) -> Self {
        BattleArena {
            protocol: protocol.to_string(),
            shard,
            players: Vec::new(),
            leaderboard: Vec::new(),
        }
    }
    
    pub fn add_player(&mut self, id: String, player_type: PlayerType) {
        self.players.push(Player {
            id,
            player_type,
            wins: 0,
            losses: 0,
            elo: 1500,
        });
    }
    
    pub fn battle(&mut self, ai1: &AIOpponent, ai2: &AIOpponent) -> u8 {
        let mut state = GameState::new(self.shard);
        let mut rng = rand::thread_rng();
        
        for turn in 0..28 {
            let ai = if turn % 2 == 0 { ai1 } else { ai2 };
            let move_type = ai.choose_move(&state);
            state.make_move(move_type);
        }
        
        // Winner determined by random (simplified)
        if rng.gen::<bool>() { ai1.shard } else { ai2.shard }
    }
}

pub struct AIBreeder {
    population: Vec<AIOpponent>,
    generation: u32,
}

impl AIBreeder {
    pub fn new(size: usize) -> Self {
        let population = (0..size).map(|i| AIOpponent::new(i as u8 % 71)).collect();
        
        AIBreeder {
            population,
            generation: 0,
        }
    }
    
    pub fn evaluate_fitness(&mut self, arena: &mut BattleArena) {
        let mut rng = rand::thread_rng();
        
        for i in 0..self.population.len() {
            for _ in 0..5 {
                let j = rng.gen_range(0..self.population.len());
                if i != j {
                    let winner_shard = arena.battle(&self.population[i], &self.population[j]);
                    
                    if winner_shard == self.population[i].shard {
                        self.population[i].wins += 1;
                        self.population[i].fitness += 10;
                    } else {
                        self.population[i].losses += 1;
                        self.population[i].fitness -= 5;
                    }
                }
            }
        }
    }
    
    pub fn evolve(&mut self) {
        let mut new_population = Vec::new();
        
        // Elitism: keep top 10%
        self.population.sort_by(|a, b| b.fitness.cmp(&a.fitness));
        let elite_count = self.population.len() / 10;
        new_population.extend_from_slice(&self.population[..elite_count]);
        
        // Breed rest
        let mut rng = rand::thread_rng();
        while new_population.len() < self.population.len() {
            let p1 = rng.gen_range(0..elite_count * 2);
            let p2 = rng.gen_range(0..elite_count * 2);
            
            let mut child = self.population[p1].crossover(&self.population[p2]);
            child.mutate(0.1);
            new_population.push(child);
        }
        
        self.population = new_population;
        self.generation += 1;
    }
    
    pub fn top_n(&self, n: usize) -> Vec<&AIOpponent> {
        let mut sorted = self.population.iter().collect::<Vec<_>>();
        sorted.sort_by(|a, b| b.fitness.cmp(&a.fitness));
        sorted.into_iter().take(n).collect()
    }
}

pub fn run_battle_arena() {
    println!("🎮 Q*BERT AI BATTLE ARENA (RUST)");
    println!("{}", "=".repeat(70));
    
    // Initialize breeder
    println!("\n1️⃣  INITIALIZING AI POPULATION");
    println!("{}", "-".repeat(70));
    let mut breeder = AIBreeder::new(71);
    println!("✓ Created {} AI opponents", breeder.population.len());
    
    // Create arenas
    println!("\n2️⃣  CREATING BATTLE ARENAS");
    println!("{}", "-".repeat(70));
    let mut arenas: HashMap<String, BattleArena> = HashMap::new();
    
    for (i, protocol) in PROTOCOLS.iter().enumerate() {
        let shard = (i % 71) as u8;
        arenas.insert(protocol.to_string(), BattleArena::new(protocol, shard));
        
        if i % 10 == 0 {
            println!("Shard {:2}: {:15} arena created", shard, protocol);
        }
    }
    println!("✓ Created {} battle arenas", arenas.len());
    
    // Evolve population
    println!("\n3️⃣  EVOLVING AI POPULATION");
    println!("{}", "-".repeat(70));
    
    for gen in 0..5 {
        // Pick random arena
        let protocol = PROTOCOLS[gen % PROTOCOLS.len()];
        let arena = arenas.get_mut(protocol).unwrap();
        
        breeder.evaluate_fitness(arena);
        
        // Show top 3
        let top = breeder.top_n(3);
        println!("\nGeneration {}:", gen + 1);
        for (i, ai) in top.iter().enumerate() {
            println!("  {}. Shard {:2}: Fitness {:4} | W:{} L:{}", 
                     i + 1, ai.shard, ai.fitness, ai.wins, ai.losses);
        }
        
        breeder.evolve();
    }
    
    // Tournament
    println!("\n4️⃣  MULTI-USER TOURNAMENT");
    println!("{}", "-".repeat(70));
    
    let ws_arena = arenas.get_mut("websocket").unwrap();
    ws_arena.add_player("Alice".to_string(), PlayerType::Human);
    ws_arena.add_player("Bob".to_string(), PlayerType::Human);
    ws_arena.add_player("Charlie".to_string(), PlayerType::Human);
    
    let top_ais = breeder.top_n(3);
    println!("\nTournament on {} (Shard {}):", ws_arena.protocol, ws_arena.shard);
    
    for i in 0..10 {
        let winner_shard = ws_arena.battle(top_ais[0], top_ais[1]);
        println!("  Battle {}: AI-{} vs AI-{} → AI-{} wins!", 
                 i + 1, top_ais[0].shard, top_ais[1].shard, winner_shard);
    }
    
    println!("\n{}", "=".repeat(70));
    println!("⊢ Q*bert AI battle arena complete ∎");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_ai_opponent() {
        let ai = AIOpponent::new(17);
        assert_eq!(ai.shard, 17);
        assert_eq!(ai.genome.len(), 28);
    }
    
    #[test]
    fn test_crossover() {
        let ai1 = AIOpponent::new(10);
        let ai2 = AIOpponent::new(20);
        let child = ai1.crossover(&ai2);
        assert_eq!(child.genome.len(), 28);
    }
    
    #[test]
    fn test_battle_arena() {
        let mut arena = BattleArena::new("websocket", 17);
        arena.add_player("Alice".to_string(), PlayerType::Human);
        assert_eq!(arena.players.len(), 1);
    }
}
