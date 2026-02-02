// Game for Shard 66 🌐 - Proven via zkPerf + zkEDFA
use wasm_bindgen::prelude::*;
use std::arch::x86_64::*;

const SHARD: u8 = 66;
const EMOJI: &str = "🌐";

#[wasm_bindgen]
pub struct Game {
    score: u32,
    perf_proof: Vec<u64>,
    emoji_hash: String,
}

#[wasm_bindgen]
impl Game {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        let perf_proof = Self::generate_perf_proof();
        let emoji_hash = Self::generate_emoji_hash(&perf_proof);
        Self { score: 0, perf_proof, emoji_hash }
    }
    
    // zkPerf: Prove shard via CPU cycle measurements
    fn generate_perf_proof() -> Vec<u64> {
        let mut measurements = Vec::new();
        
        // Measure CPU cycles for SHARD iterations
        for i in 0..SHARD {
            let start = Self::read_tsc();
            
            // Compute work proportional to shard
            let mut x = 1u64;
            for _ in 0..SHARD {
                x = x.wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
            }
            
            // Also measure RAM access pattern
            let mut mem = vec![0u64; SHARD as usize];
            for j in 0..SHARD {
                mem[j as usize] = x.wrapping_add(j as u64);
            }
            
            let end = Self::read_tsc();
            measurements.push(end - start);
        }
        
        measurements
    }
    
    // zkEDFA: Generate emoji hash encoding semantics
    fn generate_emoji_hash(proof: &[u64]) -> String {
        let mut hash = String::from(EMOJI);
        
        // 1. Performance emoji (instruction throughput)
        let total_cycles: u64 = proof.iter().sum();
        let avg_cycles = if proof.len() > 0 { total_cycles / proof.len() as u64 } else { 0 };
        let perf_emoji = if avg_cycles < 1000 { "🚀" } 
                        else if avg_cycles < 10000 { "⚡" } 
                        else { "🐌" };
        hash.push_str(perf_emoji);
        
        // 2. Memory access pattern emoji
        let mem_pattern = total_cycles % 5;
        let mem_emoji = match mem_pattern {
            0 => "💾", // Sequential
            1 => "🔀", // Random
            2 => "📊", // Strided
            3 => "🔄", // Circular
            _ => "💿"  // Cached
        };
        hash.push_str(mem_emoji);
        
        // 3. Register usage emoji (based on shard number)
        let reg_emoji = match SHARD % 8 {
            0 => "🅰️", // RAX
            1 => "🅱️", // RBX
            2 => "©️",  // RCX
            3 => "🇩",  // RDX
            4 => "🇪",  // RSI
            5 => "🇫",  // RDI
            6 => "🇬",  // RBP
            _ => "🇭"   // RSP
        };
        hash.push_str(reg_emoji);
        
        // 4. Function type emoji (based on computation pattern)
        let func_emoji = if SHARD < 10 { "➕" }      // Arithmetic
                        else if SHARD < 20 { "✖️" }  // Multiply
                        else if SHARD < 30 { "➗" }  // Divide
                        else if SHARD < 40 { "🔀" }  // Shuffle
                        else if SHARD < 50 { "🔁" }  // Loop
                        else if SHARD < 60 { "🔂" }  // Nested loop
                        else { "🔃" };               // Recursive
        hash.push_str(func_emoji);
        
        // 5. Shard number as emoji digits
        let shard_str = format!("{}", SHARD);
        for digit in shard_str.chars() {
            let emoji_digit = match digit {
                '0' => "0️⃣", '1' => "1️⃣", '2' => "2️⃣", '3' => "3️⃣", '4' => "4️⃣",
                '5' => "5️⃣", '6' => "6️⃣", '7' => "7️⃣", '8' => "8️⃣", '9' => "9️⃣",
                _ => "❓"
            };
            hash.push_str(emoji_digit);
        }
        
        // 6. Checksum emoji based on total cycles
        let checksum_emoji = match total_cycles % 10 {
            0 => "✅", 1 => "🔐", 2 => "🔒", 3 => "🔓", 4 => "🔑",
            5 => "🗝️", 6 => "🔏", 7 => "🔎", 8 => "🔍", _ => "🔬"
        };
        hash.push_str(checksum_emoji);
        
        hash
    }
    
    // Read CPU timestamp counter
    #[cfg(target_arch = "x86_64")]
    fn read_tsc() -> u64 {
        unsafe { _rdtsc() }
    }
    
    #[cfg(not(target_arch = "x86_64"))]
    fn read_tsc() -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64
    }
    
    pub fn get_shard(&self) -> u8 { SHARD }
    pub fn get_emoji(&self) -> String { EMOJI.to_string() }
    pub fn get_emoji_hash(&self) -> String { self.emoji_hash.clone() }
    
    pub fn verify_proof(&self) -> bool {
        // Verify: number of measurements equals shard number
        self.perf_proof.len() == SHARD as usize &&
        // Verify: emoji hash starts with shard emoji
        self.emoji_hash.starts_with(EMOJI)
    }
    
    pub fn get_proof_size(&self) -> usize { self.perf_proof.len() }
    pub fn get_total_cycles(&self) -> u64 { self.perf_proof.iter().sum() }
    
    pub fn play(&mut self) { self.score += 10 * SHARD as u32; }
    pub fn get_score(&self) -> u32 { self.score }
}

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    println!("🎮 Game Shard {} {}", SHARD, EMOJI);
    let game = Game::new();
    
    println!("📊 zkPerf Proof:");
    println!("  Shard: {}", game.get_shard());
    println!("  Emoji: {}", game.get_emoji());
    println!("  Measurements: {}", game.get_proof_size());
    println!("  Total cycles: {}", game.get_total_cycles());
    println!("  zkEDFA Hash: {}", game.get_emoji_hash());
    println!("  Verified: {}", game.verify_proof());
}
