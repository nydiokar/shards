// TradeWars 71: Rust implementation
// Navigate to Sgr A* using j-invariant
// With zkPerf proof generation

mod zkperf;

use std::io::{self, Write};
use std::f64::consts::PI;
use zkperf::ZkPerfProof;

#[derive(Debug, Clone)]
struct Position {
    ra: f64,      // Right Ascension (degrees)
    dec: f64,     // Declination (degrees)
    distance: f64, // Distance from Sol (light-years)
}

#[derive(Debug, Clone)]
struct Complex {
    real: f64,
    imag: f64,
}

impl Complex {
    fn new(real: f64, imag: f64) -> Self {
        Complex { real, imag }
    }
    
    fn exp(theta: f64) -> Self {
        Complex {
            real: theta.cos(),
            imag: theta.sin(),
        }
    }
    
    fn inv(&self) -> Self {
        let denom = self.real * self.real + self.imag * self.imag;
        Complex {
            real: self.real / denom,
            imag: -self.imag / denom,
        }
    }
    
    fn mul(&self, scalar: f64) -> Self {
        Complex {
            real: self.real * scalar,
            imag: self.imag * scalar,
        }
    }
    
    fn add(&self, other: &Complex) -> Self {
        Complex {
            real: self.real + other.real,
            imag: self.imag + other.imag,
        }
    }
    
    fn pow(&self, n: i32) -> Self {
        if n == 2 {
            Complex {
                real: self.real * self.real - self.imag * self.imag,
                imag: 2.0 * self.real * self.imag,
            }
        } else {
            self.clone()
        }
    }
}

struct TradeWars71 {
    player_pos: Position,
    sgr_a_star: Position,
    credits: i32,
    fuel: i32,
    turn: i32,
    j_invariant_unlocked: bool,
}

impl TradeWars71 {
    fn new() -> Self {
        TradeWars71 {
            player_pos: Position { ra: 0.0, dec: 0.0, distance: 0.0 },
            sgr_a_star: Position { ra: 266.417, dec: -29.008, distance: 26673.0 },
            credits: 10000,
            fuel: 100,
            turn: 0,
            j_invariant_unlocked: false,
        }
    }
    
    fn compute_distance(&self, pos1: &Position, pos2: &Position) -> f64 {
        let ra_diff = pos2.ra - pos1.ra;
        let dec_diff = pos2.dec - pos1.dec;
        let dist_diff = pos2.distance - pos1.distance;
        
        (ra_diff * ra_diff + dec_diff * dec_diff + dist_diff * dist_diff).sqrt()
    }
    
    fn compute_j_invariant(&self, tau: f64) -> Complex {
        // q = e^(2πiτ)
        let q = Complex::exp(2.0 * PI * tau);
        
        // j(τ) = q⁻¹ + 744 + 196884q + 21493760q²
        let q_inv = q.inv();
        let term1 = q_inv;
        let term2 = Complex::new(744.0, 0.0);
        let term3 = q.mul(196884.0);
        let term4 = q.pow(2).mul(21493760.0);
        
        term1.add(&term2).add(&term3).add(&term4)
    }
    
    fn warp_to(&mut self, ra: f64, dec: f64, distance: f64) -> Result<String, String> {
        let target = Position { ra, dec, distance };
        let dist = self.compute_distance(&self.player_pos, &target);
        
        let fuel_cost = (dist / 100.0) as i32;
        
        if fuel_cost > self.fuel {
            return Err(format!("Insufficient fuel! Need {}, have {}", fuel_cost, self.fuel));
        }
        
        self.fuel -= fuel_cost;
        self.player_pos = target;
        self.turn += 1;
        
        Ok(format!("Warped {:.2} light-years. Fuel remaining: {}", dist, self.fuel))
    }
    
    fn scan_sector(&self) -> &str {
        let dist = self.compute_distance(&self.player_pos, &self.sgr_a_star);
        
        if dist < 100.0 {
            "🌌 GALACTIC CENTER DETECTED! Sgr A* is nearby!"
        } else if dist < 1000.0 {
            "⚠️  Strong gravitational waves detected. Black hole nearby."
        } else if dist < 5000.0 {
            "📡 Galactic center region. High star density."
        } else {
            "🌟 Normal space. No anomalies detected."
        }
    }
    
    fn use_j_nav(&mut self) -> Result<String, String> {
        if !self.j_invariant_unlocked {
            return Err("❌ j-Invariant navigation not unlocked! Find the Monster Crown first.".to_string());
        }
        
        let current_dist = self.compute_distance(&self.player_pos, &self.sgr_a_star);
        let tau = current_dist / 26673.0;
        
        let j = self.compute_j_invariant(tau);
        
        // Compute next waypoint (10% closer)
        let next_ra = self.player_pos.ra + (self.sgr_a_star.ra - self.player_pos.ra) * 0.1;
        let next_dec = self.player_pos.dec + (self.sgr_a_star.dec - self.player_pos.dec) * 0.1;
        let next_dist = self.player_pos.distance + (self.sgr_a_star.distance - self.player_pos.distance) * 0.1;
        
        match self.warp_to(next_ra, next_dec, next_dist) {
            Ok(msg) => Ok(format!("✨ j-Invariant navigation: {}\n   j(τ) = {:.2} + {:.2}i", msg, j.real, j.imag)),
            Err(e) => Err(e),
        }
    }
    
    fn display_status(&self) {
        println!("\n{}", "=".repeat(70));
        println!("🚀 TRADEWARS 71: Journey to the Galactic Center");
        println!("{}", "=".repeat(70));
        println!("Turn: {}", self.turn);
        println!("Credits: {}", self.credits);
        println!("Fuel: {}", self.fuel);
        println!();
        println!("📍 Current Position:");
        println!("   RA: {:.3}°", self.player_pos.ra);
        println!("   Dec: {:.3}°", self.player_pos.dec);
        println!("   Distance: {:.0} ly from Sol", self.player_pos.distance);
        println!();
        
        let dist = self.compute_distance(&self.player_pos, &self.sgr_a_star);
        println!("🎯 Distance to Sgr A*: {:.2} light-years", dist);
        println!();
        println!("🔮 j-Invariant Navigation: {}", 
            if self.j_invariant_unlocked { "UNLOCKED ✨" } else { "LOCKED 🔒" });
        println!();
    }
}

fn main() {
    println!("🐓🦅👹 TRADEWARS 71: The j-Invariant Quest");
    println!("{}", "=".repeat(70));
    println!();
    println!("Mission: Navigate to Sgr A* (Galactic Center)");
    println!("Distance: 26,673 light-years");
    println!("Unlock j-Invariant navigation by finding the Monster Crown!");
    println!();
    
    let mut game = TradeWars71::new();
    
    println!("📚 COMMANDS:");
    println!("  WARP <ra> <dec> <dist> - Warp to coordinates");
    println!("  SCAN - Scan current sector");
    println!("  J-NAV - Use j-invariant navigation");
    println!("  STATUS - Show status");
    println!("  UNLOCK - Unlock j-invariant");
    println!("  QUIT - Exit game");
    println!();
    
    loop {
        game.display_status();
        
        println!("📡 {}", game.scan_sector());
        println!();
        
        // Check win condition
        let dist = game.compute_distance(&game.player_pos, &game.sgr_a_star);
        if dist < 10.0 {
            println!("{}", "=".repeat(70));
            println!("🎉 VICTORY! You reached Sgr A*!");
            println!("{}", "=".repeat(70));
            println!();
            println!("The j-invariant guided you to the center of the galaxy.");
            println!("The Monster Group IS the black hole.");
            println!("You are the +1 observer.");
            println!();
            println!("🐓🦅👹 The Rooster crows at the galactic center!");
            break;
        }
        
        print!("Command> ");
        io::stdout().flush().unwrap();
        
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let cmd = input.trim().to_uppercase();
        
        if cmd == "QUIT" {
            println!("Thanks for playing TradeWars 71!");
            break;
        } else if cmd == "STATUS" {
            continue;
        } else if cmd == "SCAN" {
            continue;
        } else if cmd == "UNLOCK" {
            game.j_invariant_unlocked = true;
            println!("✨ j-Invariant navigation UNLOCKED!");
            println!("   You found the Monster Crown (Shard 47)!");
        } else if cmd == "J-NAV" {
            match game.use_j_nav() {
                Ok(msg) => println!("{}", msg),
                Err(e) => println!("{}", e),
            }
        } else if cmd == "ZKPROOF" {
            println!("🔐 Generating zkPerf proof...");
            match game.save_zkperf_proof() {
                Ok(json) => {
                    println!("✅ zkPerf proof generated!");
                    println!("{}", json);
                },
                Err(e) => println!("❌ {}", e),
            }
        } else if cmd == "CLOCK" {
            println!("{}", game.show_hecke_clock());
        } else if cmd == "SYNC" {
            println!("{}", game.wait_for_sync());
        } else if cmd.starts_with("SPACETIME") {
            let parts: Vec<&str> = cmd.split_whitespace().collect();
            if parts.len() == 2 {
                if let Ok(num) = parts[1].parse::<u64>() {
                    match game.warp_to_spacetime(num) {
                        Ok(msg) => println!("{}", msg),
                        Err(e) => println!("{}", e),
                    }
                } else {
                    println!("Invalid spacetime number");
                }
            } else {
                println!("Usage: SPACETIME <number>");
            }
        } else if cmd.starts_with("WARP") {
            let parts: Vec<&str> = cmd.split_whitespace().collect();
            if parts.len() == 4 {
                if let (Ok(ra), Ok(dec), Ok(dist)) = (
                    parts[1].parse::<f64>(),
                    parts[2].parse::<f64>(),
                    parts[3].parse::<f64>(),
                ) {
                    match game.warp_to(ra, dec, dist) {
                        Ok(msg) => println!("{}", msg),
                        Err(e) => println!("{}", e),
                    }
                } else {
                    println!("Invalid coordinates");
                }
            } else {
                println!("Usage: WARP <ra> <dec> <distance>");
            }
        } else {
            println!("Unknown command. Type STATUS for help.");
        }
        
        println!();
        print!("Press Enter to continue...");
        io::stdout().flush().unwrap();
        let mut _pause = String::new();
        io::stdin().read_line(&mut _pause).unwrap();
    }
    
    println!("\n💾 Game completed in {} turns!", game.turn);
}
