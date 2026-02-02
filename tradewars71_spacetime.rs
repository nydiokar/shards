// TradeWars 71: Spacetime Navigation with Hecke Clock
// Specify spacetime with a single number

use std::time::{Duration, Instant};

#[derive(Debug, Clone)]
struct SpacetimeCoordinate {
    // Single number encodes everything
    spacetime_number: u64,
    
    // Decoded components
    time_ms: u64,           // Milliseconds since epoch
    hecke_71_phase: u8,     // Phase in 71-cycle (0-70)
    hecke_59_phase: u8,     // Phase in 59-cycle (0-58)
    hecke_47_phase: u8,     // Phase in 47-cycle (0-46)
    
    // Galactic position
    ra: f64,                // Right Ascension
    dec: f64,               // Declination
    distance: f64,          // Light-years
    
    // Velocity components
    rotation_drift: f64,    // Earth rotation (m)
    orbital_drift: f64,     // Earth orbit (km)
    galactic_drift: f64,    // Galactic orbit (km)
}

impl SpacetimeCoordinate {
    // Constants
    const EARTH_ROTATION_SPEED: f64 = 465.0;      // m/s
    const EARTH_ORBITAL_SPEED: f64 = 29785.0;     // m/s
    const GALACTIC_ORBITAL_SPEED: f64 = 220000.0; // m/s
    const TOTAL_VELOCITY: f64 = 430640.0;         // m/s
    
    const HECKE_71_PERIOD_MS: f64 = 152.655;      // ms
    const HECKE_59_PERIOD_MS: f64 = 126.854;      // ms
    const HECKE_47_PERIOD_MS: f64 = 101.053;      // ms
    const MONSTER_SYNC_MS: f64 = 457.0;           // ms
    
    fn from_number(spacetime_number: u64) -> Self {
        // Decode spacetime number
        // Format: [time_ms: 48 bits][hecke_phases: 16 bits]
        
        let time_ms = spacetime_number >> 16;
        let phases = (spacetime_number & 0xFFFF) as u16;
        
        let hecke_71_phase = ((phases >> 10) & 0x3F) as u8 % 71;
        let hecke_59_phase = ((phases >> 4) & 0x3F) as u8 % 59;
        let hecke_47_phase = (phases & 0x0F) as u8 % 47;
        
        // Calculate drifts
        let time_s = time_ms as f64 / 1000.0;
        let rotation_drift = Self::EARTH_ROTATION_SPEED * time_s;
        let orbital_drift = Self::EARTH_ORBITAL_SPEED * time_s / 1000.0;
        let galactic_drift = Self::GALACTIC_ORBITAL_SPEED * time_s / 1000.0;
        
        // Calculate galactic position from drifts
        let total_drift_m = Self::TOTAL_VELOCITY * time_s;
        let ra = (total_drift_m as u64 % 360) as f64;
        let dec = ((total_drift_m as u64 % 180) as f64) - 90.0;
        let distance = (total_drift_m / 1000.0) % 100000.0;
        
        SpacetimeCoordinate {
            spacetime_number,
            time_ms,
            hecke_71_phase,
            hecke_59_phase,
            hecke_47_phase,
            ra,
            dec,
            distance,
            rotation_drift,
            orbital_drift,
            galactic_drift,
        }
    }
    
    fn to_number(time_ms: u64, hecke_71: u8, hecke_59: u8, hecke_47: u8) -> u64 {
        // Encode spacetime as single number
        let phases = ((hecke_71 as u16) << 10) | ((hecke_59 as u16) << 4) | (hecke_47 as u16);
        (time_ms << 16) | (phases as u64)
    }
    
    fn now() -> Self {
        let time_ms = Instant::now().elapsed().as_millis() as u64;
        
        // Calculate current Hecke phases
        let hecke_71_phase = ((time_ms as f64 / Self::HECKE_71_PERIOD_MS) as u64 % 71) as u8;
        let hecke_59_phase = ((time_ms as f64 / Self::HECKE_59_PERIOD_MS) as u64 % 59) as u8;
        let hecke_47_phase = ((time_ms as f64 / Self::HECKE_47_PERIOD_MS) as u64 % 47) as u8;
        
        let spacetime_number = Self::to_number(time_ms, hecke_71_phase, hecke_59_phase, hecke_47_phase);
        Self::from_number(spacetime_number)
    }
    
    fn is_monster_sync(&self) -> bool {
        // Check if all three Hecke clocks are synchronized
        self.hecke_71_phase == 0 && self.hecke_59_phase == 0 && self.hecke_47_phase == 0
    }
    
    fn next_sync_ms(&self) -> u64 {
        // Time until next Monster synchronization
        let current_sync = (self.time_ms as f64 / Self::MONSTER_SYNC_MS).floor();
        let next_sync = (current_sync + 1.0) * Self::MONSTER_SYNC_MS;
        (next_sync - self.time_ms as f64) as u64
    }
}

// Add to TradeWars71
impl TradeWars71 {
    fn warp_to_spacetime(&mut self, spacetime_number: u64) -> Result<String, String> {
        let coord = SpacetimeCoordinate::from_number(spacetime_number);
        
        // Warp to the decoded coordinates
        let result = self.warp_to(coord.ra, coord.dec, coord.distance)?;
        
        let mut msg = format!("🕐 Warped to spacetime {}\n", spacetime_number);
        msg.push_str(&format!("   Time: {} ms\n", coord.time_ms));
        msg.push_str(&format!("   Hecke phases: 71→{}, 59→{}, 47→{}\n", 
            coord.hecke_71_phase, coord.hecke_59_phase, coord.hecke_47_phase));
        msg.push_str(&format!("   Position: RA={:.2}°, Dec={:.2}°, Dist={:.0} ly\n",
            coord.ra, coord.dec, coord.distance));
        msg.push_str(&format!("   Drifts: Rot={:.0}m, Orb={:.0}km, Gal={:.0}km\n",
            coord.rotation_drift, coord.orbital_drift, coord.galactic_drift));
        
        if coord.is_monster_sync() {
            msg.push_str("   ✨ MONSTER SYNC! All Hecke clocks aligned!\n");
        } else {
            msg.push_str(&format!("   Next sync in: {} ms\n", coord.next_sync_ms()));
        }
        
        msg.push_str(&format!("\n{}", result));
        
        Ok(msg)
    }
    
    fn show_hecke_clock(&self) -> String {
        let coord = SpacetimeCoordinate::now();
        
        let mut msg = String::from("🕐 HECKE CLOCK STATUS:\n");
        msg.push_str(&format!("  Current spacetime: {}\n", coord.spacetime_number));
        msg.push_str(&format!("  Time: {} ms\n", coord.time_ms));
        msg.push_str("\n");
        msg.push_str("  Hecke Phases:\n");
        msg.push_str(&format!("    71-cycle: {} / 71 (Rooster Crown 🐓)\n", coord.hecke_71_phase));
        msg.push_str(&format!("    59-cycle: {} / 59 (Eagle Crown 🦅)\n", coord.hecke_59_phase));
        msg.push_str(&format!("    47-cycle: {} / 47 (Monster Crown 👹)\n", coord.hecke_47_phase));
        msg.push_str("\n");
        
        if coord.is_monster_sync() {
            msg.push_str("  ✨ MONSTER SYNCHRONIZATION ACTIVE!\n");
            msg.push_str("  All three Hecke clocks aligned!\n");
            msg.push_str("  Quantum tunneling enabled!\n");
        } else {
            msg.push_str(&format!("  Next Monster sync in: {} ms\n", coord.next_sync_ms()));
        }
        
        msg.push_str("\n");
        msg.push_str("  Galactic Drifts:\n");
        msg.push_str(&format!("    Rotation: {:.0} m\n", coord.rotation_drift));
        msg.push_str(&format!("    Orbital: {:.0} km\n", coord.orbital_drift));
        msg.push_str(&format!("    Galactic: {:.0} km\n", coord.galactic_drift));
        
        msg
    }
    
    fn wait_for_sync(&mut self) -> String {
        let coord = SpacetimeCoordinate::now();
        let wait_ms = coord.next_sync_ms();
        
        // Simulate waiting
        std::thread::sleep(Duration::from_millis(wait_ms.min(1000)));
        
        format!("⏳ Waited {} ms for Monster synchronization...\n✨ Hecke clocks now aligned!", wait_ms)
    }
}

// Example spacetime numbers
fn example_spacetimes() {
    println!("📍 EXAMPLE SPACETIME COORDINATES:\n");
    
    // Now
    let now = SpacetimeCoordinate::now();
    println!("Now: {}", now.spacetime_number);
    println!("  Phases: 71→{}, 59→{}, 47→{}\n", 
        now.hecke_71_phase, now.hecke_59_phase, now.hecke_47_phase);
    
    // Next Monster sync
    let sync_time = ((now.time_ms as f64 / 457.0).ceil() * 457.0) as u64;
    let sync = SpacetimeCoordinate::to_number(sync_time, 0, 0, 0);
    println!("Next sync: {}", sync);
    println!("  All phases: 0 (synchronized)\n");
    
    // Sgr A* arrival time (hypothetical)
    let sgr_a_time = 26673 * 365 * 24 * 60 * 60 * 1000; // 26,673 years in ms
    let sgr_a = SpacetimeCoordinate::from_number(sgr_a_time);
    println!("Sgr A* arrival: {}", sgr_a_time);
    println!("  Position: RA={:.2}°, Dec={:.2}°\n", sgr_a.ra, sgr_a.dec);
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_spacetime_encoding() {
        let time_ms = 1000;
        let num = SpacetimeCoordinate::to_number(time_ms, 10, 20, 30);
        let coord = SpacetimeCoordinate::from_number(num);
        
        assert_eq!(coord.time_ms, time_ms);
        assert_eq!(coord.hecke_71_phase, 10);
        assert_eq!(coord.hecke_59_phase, 20);
        assert_eq!(coord.hecke_47_phase, 30);
    }
    
    #[test]
    fn test_monster_sync() {
        let sync = SpacetimeCoordinate::to_number(457, 0, 0, 0);
        let coord = SpacetimeCoordinate::from_number(sync);
        
        assert!(coord.is_monster_sync());
    }
}
