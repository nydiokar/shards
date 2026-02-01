use std::collections::HashMap;

const MORSE_CODE: &[(&str, &str)] = &[
    ("A", ".-"),    ("B", "-..."),  ("C", "-.-."),  ("D", "-.."),
    ("E", "."),     ("F", "..-."),  ("G", "--."),   ("H", "...."),
    ("I", ".."),    ("J", ".---"),  ("K", "-.-"),   ("L", ".-.."),
    ("M", "--"),    ("N", "-."),    ("O", "---"),   ("P", ".--."),
    ("Q", "--.-"),  ("R", ".-."),   ("S", "..."),   ("T", "-"),
    ("U", "..-"),   ("V", "...-"),  ("W", ".--"),   ("X", "-..-"),
    ("Y", "-.--"),  ("Z", "--.."),
    ("0", "-----"), ("1", ".----"), ("2", "..---"), ("3", "...--"),
    ("4", "....-"), ("5", "....."), ("6", "-...."), ("7", "--..."),
    ("8", "---.."), ("9", "----."),
    (" ", "/"),
];

struct MorseTower {
    shard_id: usize,
    callsign: String,
    frequency_mhz: f64,
    band: String,
}

impl MorseTower {
    fn new(shard_id: usize) -> Self {
        let (freq, band) = Self::assign_frequency(shard_id);
        let callsign = Self::generate_callsign(shard_id);
        
        MorseTower {
            shard_id,
            callsign,
            frequency_mhz: freq,
            band,
        }
    }
    
    fn assign_frequency(shard_id: usize) -> (f64, String) {
        match shard_id {
            0..=9   => (3.5 + (shard_id as f64 * 0.05), "80m".to_string()),
            10..=19 => (7.0 + ((shard_id - 10) as f64 * 0.03), "40m".to_string()),
            20..=29 => (14.0 + ((shard_id - 20) as f64 * 0.035), "20m".to_string()),
            30..=39 => (21.0 + ((shard_id - 30) as f64 * 0.045), "15m".to_string()),
            40..=49 => (28.0 + ((shard_id - 40) as f64 * 0.17), "10m".to_string()),
            50..=59 => (144.0 + ((shard_id - 50) as f64 * 0.4), "2m".to_string()),
            60..=69 => (420.0 + ((shard_id - 60) as f64 * 3.0), "70cm".to_string()),
            70      => (1296.0, "23cm".to_string()),
            _       => (14.196, "20m".to_string()),
        }
    }
    
    fn generate_callsign(shard_id: usize) -> String {
        format!("M{}NST", shard_id)
    }
    
    fn encode_morse(text: &str) -> String {
        text.to_uppercase()
            .chars()
            .filter_map(|c| {
                MORSE_CODE.iter()
                    .find(|(ch, _)| ch.chars().next() == Some(c))
                    .map(|(_, morse)| *morse)
            })
            .collect::<Vec<_>>()
            .join(" ")
    }
    
    fn transmit(&self, message: &str) {
        let morse = Self::encode_morse(message);
        
        println!("📡 {} transmitting on {:.3} MHz ({})", 
            self.callsign, self.frequency_mhz, self.band);
        println!("   Message: {}", message);
        println!("   Morse:   {}", morse);
        println!();
    }
}

fn main() {
    println!("📻 CICADA-71 Morse Code Towers");
    println!("================================\n");
    
    // Create towers for first 10 shards
    let towers: Vec<MorseTower> = (0..10)
        .map(|i| MorseTower::new(i))
        .collect();
    
    println!("Frequency allocation:\n");
    for tower in &towers {
        println!("  Shard {:2}: {} - {:.3} MHz ({})", 
            tower.shard_id, tower.callsign, tower.frequency_mhz, tower.band);
    }
    println!();
    
    // Transmit Gödel number
    println!("Transmitting Gödel number:\n");
    towers[0].transmit("GODEL 67500000");
    
    // Transmit j-invariant
    println!("Transmitting j-invariant:\n");
    towers[1].transmit("JINV 744 196884");
    
    // Transmit Monster dimension
    println!("Transmitting Monster dimension:\n");
    towers[2].transmit("MONSTER 196883");
    
    // Special: Shard 70 moonbounce
    let moonbounce = MorseTower::new(70);
    println!("🌙 Moonbounce transmission:\n");
    moonbounce.transmit("MOONSHINE");
    
    println!("Monster resonance: 9,936 Hz");
    println!("Bott periodicity: 10 rounds");
    println!("\n73 de M0NST 📡");
}
