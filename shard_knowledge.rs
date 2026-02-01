use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::fs;
use std::io::{BufRead, BufReader};

fn hash_fn(s: &str, seed: u64) -> u64 {
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    s.hash(&mut hasher);
    hasher.finish()
}

fn main() -> std::io::Result<()> {
    let file = fs::File::open("depth2")?;
    let reader = BufReader::new(file);
    
    println!("Path,Hash0,Hash1,Hash2,Hash3,Hash4,Hash5,Hash6,Hash7,Hash8,Hash9,Hash10,Hash11,Hash12,Hash13,Hash14,Hash15,Hash16,Hash17,Hash18,Hash19,Hash20,Hash21,Hash22,Hash23,Hash24,Hash25,Hash26,Hash27,Hash28,Hash29,Hash30,Hash31,Hash32,Hash33,Hash34,Hash35,Hash36,Hash37,Hash38,Hash39,Hash40,Hash41,Hash42,Hash43,Hash44,Hash45,Hash46,Hash47,Hash48,Hash49,Hash50,Hash51,Hash52,Hash53,Hash54,Hash55,Hash56,Hash57,Hash58,Hash59,Hash60,Hash61,Hash62,Hash63,Hash64,Hash65,Hash66,Hash67,Hash68,Hash69,Hash70,Sum,Shard");
    
    for line in reader.lines() {
        let path = line?;
        let mut hashes = Vec::new();
        let mut sum: u64 = 0;
        
        for i in 0..71 {
            let h = hash_fn(&path, i);
            hashes.push(h);
            sum = sum.wrapping_add(h);
        }
        
        let shard = sum % 71;
        
        print!("{}", path);
        for h in &hashes {
            print!(",{}", h);
        }
        println!(",{},{}", sum, shard);
    }
    
    Ok(())
}
