use cicada71_contribution::Contribution;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    
    if args.len() < 4 {
        eprintln!("Usage: contribute <author> <shard> <sop_id>");
        eprintln!("\nExample:");
        eprintln!("  contribute alice 1 SOP-J-INVARIANT-001");
        std::process::exit(1);
    }
    
    let author = &args[1];
    let shard: u8 = args[2].parse().expect("Invalid shard (0-70)");
    let sop_id = &args[3];
    
    let mut contrib = Contribution::new(
        author.clone(),
        shard,
        sop_id.clone()
    );
    
    contrib.add_change("Initial contribution".to_string());
    
    if contrib.verify() {
        println!("✅ Contribution verified");
        println!("   Author: {}", contrib.author);
        println!("   Shard: {}", contrib.shard);
        println!("   SOP: {}", contrib.sop_id);
        println!("   Assigned shard: {}", contrib.to_shard());
    } else {
        eprintln!("❌ Contribution verification failed");
        std::process::exit(1);
    }
}
