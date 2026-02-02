use std::collections::HashMap;
use std::path::Path;
use sha2::{Sha256, Digest};

pub struct ShardDistribution {
    pub shards: HashMap<u8, Vec<String>>,
    pub total_files: usize,
}

pub fn shard_files(paths: &[&Path]) -> ShardDistribution {
    let mut shards: HashMap<u8, Vec<String>> = HashMap::new();
    
    for path in paths {
        if let Ok(content) = std::fs::read(path) {
            // Hash content
            let mut hasher = Sha256::new();
            hasher.update(&content);
            let hash = hasher.finalize();
            
            // Shard via mod 71
            let shard = (hash[0] as u64 % 71) as u8;
            
            shards.entry(shard)
                .or_insert_with(Vec::new)
                .push(path.to_string_lossy().to_string());
        }
    }
    
    let total_files = paths.len();
    
    ShardDistribution { shards, total_files }
}

pub fn print_distribution(dist: &ShardDistribution) {
    println!("Shard Distribution (71 shards):");
    println!("Total files: {}", dist.total_files);
    println!();
    
    for shard in 0..71 {
        if let Some(files) = dist.shards.get(&shard) {
            let bar = "█".repeat(files.len().min(50));
            println!("  Shard {:2}: {:3} files {}", shard, files.len(), bar);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_sharding() {
        let paths = vec![
            Path::new("SimpleExprMonster.lean"),
            Path::new("MetaCoqMonsterProof.lean"),
        ];
        let dist = shard_files(&paths);
        assert!(dist.shards.len() > 0);
    }
}
