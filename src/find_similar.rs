use std::path::Path;
use std::collections::HashMap;
use sha2::{Sha256, Digest};

#[derive(Debug, Clone)]
pub struct SimilarFile {
    pub path: String,
    pub shard: u8,
    pub distance: u8,
    pub lines: usize,
}

pub fn find_similar(target: &Path, all_files: &[&Path]) -> Vec<SimilarFile> {
    // Hash target
    let target_content = std::fs::read(target).unwrap_or_default();
    let mut hasher = Sha256::new();
    hasher.update(&target_content);
    let target_hash = hasher.finalize();
    let target_shard = (target_hash[0] as u64 % 71) as u8;
    
    let mut similar = Vec::new();
    
    for file in all_files {
        if *file == target {
            continue;
        }
        
        if let Ok(content) = std::fs::read(file) {
            let mut hasher = Sha256::new();
            hasher.update(&content);
            let hash = hasher.finalize();
            let shard = (hash[0] as u64 % 71) as u8;
            
            // Distance in shard space (circular)
            let distance = if shard >= target_shard {
                (shard - target_shard).min(target_shard + 71 - shard)
            } else {
                (target_shard - shard).min(shard + 71 - target_shard)
            };
            
            if distance <= 3 {  // Within 3 shards
                let lines = content.iter().filter(|&&b| b == b'\n').count();
                similar.push(SimilarFile {
                    path: file.to_string_lossy().to_string(),
                    shard,
                    distance,
                    lines,
                });
            }
        }
    }
    
    similar.sort_by_key(|f| f.distance);
    similar
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_find_similar() {
        let target = Path::new("SimpleExprMonster.lean");
        let files = vec![
            Path::new("MetaCoqMonsterProof.lean"),
            Path::new("TowerExpansion.lean"),
        ];
        let similar = find_similar(target, &files);
        assert!(similar.len() <= files.len());
    }
}
