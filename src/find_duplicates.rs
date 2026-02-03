use std::collections::HashMap;
use std::path::Path;
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Duplicate {
    pub files: Vec<String>,
    pub hash: String,
    pub lines: usize,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct NearDuplicate {
    pub files: Vec<String>,
    pub shard: u8,
    pub lines: usize,
    pub similarity: f64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DuplicateReport {
    pub exact_duplicates: Vec<Duplicate>,
    pub near_duplicates: Vec<NearDuplicate>,
}

pub fn find_duplicates(files: &[&Path]) -> DuplicateReport {
    let mut content_map: HashMap<String, Vec<String>> = HashMap::new();
    let mut shard_size_map: HashMap<(u8, usize), Vec<String>> = HashMap::new();
    
    // Find exact duplicates
    for file in files {
        if let Ok(content) = std::fs::read(file) {
            let mut hasher = Sha256::new();
            hasher.update(&content);
            let hash = format!("{:x}", hasher.finalize());
            
            content_map.entry(hash)
                .or_insert_with(Vec::new)
                .push(file.to_string_lossy().to_string());
            
            // For near-duplicates: group by shard and size
            let shard = (content[0] as u64 % 71) as u8;
            let lines = content.iter().filter(|&&b| b == b'\n').count();
            
            shard_size_map.entry((shard, lines))
                .or_insert_with(Vec::new)
                .push(file.to_string_lossy().to_string());
        }
    }
    
    // Exact duplicates
    let exact_duplicates: Vec<Duplicate> = content_map.iter()
        .filter(|(_, files)| files.len() > 1)
        .map(|(hash, files)| {
            let lines = if let Ok(content) = std::fs::read(files[0].as_str()) {
                content.iter().filter(|&&b| b == b'\n').count()
            } else { 0 };
            
            Duplicate {
                files: files.clone(),
                hash: hash.clone(),
                lines,
            }
        })
        .collect();
    
    // Near duplicates
    let near_duplicates: Vec<NearDuplicate> = shard_size_map.iter()
        .filter(|(_, files)| files.len() > 1)
        .map(|((shard, lines), files)| NearDuplicate {
            files: files.clone(),
            shard: *shard,
            lines: *lines,
            similarity: 0.9, // Same shard + same size = high similarity
        })
        .collect();
    
    DuplicateReport {
        exact_duplicates,
        near_duplicates,
    }
}
