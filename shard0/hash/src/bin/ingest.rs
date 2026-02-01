use std::fs::{self, File};
use std::path::Path;
use std::io::Read;
use std::sync::Arc;
use walkdir::WalkDir;
use parquet::arrow::ArrowWriter;
use parquet::file::properties::WriterProperties;
use parquet::basic::Compression;
use arrow::array::{StringArray, UInt64Array, Int64Array};
use arrow::record_batch::RecordBatch;
use arrow::datatypes::{Schema, Field, DataType};
use chrono::Utc;
use sha2::{Sha224, Sha256, Sha384, Sha512, Digest};
use blake2::{Blake2b512, Blake2s256};
use blake3::Hasher as Blake3Hasher;
use sha1::Sha1;
use sha3::{Sha3_224, Sha3_256, Sha3_384, Sha3_512, Keccak256};
use md5::Md5;
use ripemd::{Ripemd160, Ripemd256};
use whirlpool::Whirlpool;

mod resource;
use resource::ShardResource;
use groestl::{Groestl256, Groestl512};
use streebog::{Streebog256, Streebog512};
use xxhash_rust::xxh3::xxh3_64;
use rayon::prelude::*;
use parking_lot::Mutex;
use std::collections::HashMap;

struct FileRecord {
    path: String,
    size: u64,
    sha256: String,
    hash_sum: u64,
    shard: u8,
    timestamp: i64,
}

fn hash_file_71(path: &Path) -> Result<Vec<u64>, std::io::Error> {
    let mut file = File::open(path)?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    
    let mut hashes = Vec::with_capacity(71);
    let primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71];
    
    for &prime in &primes {
        let mut ngram_hash = 0u64;
        for chunk in buffer.chunks(prime) {
            ngram_hash = ngram_hash.wrapping_add(xxh3_64(chunk));
        }
        hashes.push(ngram_hash);
    }
    
    hashes.push(u64::from_be_bytes(Sha224::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Sha256::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Sha384::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Sha512::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Blake2b512::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Blake2s256::digest(&buffer)[..8].try_into().unwrap()));
    
    let mut blake3 = Blake3Hasher::new();
    blake3.update(&buffer);
    hashes.push(u64::from_be_bytes(blake3.finalize().as_bytes()[..8].try_into().unwrap()));
    
    hashes.push(u64::from_be_bytes(Sha3_224::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Sha3_256::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Sha3_384::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Sha3_512::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Keccak256::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Ripemd160::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Ripemd256::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Whirlpool::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Groestl256::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Groestl512::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Streebog256::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Streebog512::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Md5::digest(&buffer)[..8].try_into().unwrap()));
    hashes.push(u64::from_be_bytes(Sha1::digest(&buffer)[..8].try_into().unwrap()));
    
    for seed in 0..30 {
        hashes.push(xxh3_64(&buffer).wrapping_add(seed));
    }
    
    Ok(hashes)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    rayon::ThreadPoolBuilder::new().num_threads(23).build_global()?;
    
    let targets = vec!["target".to_string(), "/nix/store".to_string()];
    let now = Utc::now().timestamp();
    
    let shards: Arc<Mutex<HashMap<u8, Vec<FileRecord>>>> = Arc::new(Mutex::new(HashMap::new()));
    
    for target in &targets {
        if !Path::new(target).exists() {
            continue;
        }
        
        println!("Scanning: {}", target);
        
        let files: Vec<_> = WalkDir::new(target)
            .max_depth(if target.contains("nix/store") { 3 } else { 15 })
            .follow_links(false)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().is_file())
            .filter(|e| e.metadata().map(|m| m.len() <= 100_000_000).unwrap_or(false))
            .collect();
        
        println!("Processing {} files with 23 CPUs", files.len());
        
        files.par_iter().for_each(|entry| {
            let path = entry.path();
            let path_str = path.to_string_lossy().to_string();
            
            if let Ok(hashes) = hash_file_71(path) {
                let sum: u64 = hashes.iter().sum();
                let shard = (sum % 71) as u8;
                let size = entry.metadata().map(|m| m.len()).unwrap_or(0);
                
                let record = FileRecord {
                    path: path_str,
                    size,
                    sha256: format!("{:x}", hashes[21]),
                    hash_sum: sum,
                    shard,
                    timestamp: now,
                };
                
                let mut shards_lock = shards.lock();
                shards_lock.entry(shard).or_insert_with(Vec::new).push(record);
            }
        });
    }
    
    println!("Writing shards to parquet...");
    
    let shards_map = shards.lock();
    let schema = Arc::new(Schema::new(vec![
        Field::new("path", DataType::Utf8, false),
        Field::new("size", DataType::UInt64, false),
        Field::new("sha256", DataType::Utf8, false),
        Field::new("hash_sum", DataType::UInt64, false),
        Field::new("shard", DataType::UInt64, false),
        Field::new("timestamp", DataType::Int64, false),
    ]));
    
    let props = WriterProperties::builder()
        .set_compression(Compression::ZSTD(Default::default()))
        .build();
    
    fs::create_dir_all("../data/parquet")?;
    
    for (shard_id, records) in shards_map.iter() {
        let paths: Vec<_> = records.iter().map(|r| r.path.clone()).collect();
        let sizes: Vec<_> = records.iter().map(|r| r.size).collect();
        let sha256s: Vec<_> = records.iter().map(|r| r.sha256.clone()).collect();
        let hash_sums: Vec<_> = records.iter().map(|r| r.hash_sum).collect();
        let shards: Vec<_> = records.iter().map(|r| r.shard as u64).collect();
        let timestamps: Vec<_> = records.iter().map(|r| r.timestamp).collect();
        
        let batch = RecordBatch::try_new(
            schema.clone(),
            vec![
                Arc::new(StringArray::from(paths)),
                Arc::new(UInt64Array::from(sizes)),
                Arc::new(StringArray::from(sha256s)),
                Arc::new(UInt64Array::from(hash_sums)),
                Arc::new(UInt64Array::from(shards)),
                Arc::new(Int64Array::from(timestamps)),
            ],
        )?;
        
        let file = File::create(format!("../data/parquet/shard{:02}.parquet", shard_id))?;
        let mut writer = ArrowWriter::try_new(file, schema.clone(), Some(props.clone()))?;
        writer.write(&batch)?;
        writer.close()?;
        
        println!("Shard {}: {} files", shard_id, records.len());
    }
    
    println!("Done!");
    Ok(())
}
