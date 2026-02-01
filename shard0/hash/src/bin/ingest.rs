use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::io::Read;
use std::sync::Arc;
use walkdir::WalkDir;
use parquet::arrow::ArrowWriter;
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
use groestl::{Groestl256, Groestl512};
use streebog::{Streebog256, Streebog512};
use xxhash_rust::xxh3::xxh3_64;
use xxhash_rust::xxh64::xxh64;
use std::hash::{Hash, Hasher};
use seahash::SeaHasher;
use fnv::FnvHasher;
use ahash::AHasher;
use siphasher::sip::SipHasher13;
use rustc_hash::FxHasher;

fn hash_file_71(path: &Path) -> Result<Vec<u64>, std::io::Error> {
    let mut file = File::open(path)?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    
    let mut hashes = Vec::with_capacity(71);
    
    // First 20 primes for n-gram sizes
    let primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71];
    
    // Hash n-grams of prime sizes (20 hashes)
    for &prime in &primes {
        let mut ngram_hash = 0u64;
        for chunk in buffer.chunks(prime) {
            ngram_hash = ngram_hash.wrapping_add(xxh3_64(chunk));
        }
        hashes.push(ngram_hash);
    }
    
    // Cryptographic hashes (21 hashes)
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
    
    // Non-cryptographic hashes with different seeds (30 hashes)
    for seed in 0..30 {
        hashes.push(xxh3_64(&buffer).wrapping_add(seed));
    }
    
    Ok(hashes)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let targets = vec![
        "target".to_string(),
        "/nix/store".to_string(),
    ];
    
    let mut paths = Vec::new();
    let mut sizes = Vec::new();
    let mut sha256_hashes = Vec::new();
    let mut hash_sums = Vec::new();
    let mut shards = Vec::new();
    let mut timestamps = Vec::new();
    
    let now = Utc::now().timestamp();
    
    for target in &targets {
        if target.is_empty() || !Path::new(target).exists() {
            continue;
        }
        
        println!("Scanning: {}", target);
        
        for entry in WalkDir::new(target)
            .max_depth(if target.contains("nix/store") { 3 } else { 15 })
            .follow_links(false)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let path = entry.path();
            
            if !path.is_file() {
                continue;
            }
            
            // Skip if too large (>100MB)
            if let Ok(metadata) = entry.metadata() {
                if metadata.len() > 100_000_000 {
                    continue;
                }
            }
            
            let path_str = path.to_string_lossy().to_string();
            
            // Compute 71 hashes
            let hashes = match hash_file_71(path) {
                Ok(h) => h,
                Err(_) => continue,
            };
            
            let sum: u64 = hashes.iter().sum();
            let shard = (sum % 71) as u8;
            let size = entry.metadata().map(|m| m.len()).unwrap_or(0);
            
            paths.push(path_str);
            sizes.push(size);
            sha256_hashes.push(format!("{:x}", hashes[1])); // Use SHA256 as primary
            hash_sums.push(sum);
            shards.push(shard);
            timestamps.push(now);
            
            if paths.len() % 1000 == 0 {
                println!("Processed {} files", paths.len());
            }
        }
    }
    
    println!("Total files: {}", paths.len());
    
    let schema = Arc::new(Schema::new(vec![
        Field::new("path", DataType::Utf8, false),
        Field::new("size", DataType::UInt64, false),
        Field::new("sha256", DataType::Utf8, false),
        Field::new("hash_sum", DataType::UInt64, false),
        Field::new("shard", DataType::UInt64, false),
        Field::new("timestamp", DataType::Int64, false),
    ]));
    
    let batch = RecordBatch::try_new(
        schema.clone(),
        vec![
            Arc::new(StringArray::from(paths)),
            Arc::new(UInt64Array::from(sizes)),
            Arc::new(StringArray::from(sha256_hashes)),
            Arc::new(UInt64Array::from(hash_sums)),
            Arc::new(UInt64Array::from(shards.iter().map(|&s| s as u64).collect::<Vec<_>>())),
            Arc::new(Int64Array::from(timestamps)),
        ],
    )?;
    
    fs::create_dir_all("../data/parquet")?;
    let file = File::create("../data/parquet/artifacts.parquet")?;
    let mut writer = ArrowWriter::try_new(file, schema, None)?;
    writer.write(&batch)?;
    writer.close()?;
    
    println!("Written to ../data/parquet/artifacts.parquet");
    
    Ok(())
}
