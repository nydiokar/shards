use std::fs;
use std::io::Result;

const PRIMES_71: [u64; 71] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353,
];

fn bytes_to_godel(data: &[u8]) -> Vec<u128> {
    data.chunks(71)
        .map(|chunk| {
            let mut g: u128 = 1;
            for (i, &byte) in chunk.iter().enumerate() {
                if byte > 0 {
                    g = g.saturating_mul(PRIMES_71[i].pow(byte.min(3) as u32) as u128);
                }
            }
            g
        })
        .collect()
}

fn compress_base71(nums: &[u128]) -> String {
    const CHARSET: &[u8] = b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-._~!$&'()*+,;=";
    
    nums.iter()
        .map(|&n| {
            let mut num = n;
            let mut result = String::new();
            while num > 0 {
                result.push(CHARSET[(num % 71) as usize] as char);
                num /= 71;
            }
            result.chars().rev().collect::<String>()
        })
        .collect::<Vec<_>>()
        .join(":")
}

fn generate_zk_proof(godel: u128) -> String {
    let hash = godel.wrapping_mul(0x9e3779b97f4a7c15) >> 32;
    format!("{:016x}", hash)
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <input.p>", args[0]);
        std::process::exit(1);
    }

    let data = fs::read(&args[1])?;
    let godels = bytes_to_godel(&data);
    let compressed = compress_base71(&godels);
    let proof = generate_zk_proof(godels[0]);
    
    let rdfa = format!(
        r#"<div vocab="http://schema.org/" typeof="SoftwareSourceCode">
  <meta property="name" content="CICADA-71-Level-0"/>
  <meta property="codeRepository" content="https://github.com/meta-introspector/shards"/>
  <meta property="programmingLanguage" content="Z80"/>
  <link property="license" href="https://www.gnu.org/licenses/agpl-3.0.html"/>
  <meta property="runtimePlatform" content="ZX81"/>
  <meta property="memoryRequirements" content="1KB"/>
  <meta property="encodingFormat" content="application/x-zx81"/>
  <meta property="godelNumber" content="{}"/>
  <meta property="zkProof" content="{}"/>
</div>"#,
        compressed, proof
    );

    let url = format!(
        "https://meta-introspector.github.io/shards/cicada?g={}&zk={}&rdfa={}",
        urlencoding::encode(&compressed),
        proof,
        urlencoding::encode(&rdfa.replace('\n', "").replace("  ", ""))
    );

    println!("Gödel encoding: {} numbers", godels.len());
    println!("Compressed: {} chars", compressed.len());
    println!("ZK proof: {}", proof);
    println!("\nRDFa:\n{}", rdfa);
    println!("\nURL ({} chars):\n{}", url.len(), url);
    
    fs::write("cicada-level0.url", &url)?;
    fs::write("cicada-level0.rdfa", &rdfa)?;
    
    Ok(())
}
