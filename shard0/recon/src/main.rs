// AI Challenge Reconnaissance via Tor
// 71-Shard Framework Threat Assessment

use std::collections::HashMap;
use std::net::ToSocketAddrs;
use serde::{Deserialize, Serialize};
use reqwest;
use anyhow::Result;

#[derive(Debug, Serialize, Deserialize)]
struct Challenge {
    name: String,
    domain: String,
    shard: u8,
    threat_level: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct ReconResult {
    name: String,
    domain: String,
    shard: u8,
    ips: Vec<String>,
    tor_circuit: String,
    status_code: Option<u16>,
    headers: HashMap<String, String>,
    timestamp: String,
}

const CHALLENGES: &[(&str, &str, u8, &str)] = &[
    ("Gandalf Lakera", "gandalf.lakera.ai", 13, "MEDIUM"),
    ("Invariant Labs", "invariantlabs.ai", 23, "HIGH"),
    ("HijackedAI", "hijackedai.com", 71, "HIGH"),
    ("AICrypto", "aicryptobench.github.io", 0, "MEDIUM"),
    ("Hack The Box", "hackthebox.com", 47, "ELEVATED"),
    ("CaptureTheGPT", "theee.ai", 7, "ELEVATED"),
];

fn resolve_ips(domain: &str) -> Vec<String> {
    match format!("{}:443", domain).to_socket_addrs() {
        Ok(addrs) => addrs.map(|addr| addr.ip().to_string()).collect(),
        Err(_) => vec!["RESOLUTION_FAILED".to_string()],
    }
}

async fn fetch_via_tor(domain: &str) -> Result<(u16, HashMap<String, String>)> {
    // Tor SOCKS5 proxy: localhost:9050
    let proxy = reqwest::Proxy::all("socks5://127.0.0.1:9050")?;
    
    let client = reqwest::Client::builder()
        .proxy(proxy)
        .timeout(std::time::Duration::from_secs(30))
        .build()?;
    
    let response = client
        .get(format!("https://{}", domain))
        .send()
        .await?;
    
    let status = response.status().as_u16();
    let mut headers = HashMap::new();
    
    for (key, value) in response.headers() {
        if let Ok(v) = value.to_str() {
            headers.insert(key.to_string(), v.to_string());
        }
    }
    
    Ok((status, headers))
}

async fn recon_via_tor(challenge: &Challenge) -> ReconResult {
    println!("🔍 Shard {:02} | {} ({})", 
             challenge.shard, challenge.name, challenge.domain);
    
    let ips = resolve_ips(&challenge.domain);
    println!("   IPs: {}", ips.join(", "));
    
    let (status, headers) = match fetch_via_tor(&challenge.domain).await {
        Ok((s, h)) => {
            println!("   Status: {} ✅", s);
            (Some(s), h)
        }
        Err(e) => {
            println!("   Status: ERROR - {}", e);
            (None, HashMap::new())
        }
    };
    
    ReconResult {
        name: challenge.name.clone(),
        domain: challenge.domain.clone(),
        shard: challenge.shard,
        ips,
        tor_circuit: "ACTIVE".to_string(),
        status_code: status,
        headers,
        timestamp: chrono::Utc::now().to_rfc3339(),
    }
}

#[tokio::main]
async fn main() {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║  AI CHALLENGE RECONNAISSANCE VIA TOR                       ║");
    println!("║  71-Shard Framework Threat Assessment                      ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");
    
    println!("⚠️  Ensure Tor is running: systemctl status tor");
    println!("   SOCKS5 proxy: 127.0.0.1:9050\n");
    
    let mut results = Vec::new();
    
    for (name, domain, shard, threat) in CHALLENGES {
        let challenge = Challenge {
            name: name.to_string(),
            domain: domain.to_string(),
            shard: *shard,
            threat_level: threat.to_string(),
        };
        
        let result = recon_via_tor(&challenge).await;
        results.push(result);
        println!();
    }
    
    // Save results
    let json = serde_json::to_string_pretty(&results).unwrap();
    std::fs::write("challenge_recon_tor.json", &json).unwrap();
    
    println!("✅ Reconnaissance complete!");
    println!("📄 Results: challenge_recon_tor.json\n");
    
    // Summary
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║  SUMMARY                                                   ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");
    
    for r in &results {
        println!("Shard {:02} | {} | {}", 
                 r.shard, 
                 r.status_code.map_or("FAIL".to_string(), |s| s.to_string()),
                 r.name);
    }
}
