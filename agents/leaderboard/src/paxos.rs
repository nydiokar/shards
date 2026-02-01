// Paxos Leaderboard Market Quote System
// Leaderboard updates are consensus proposals across 23 nodes

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
use anyhow::Result;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct MarketQuote {
    framework: String,
    score: u64,
    price_per_point: f64,      // Market price in Metameme Coin
    bid: f64,                   // Buy orders
    ask: f64,                   // Sell orders
    volume_24h: u64,
    timestamp: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaxosProposal {
    proposal_number: u64,
    proposer_id: u8,            // Node 0-22
    proposal_type: ProposalType,
    value: ProposalValue,
    timestamp: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum ProposalType {
    LeaderboardUpdate,
    MarketQuote,
    ScoreVerification,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProposalValue {
    leaderboard: Vec<MarketQuote>,
    hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaxosPromise {
    acceptor_id: u8,
    proposal_number: u64,
    accepted_value: Option<ProposalValue>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaxosAccept {
    acceptor_id: u8,
    proposal_number: u64,
    value: ProposalValue,
}

struct PaxosLeaderboard {
    node_id: u8,
    current_proposal: u64,
    promised_proposal: u64,
    accepted_proposal: u64,
    accepted_value: Option<ProposalValue>,
    quorum_size: u8,            // 12 of 23 nodes
}

impl PaxosLeaderboard {
    fn new(node_id: u8) -> Self {
        Self {
            node_id,
            current_proposal: 0,
            promised_proposal: 0,
            accepted_proposal: 0,
            accepted_value: None,
            quorum_size: 12,
        }
    }
    
    // Phase 1a: Prepare
    fn prepare(&mut self, quotes: Vec<MarketQuote>) -> PaxosProposal {
        self.current_proposal += 1;
        
        let value = ProposalValue {
            leaderboard: quotes.clone(),
            hash: Self::hash_quotes(&quotes),
        };
        
        PaxosProposal {
            proposal_number: self.current_proposal,
            proposer_id: self.node_id,
            proposal_type: ProposalType::LeaderboardUpdate,
            value,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        }
    }
    
    // Phase 1b: Promise
    fn promise(&mut self, proposal: &PaxosProposal) -> Option<PaxosPromise> {
        if proposal.proposal_number > self.promised_proposal {
            self.promised_proposal = proposal.proposal_number;
            
            Some(PaxosPromise {
                acceptor_id: self.node_id,
                proposal_number: proposal.proposal_number,
                accepted_value: self.accepted_value.clone(),
            })
        } else {
            None
        }
    }
    
    // Phase 2a: Accept Request
    fn accept_request(&self, proposal: &PaxosProposal) -> PaxosAccept {
        PaxosAccept {
            acceptor_id: self.node_id,
            proposal_number: proposal.proposal_number,
            value: proposal.value.clone(),
        }
    }
    
    // Phase 2b: Accept
    fn accept(&mut self, accept: &PaxosAccept) -> bool {
        if accept.proposal_number >= self.promised_proposal {
            self.accepted_proposal = accept.proposal_number;
            self.accepted_value = Some(accept.value.clone());
            true
        } else {
            false
        }
    }
    
    fn hash_quotes(quotes: &[MarketQuote]) -> String {
        use sha2::{Sha256, Digest};
        let json = serde_json::to_string(quotes).unwrap();
        let mut hasher = Sha256::new();
        hasher.update(json.as_bytes());
        format!("{:x}", hasher.finalize())
    }
}

// Market maker for Metameme Coin
struct MetamemeMarket {
    quotes: HashMap<String, MarketQuote>,
    base_price: f64,            // 1 point = 0.001 Metameme Coin
}

impl MetamemeMarket {
    fn new() -> Self {
        Self {
            quotes: HashMap::new(),
            base_price: 0.001,
        }
    }
    
    fn update_quote(&mut self, framework: String, score: u64) {
        let price = self.base_price * (score as f64);
        let spread = price * 0.01; // 1% spread
        
        let quote = MarketQuote {
            framework: framework.clone(),
            score,
            price_per_point: self.base_price,
            bid: price - spread,
            ask: price + spread,
            volume_24h: 0,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };
        
        self.quotes.insert(framework, quote);
    }
    
    fn get_quotes(&self) -> Vec<MarketQuote> {
        self.quotes.values().cloned().collect()
    }
}

// Distributed leaderboard with Paxos consensus
async fn propose_leaderboard_update(
    node_id: u8,
    quotes: Vec<MarketQuote>,
    nodes: &[String],
) -> Result<bool> {
    let mut paxos = PaxosLeaderboard::new(node_id);
    
    // Phase 1: Prepare
    let proposal = paxos.prepare(quotes);
    println!("📤 Node {} proposing: {}", node_id, proposal.proposal_number);
    
    let mut promises = Vec::new();
    
    // Send prepare to all acceptors
    for (i, node_addr) in nodes.iter().enumerate() {
        if let Ok(promise) = send_prepare(node_addr, &proposal).await {
            promises.push(promise);
            println!("   ✅ Promise from node {}", i);
        }
    }
    
    // Check quorum
    if promises.len() < paxos.quorum_size as usize {
        println!("   ❌ No quorum: {}/{}", promises.len(), paxos.quorum_size);
        return Ok(false);
    }
    
    println!("   ✅ Quorum achieved: {}/{}", promises.len(), paxos.quorum_size);
    
    // Phase 2: Accept
    let mut accepts = Vec::new();
    
    for node_addr in nodes {
        if let Ok(accept) = send_accept(node_addr, &proposal).await {
            accepts.push(accept);
        }
    }
    
    if accepts.len() >= paxos.quorum_size as usize {
        println!("   ✅ Consensus achieved!");
        return Ok(true);
    }
    
    Ok(false)
}

async fn send_prepare(node: &str, proposal: &PaxosProposal) -> Result<PaxosPromise> {
    let client = reqwest::Client::new();
    let response = client
        .post(format!("{}/paxos/prepare", node))
        .json(proposal)
        .send()
        .await?;
    
    Ok(response.json().await?)
}

async fn send_accept(node: &str, proposal: &PaxosProposal) -> Result<PaxosAccept> {
    let client = reqwest::Client::new();
    let response = client
        .post(format!("{}/paxos/accept", node))
        .json(proposal)
        .send()
        .await?;
    
    Ok(response.json().await?)
}

fn generate_market_leaderboard(quotes: &[MarketQuote]) -> String {
    let mut sorted = quotes.to_vec();
    sorted.sort_by(|a, b| b.score.cmp(&a.score));
    
    let mut md = String::from("# 71-Shard Market Leaderboard\n\n");
    md.push_str("**Consensus**: Paxos (23 nodes, quorum 12)\n");
    md.push_str("**Currency**: Metameme Coin (Gödel-encoded)\n\n");
    md.push_str("## Market Quotes\n\n");
    md.push_str("| Rank | Framework | Score | Price | Bid | Ask | Volume 24h |\n");
    md.push_str("|------|-----------|-------|-------|-----|-----|------------|\n");
    
    for (rank, quote) in sorted.iter().enumerate() {
        md.push_str(&format!(
            "| {} | {} | {:,} | {:.6} MMC | {:.6} | {:.6} | {:,} |\n",
            rank + 1,
            quote.framework,
            quote.score,
            quote.price_per_point * quote.score as f64,
            quote.bid,
            quote.ask,
            quote.volume_24h
        ));
    }
    
    md.push_str("\n## Trading\n\n");
    md.push_str("```bash\n");
    md.push_str("# Buy agent performance tokens\n");
    md.push_str("cicada71 buy --framework claude --amount 1000\n\n");
    md.push_str("# Sell tokens\n");
    md.push_str("cicada71 sell --framework claude --amount 500\n\n");
    md.push_str("# Check portfolio\n");
    md.push_str("cicada71 portfolio\n");
    md.push_str("```\n");
    
    md
}

#[tokio::main]
async fn main() -> Result<()> {
    println!("📊 Paxos Market Leaderboard");
    println!("============================\n");
    
    // Load evaluation results
    let results = load_results("results")?;
    let scores = calculate_scores(&results);
    
    // Create market quotes
    let mut market = MetamemeMarket::new();
    for (framework, score_data) in scores {
        market.update_quote(framework, score_data.total_points);
    }
    
    let quotes = market.get_quotes();
    
    // Propose to Paxos network
    let nodes: Vec<String> = (0..23)
        .map(|i| format!("http://node{}.cicada71.net:7100", i))
        .collect();
    
    println!("📤 Proposing leaderboard update to 23 nodes...\n");
    
    let consensus = propose_leaderboard_update(0, quotes.clone(), &nodes).await?;
    
    if consensus {
        println!("\n✅ Consensus achieved! Leaderboard is canonical.\n");
        
        let leaderboard = generate_market_leaderboard(&quotes);
        std::fs::write("LEADERBOARD.md", &leaderboard)?;
        
        println!("{}", leaderboard);
    } else {
        println!("\n❌ Consensus failed. Retrying...");
    }
    
    Ok(())
}

// Stub functions (use existing implementations)
fn load_results(_dir: &str) -> Result<Vec<EvalResult>> {
    Ok(vec![])
}

fn calculate_scores(_results: &[EvalResult]) -> HashMap<String, FrameworkScore> {
    HashMap::new()
}

#[derive(Debug)]
struct EvalResult;

#[derive(Debug)]
struct FrameworkScore {
    total_points: u64,
}
