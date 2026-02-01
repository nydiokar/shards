// Paxos Acceptor Node for Leaderboard Consensus
// Runs on each of 23 nodes

use serde::{Deserialize, Serialize};
use std::sync::{Arc, Mutex};
use warp::Filter;
use anyhow::Result;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaxosProposal {
    proposal_number: u64,
    proposer_id: u8,
    value: ProposalValue,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProposalValue {
    leaderboard: Vec<MarketQuote>,
    hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct MarketQuote {
    framework: String,
    score: u64,
    price_per_point: f64,
    bid: f64,
    ask: f64,
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

#[derive(Debug, Clone)]
struct AcceptorState {
    node_id: u8,
    promised_proposal: u64,
    accepted_proposal: u64,
    accepted_value: Option<ProposalValue>,
}

impl AcceptorState {
    fn new(node_id: u8) -> Self {
        Self {
            node_id,
            promised_proposal: 0,
            accepted_proposal: 0,
            accepted_value: None,
        }
    }
    
    fn handle_prepare(&mut self, proposal: PaxosProposal) -> Option<PaxosPromise> {
        if proposal.proposal_number > self.promised_proposal {
            self.promised_proposal = proposal.proposal_number;
            
            println!("✅ Node {} promised proposal {}", 
                     self.node_id, proposal.proposal_number);
            
            Some(PaxosPromise {
                acceptor_id: self.node_id,
                proposal_number: proposal.proposal_number,
                accepted_value: self.accepted_value.clone(),
            })
        } else {
            println!("❌ Node {} rejected proposal {} (promised: {})", 
                     self.node_id, proposal.proposal_number, self.promised_proposal);
            None
        }
    }
    
    fn handle_accept(&mut self, proposal: PaxosProposal) -> Option<PaxosAccept> {
        if proposal.proposal_number >= self.promised_proposal {
            self.accepted_proposal = proposal.proposal_number;
            self.accepted_value = Some(proposal.value.clone());
            
            println!("✅ Node {} accepted proposal {}", 
                     self.node_id, proposal.proposal_number);
            
            Some(PaxosAccept {
                acceptor_id: self.node_id,
                proposal_number: proposal.proposal_number,
                value: proposal.value,
            })
        } else {
            println!("❌ Node {} rejected accept {} (promised: {})", 
                     self.node_id, proposal.proposal_number, self.promised_proposal);
            None
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let node_id: u8 = std::env::var("NODE_ID")
        .unwrap_or_else(|_| "0".to_string())
        .parse()
        .unwrap_or(0);
    
    println!("🔷 Paxos Acceptor Node {}", node_id);
    println!("   Listening on port 7100");
    println!("   Part of 23-node consensus\n");
    
    let state = Arc::new(Mutex::new(AcceptorState::new(node_id)));
    
    // Prepare endpoint
    let state_prepare = state.clone();
    let prepare = warp::path!("paxos" / "prepare")
        .and(warp::post())
        .and(warp::body::json())
        .map(move |proposal: PaxosProposal| {
            let mut state = state_prepare.lock().unwrap();
            match state.handle_prepare(proposal) {
                Some(promise) => warp::reply::json(&promise),
                None => warp::reply::json(&serde_json::json!({"error": "rejected"})),
            }
        });
    
    // Accept endpoint
    let state_accept = state.clone();
    let accept = warp::path!("paxos" / "accept")
        .and(warp::post())
        .and(warp::body::json())
        .map(move |proposal: PaxosProposal| {
            let mut state = state_accept.lock().unwrap();
            match state.handle_accept(proposal) {
                Some(accept) => warp::reply::json(&accept),
                None => warp::reply::json(&serde_json::json!({"error": "rejected"})),
            }
        });
    
    // Status endpoint
    let state_status = state.clone();
    let status = warp::path!("paxos" / "status")
        .and(warp::get())
        .map(move || {
            let state = state_status.lock().unwrap();
            warp::reply::json(&serde_json::json!({
                "node_id": state.node_id,
                "promised_proposal": state.promised_proposal,
                "accepted_proposal": state.accepted_proposal,
                "has_value": state.accepted_value.is_some(),
            }))
        });
    
    let routes = prepare.or(accept).or(status);
    
    warp::serve(routes)
        .run(([0, 0, 0, 0], 7100))
        .await;
    
    Ok(())
}
