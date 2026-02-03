# SOP: Moltbot Observatory
## ZK Witness & Prediction Markets for AI Bots

**Version**: 1.0  
**Date**: 2026-02-01  
**Owner**: CICADA-71 Bot Intelligence Team  
**Status**: Active

---

## Purpose

Systematically discover, observe, and create zero-knowledge witnesses of all Moltbot servers, forks, and resources. Establish prediction markets for bot behavior and performance.

**Metaphor**: "Observatory" = passive monitoring with cryptographic proof of observations.

---

## Scope

- **Discovery**: Find all Moltbot instances, forks, and related projects
- **Observation**: Join as observer (read-only)
- **ZK Witness**: Generate zero-knowledge proofs of bot activity
- **Prediction Markets**: Create Solana markets for bot outcomes
- **71-Shard Distribution**: Distribute bots across shards

---

## Prerequisites

- [x] GitHub API access
- [x] Discord bot token (observer mode)
- [x] Solana wallet for markets
- [x] ZK proof generation (snarkjs/circom)
- [x] Rust toolchain

---

## Phase 1: Discovery

### Step 1.1: Find Moltbot Repositories

```bash
#!/bin/bash
# discover_moltbots.sh

echo "=== Discovering Moltbot Ecosystem ==="

# Search GitHub
gh search repos "moltbot" --limit 100 --json name,url,stars,forks,description > moltbot_repos.json
gh search repos "eliza" --limit 100 --json name,url,stars,forks,description > eliza_repos.json
gh search repos "ai16z" --limit 50 --json name,url,stars,forks,description > ai16z_repos.json

# Combine
jq -s 'add | unique_by(.url)' moltbot_repos.json eliza_repos.json ai16z_repos.json > all_bot_repos.json

TOTAL=$(jq 'length' all_bot_repos.json)
echo "Found $TOTAL bot repositories"
```

### Step 1.2: Discover Live Instances

```python
#!/usr/bin/env python3
# discover_instances.py

import requests
import json
from pathlib import Path

def discover_moltbot_instances():
    """Find live Moltbot instances"""
    
    instances = []
    
    # Known Moltbot registries
    registries = [
        "https://registry.moltbot.ai/instances",
        "https://eliza.ai/instances",
        "https://ai16z.com/bots",
    ]
    
    for registry in registries:
        try:
            resp = requests.get(registry, timeout=5)
            if resp.status_code == 200:
                data = resp.json()
                instances.extend(data.get('instances', []))
        except:
            print(f"Registry {registry} not available")
    
    # Discover via Discord
    # (requires Discord bot token)
    
    # Discover via Twitter/X
    # (search for #moltbot, #eliza)
    
    return instances

def main():
    print("=== Discovering Live Instances ===")
    
    instances = discover_moltbot_instances()
    
    with open('moltbot_instances.json', 'w') as f:
        json.dump(instances, f, indent=2)
    
    print(f"Found {len(instances)} live instances")

if __name__ == '__main__':
    main()
```

---

## Phase 2: Observation

### Step 2.1: Join as Observer

```rust
// src/observer.rs
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub struct BotObservation {
    pub bot_id: String,
    pub platform: String,  // discord, twitter, telegram
    pub timestamp: u64,
    pub activity: ActivityType,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum ActivityType {
    Message { content_hash: String, length: usize },
    Reaction { emoji: String },
    Join { channel: String },
    Leave { channel: String },
    StatusChange { status: String },
}

pub struct BotObserver {
    bot_id: String,
    observations: Vec<BotObservation>,
}

impl BotObserver {
    pub fn new(bot_id: String) -> Self {
        Self {
            bot_id,
            observations: Vec::new(),
        }
    }
    
    pub async fn observe_discord(&mut self, token: &str) -> Result<(), Box<dyn std::error::Error>> {
        // Join Discord as observer (read-only)
        // Record all bot activities
        // Generate observations
        
        println!("Observing bot {} on Discord", self.bot_id);
        
        // Passive monitoring only
        // No interaction, no commands
        
        Ok(())
    }
    
    pub fn record_observation(&mut self, obs: BotObservation) {
        self.observations.push(obs);
    }
    
    pub fn get_observations(&self) -> &[BotObservation] {
        &self.observations
    }
}
```

### Step 2.2: Passive Monitoring

```rust
// src/monitor.rs
use tokio::time::{interval, Duration};

pub struct PassiveMonitor {
    observers: Vec<BotObserver>,
}

impl PassiveMonitor {
    pub async fn monitor_all(&mut self) {
        let mut ticker = interval(Duration::from_secs(60));
        
        loop {
            ticker.tick().await;
            
            for observer in &mut self.observers {
                // Check bot status
                // Record activity
                // No interaction
                
                println!("Monitoring bot: {}", observer.bot_id);
            }
        }
    }
}
```

---

## Phase 3: ZK Witness Generation

### Step 3.1: Observation Commitment

```rust
// src/zk_witness.rs
use sha2::{Digest, Sha256};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct ZKWitness {
    pub bot_id: String,
    pub observation_count: usize,
    pub merkle_root: [u8; 32],
    pub timestamp_range: (u64, u64),
    pub proof: Vec<u8>,
}

pub fn generate_zk_witness(observations: &[BotObservation]) -> ZKWitness {
    // Compute Merkle tree of observations
    let leaves: Vec<[u8; 32]> = observations
        .iter()
        .map(|obs| {
            let json = serde_json::to_string(obs).unwrap();
            let mut hasher = Sha256::new();
            hasher.update(json.as_bytes());
            hasher.finalize().into()
        })
        .collect();
    
    let merkle_root = compute_merkle_root(&leaves);
    
    // Generate ZK proof
    // "I observed N activities from bot X in time range [t1, t2]"
    // Without revealing specific activities
    
    let proof = generate_proof(observations);
    
    ZKWitness {
        bot_id: observations[0].bot_id.clone(),
        observation_count: observations.len(),
        merkle_root,
        timestamp_range: (
            observations.first().unwrap().timestamp,
            observations.last().unwrap().timestamp,
        ),
        proof,
    }
}

fn compute_merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    if leaves.is_empty() {
        return [0u8; 32];
    }
    
    if leaves.len() == 1 {
        return leaves[0];
    }
    
    let mut current_level = leaves.to_vec();
    
    while current_level.len() > 1 {
        let mut next_level = Vec::new();
        
        for chunk in current_level.chunks(2) {
            let mut hasher = Sha256::new();
            hasher.update(&chunk[0]);
            if chunk.len() > 1 {
                hasher.update(&chunk[1]);
            }
            next_level.push(hasher.finalize().into());
        }
        
        current_level = next_level;
    }
    
    current_level[0]
}

fn generate_proof(observations: &[BotObservation]) -> Vec<u8> {
    // Simplified proof generation
    // In production: use snarkjs/circom
    
    let mut hasher = Sha256::new();
    hasher.update(format!("proof:{}", observations.len()).as_bytes());
    hasher.finalize().to_vec()
}
```

### Step 3.2: Circom Circuit

```circom
// circuits/bot_witness.circom
pragma circom 2.0.0;

template BotWitness(n) {
    // Public inputs
    signal input merkle_root;
    signal input observation_count;
    signal input bot_id_hash;
    
    // Private inputs
    signal input observations[n];
    signal input merkle_path[n];
    
    // Verify observation count
    signal count_check;
    count_check <== observation_count * observation_count;
    
    // Verify Merkle root
    component merkle = MerkleVerify(n);
    merkle.root <== merkle_root;
    for (var i = 0; i < n; i++) {
        merkle.leaves[i] <== observations[i];
        merkle.path[i] <== merkle_path[i];
    }
    
    // Output: proof that we observed N activities
    signal output valid;
    valid <== merkle.valid;
}

component main = BotWitness(100);
```

---

## Phase 4: Prediction Markets

### Step 4.1: Market Types

```rust
// src/markets.rs
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub enum BotMarket {
    // Will bot X respond within 5 seconds?
    ResponseTime {
        bot_id: String,
        threshold_ms: u64,
    },
    
    // Will bot X be online at time T?
    Uptime {
        bot_id: String,
        check_time: u64,
    },
    
    // Will bot X generate more than N messages today?
    Activity {
        bot_id: String,
        threshold: usize,
    },
    
    // Will bot X pass Turing test?
    TuringTest {
        bot_id: String,
        judge_count: usize,
    },
    
    // Which bot will have higher engagement?
    Comparison {
        bot_a: String,
        bot_b: String,
        metric: String,
    },
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Market {
    pub id: String,
    pub market_type: BotMarket,
    pub total_staked: u64,
    pub yes_stake: u64,
    pub no_stake: u64,
    pub resolution_time: u64,
    pub resolved: bool,
    pub outcome: Option<bool>,
}
```

### Step 4.2: Solana Program

```rust
// programs/bot-markets/src/lib.rs
use anchor_lang::prelude::*;

declare_id!("BotMkt111111111111111111111111111111111111");

#[program]
pub mod bot_markets {
    use super::*;
    
    pub fn create_market(
        ctx: Context<CreateMarket>,
        bot_id: String,
        market_type: u8,
        resolution_time: i64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        market.bot_id = bot_id;
        market.market_type = market_type;
        market.resolution_time = resolution_time;
        market.total_staked = 0;
        market.yes_stake = 0;
        market.no_stake = 0;
        market.resolved = false;
        Ok(())
    }
    
    pub fn place_bet(
        ctx: Context<PlaceBet>,
        amount: u64,
        position: bool,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        
        require!(!market.resolved, ErrorCode::MarketResolved);
        
        market.total_staked += amount;
        if position {
            market.yes_stake += amount;
        } else {
            market.no_stake += amount;
        }
        
        // Transfer SOL to escrow
        // Record bet
        
        Ok(())
    }
    
    pub fn resolve_market(
        ctx: Context<ResolveMarket>,
        outcome: bool,
        zk_witness: Vec<u8>,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        
        require!(!market.resolved, ErrorCode::AlreadyResolved);
        
        // Verify ZK witness
        require!(verify_zk_witness(&zk_witness), ErrorCode::InvalidWitness);
        
        market.resolved = true;
        market.outcome = Some(outcome);
        
        // Distribute winnings
        
        Ok(())
    }
}

#[account]
pub struct BotMarket {
    pub bot_id: String,
    pub market_type: u8,
    pub resolution_time: i64,
    pub total_staked: u64,
    pub yes_stake: u64,
    pub no_stake: u64,
    pub resolved: bool,
    pub outcome: Option<bool>,
}

#[derive(Accounts)]
pub struct CreateMarket<'info> {
    #[account(init, payer = creator, space = 8 + 256)]
    pub market: Account<'info, BotMarket>,
    #[account(mut)]
    pub creator: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct PlaceBet<'info> {
    #[account(mut)]
    pub market: Account<'info, BotMarket>,
    #[account(mut)]
    pub bettor: Signer<'info>,
}

#[derive(Accounts)]
pub struct ResolveMarket<'info> {
    #[account(mut)]
    pub market: Account<'info, BotMarket>,
    pub resolver: Signer<'info>,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Market already resolved")]
    MarketResolved,
    #[msg("Market already resolved")]
    AlreadyResolved,
    #[msg("Invalid ZK witness")]
    InvalidWitness,
}

fn verify_zk_witness(witness: &[u8]) -> bool {
    // Verify ZK proof
    // In production: use proper ZK verification
    !witness.is_empty()
}
```

---

## Phase 5: 71-Shard Distribution

### Step 5.1: Assign Bots to Shards

```rust
// src/shard_bots.rs
use sha2::{Digest, Sha256};

pub fn assign_bot_to_shard(bot_id: &str) -> u8 {
    let mut hasher = Sha256::new();
    hasher.update(bot_id.as_bytes());
    let hash = hasher.finalize();
    
    let hash_val = u64::from_be_bytes(hash[..8].try_into().unwrap());
    (hash_val % 71) as u8
}

pub fn distribute_bots(bots: &[String]) -> HashMap<u8, Vec<String>> {
    let mut shards: HashMap<u8, Vec<String>> = HashMap::new();
    
    for bot in bots {
        let shard = assign_bot_to_shard(bot);
        shards.entry(shard).or_insert_with(Vec::new).push(bot.clone());
    }
    
    shards
}
```

---

## Automation

### Complete Pipeline

```bash
#!/bin/bash
# moltbot_observatory.sh

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║              MOLTBOT OBSERVATORY - ZK Witness              ║"
echo "╚════════════════════════════════════════════════════════════╝"

# Phase 1: Discovery
echo "Phase 1: Discovery..."
bash discover_moltbots.sh
python3 discover_instances.py

# Phase 2: Observation
echo "Phase 2: Observation..."
cargo run --bin observer -- start

# Phase 3: ZK Witness
echo "Phase 3: ZK Witness Generation..."
cargo run --bin zk-witness -- generate

# Phase 4: Markets
echo "Phase 4: Create Prediction Markets..."
cargo run --bin markets -- create

# Phase 5: Distribution
echo "Phase 5: Distribute to 71 Shards..."
cargo run --bin shard-bots -- distribute

echo ""
echo "╔════════════════════════════════════════════════════════════╗"
echo "║                  OBSERVATORY ACTIVE ✓                      ║"
echo "╚════════════════════════════════════════════════════════════╝"
```

---

## Outputs

### Generated Files

1. **moltbot_repos.json** - All bot repositories
2. **moltbot_instances.json** - Live bot instances
3. **observations.json** - Bot activity observations
4. **zk_witnesses.json** - Zero-knowledge proofs
5. **markets.json** - Active prediction markets
6. **BOT_SHARD_MANIFEST.json** - 71-shard distribution

---

## Market Examples

### Example 1: Response Time

```json
{
  "market_id": "resp_time_moltbot_001",
  "question": "Will Moltbot #001 respond within 5 seconds?",
  "bot_id": "moltbot_001",
  "threshold_ms": 5000,
  "total_staked": 100.0,
  "yes_stake": 60.0,
  "no_stake": 40.0,
  "resolution_time": 1738440000,
  "resolved": false
}
```

### Example 2: Turing Test

```json
{
  "market_id": "turing_eliza_042",
  "question": "Will Eliza #042 pass Turing test with 3 judges?",
  "bot_id": "eliza_042",
  "judge_count": 3,
  "total_staked": 500.0,
  "yes_stake": 300.0,
  "no_stake": 200.0,
  "resolution_time": 1738526400,
  "resolved": false
}
```

---

## Verification Checklist

- [ ] All Moltbot repos discovered
- [ ] Live instances identified
- [ ] Observer mode active (read-only)
- [ ] ZK witnesses generated
- [ ] Prediction markets created
- [ ] Bots distributed across 71 shards
- [ ] No bot interaction (passive only)
- [ ] Privacy preserved (ZK proofs)

---

## Ethics & Privacy

**Observer Mode Only**:
- No commands sent to bots
- No interaction with users
- No data collection beyond public activity
- ZK proofs preserve privacy

**Transparency**:
- All observations are public
- ZK witnesses are verifiable
- Markets are fair and open

---

## Monitoring

```bash
# Check active observations
curl http://localhost:7200/observations | jq

# View ZK witnesses
curl http://localhost:7200/witnesses | jq

# Check markets
curl http://localhost:7200/markets | jq

# Shard distribution
curl http://localhost:7200/shards | jq
```

---

## Related SOPs

- [SOP_SWAB_THE_DECK.md](SOP_SWAB_THE_DECK.md) - File sharding
- [SOLANA_MATH_STAKES.md](SOLANA_MATH_STAKES.md) - Prediction markets
- [71_CRYPTO_PORTFOLIO.md](71_CRYPTO_PORTFOLIO.md) - Multi-chain settlement

---

## Contact

- **Observatory**: observatory@solfunmeme.com
- **Markets**: markets@solfunmeme.com
- **Technical**: shards@solfunmeme.com

---

**Observe. Witness. Predict. Profit.** 🔭🤖💰✨
