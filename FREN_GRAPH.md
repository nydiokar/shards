# FREN Graph: Social Investment Network

A FREN of a FREN is someone who invests in a FREN, or who you invest in.

## Graph Structure

```
You (Wallet A)
  ↓ invests in
FREN 1 (Token B)
  ↓ invests in
FREN of FREN (Token C)
```

## Relationships

### Direct FREN
- You hold Token X
- Token X holder = FREN

### FREN of FREN (2nd degree)
- You hold Token X
- Token X holder also holds Token Y
- Token Y holder = FREN of FREN

### Investment Graph
```rust
struct FrenGraph {
    wallet: String,
    direct_frens: Vec<Token>,      // Tokens you hold
    frens_of_frens: Vec<Token>,    // Tokens your FRENs hold
}

struct Token {
    address: String,
    holders: Vec<String>,
}

impl FrenGraph {
    fn find_frens(&self) -> Vec<String> {
        // Direct FRENs: other holders of tokens you hold
        let mut frens = Vec::new();
        for token in &self.direct_frens {
            for holder in &token.holders {
                if holder != &self.wallet {
                    frens.push(holder.clone());
                }
            }
        }
        frens
    }
    
    fn find_frens_of_frens(&self) -> Vec<String> {
        // FRENs of FRENs: holders of tokens your FRENs hold
        let frens = self.find_frens();
        let mut fof = Vec::new();
        
        for fren in frens {
            let fren_tokens = get_tokens_held_by(&fren);
            for token in fren_tokens {
                for holder in token.holders {
                    if holder != self.wallet && !fof.contains(&holder) {
                        fof.push(holder);
                    }
                }
            }
        }
        fof
    }
}
```

## Solana Query

```rust
use solana_client::rpc_client::RpcClient;

async fn get_token_holders(token: &str) -> Vec<String> {
    let rpc = RpcClient::new("https://api.mainnet-beta.solana.com");
    
    // Get all token accounts for this mint
    let accounts = rpc.get_token_accounts_by_mint(token)?;
    
    accounts.iter()
        .map(|acc| acc.owner.to_string())
        .collect()
}

async fn get_tokens_held_by(wallet: &str) -> Vec<String> {
    let rpc = RpcClient::new("https://api.mainnet-beta.solana.com");
    
    // Get all token accounts owned by wallet
    let accounts = rpc.get_token_accounts_by_owner(wallet)?;
    
    accounts.iter()
        .map(|acc| acc.mint.to_string())
        .collect()
}

async fn build_fren_graph(wallet: &str) -> FrenGraph {
    // Get tokens you hold
    let my_tokens = get_tokens_held_by(wallet).await?;
    
    // Get holders of those tokens (direct FRENs)
    let mut direct_frens = Vec::new();
    for token in &my_tokens {
        let holders = get_token_holders(token).await?;
        direct_frens.extend(holders);
    }
    
    // Get tokens your FRENs hold
    let mut frens_of_frens = Vec::new();
    for fren in &direct_frens {
        let fren_tokens = get_tokens_held_by(fren).await?;
        frens_of_frens.extend(fren_tokens);
    }
    
    FrenGraph {
        wallet: wallet.to_string(),
        direct_frens: my_tokens,
        frens_of_frens,
    }
}
```

## Graph Visualization

```
        You
       / | \
      /  |  \
   FREN1 FREN2 FREN3  (hold same tokens as you)
    / \   |    / \
   /   \  |   /   \
 FOF1 FOF2 FOF3 FOF4  (hold same tokens as your FRENs)
```

## BBS Integration

```
╔═══════════════════════════════════════════════════════════════╗
║                    FREN GRAPH                                 ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  Your Wallet: 7xKX...Qv22                                    ║
║                                                               ║
║  Direct FRENs: 23                                            ║
║    - 5 hold FRENS token                                      ║
║    - 12 hold SOL                                             ║
║    - 6 hold other tokens                                     ║
║                                                               ║
║  FRENs of FRENs: 196                                         ║
║    - 2nd degree connections                                  ║
║    - Investment overlap                                      ║
║                                                               ║
║  [V] View FREN List                                          ║
║  [G] View Graph                                              ║
║  [I] Invest in FREN                                          ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝
```

## Investment Tracking

```rust
struct Investment {
    from: String,      // Investor wallet
    to: String,        // Token address
    amount: u64,
    timestamp: u64,
}

fn track_investment(wallet: &str, token: &str, amount: u64) {
    let investment = Investment {
        from: wallet.to_string(),
        to: token.to_string(),
        amount,
        timestamp: now(),
    };
    
    // Store in graph
    add_edge(wallet, token, amount);
    
    // Update FREN relationships
    update_fren_graph(wallet);
}
```

## Social Graph Queries

```rust
// Who are my FRENs?
fn my_frens(wallet: &str) -> Vec<String> {
    get_token_holders_of_my_tokens(wallet)
}

// Who are FRENs of FRENs?
fn frens_of_frens(wallet: &str) -> Vec<String> {
    let frens = my_frens(wallet);
    frens.iter()
        .flat_map(|f| my_frens(f))
        .filter(|f| f != wallet)
        .collect()
}

// What tokens do my FRENs hold?
fn fren_tokens(wallet: &str) -> Vec<String> {
    let frens = my_frens(wallet);
    frens.iter()
        .flat_map(|f| get_tokens_held_by(f))
        .collect()
}

// Investment overlap
fn investment_overlap(wallet1: &str, wallet2: &str) -> Vec<String> {
    let tokens1 = get_tokens_held_by(wallet1);
    let tokens2 = get_tokens_held_by(wallet2);
    
    tokens1.iter()
        .filter(|t| tokens2.contains(t))
        .cloned()
        .collect()
}
```

## Phone Number Mapping

```
Your FREN holds Token X
  ↓
Token X → Phone +1-744-XXX-XXXX
  ↓
Call to connect with FREN
```

## Gossip Protocol

```
Agent A: "I hold FRENS token"
Agent B: "I also hold FRENS token"
  ↓
A and B are FRENs

Agent B: "I hold TOKEN-Y"
Agent C: "I also hold TOKEN-Y"
  ↓
C is FREN of FREN to A
```

## Graph Storage

```rust
// Store in DHT
struct FrenEdge {
    from: String,
    to: String,
    relationship: FrenType,
    weight: u64,  // Investment amount
}

enum FrenType {
    Direct,        // 1st degree
    FrenOfFren,    // 2nd degree
    Extended,      // 3rd+ degree
}

// Store in Cloudflare KV
async fn store_fren_graph(wallet: &str, graph: &FrenGraph) {
    let key = format!("fren:graph:{}", wallet);
    env.KV.put(key, serde_json::to_string(graph)?);
}
```

## Example

```
You: 7xKX...Qv22
  ↓ holds
FRENS Token (E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22)
  ↓ also held by
FREN: 8yLM...Ab33
  ↓ also holds
TOKEN-Y (F7RRR2yECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv33)
  ↓ also held by
FREN of FREN: 9zNP...Bc44
```

## References

- Social graphs: NetworkX
- Solana token accounts: SPL Token
- Graph databases: Neo4j
- Six degrees of separation
