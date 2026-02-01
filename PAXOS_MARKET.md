# Paxos Market Leaderboard

## Overview

The leaderboard is now a **market quote system** where agent performance scores are traded as Metameme Coins through **Paxos consensus** across 23 nodes.

## Architecture

```
Agent Scores → Market Quotes → Paxos Proposal → 23 Nodes → Consensus → Canonical Leaderboard
```

## Components

### 1. Market Maker
- Converts scores to Metameme Coin prices
- Base rate: 1 point = 0.001 MMC
- 1% bid-ask spread
- 24h volume tracking

### 2. Paxos Consensus (23 Nodes)
- **Quorum**: 12 of 23 nodes
- **Byzantine tolerance**: 7 faulty nodes
- **Proposal**: Leaderboard updates
- **Value**: Market quotes + hash

### 3. Trading System
- Buy/sell agent performance tokens
- Portfolio management
- Real-time quotes

## Paxos Protocol

### Phase 1: Prepare
```
Proposer → Prepare(n) → All Acceptors
Acceptors → Promise(n, accepted_value) → Proposer
```

### Phase 2: Accept
```
Proposer → Accept(n, value) → All Acceptors
Acceptors → Accepted(n, value) → Proposer
```

### Consensus
- If ≥12 acceptors agree → Consensus achieved
- Leaderboard becomes canonical
- Market quotes are official

## Market Quote Format

```json
{
  "framework": "claude",
  "score": 50000,
  "price_per_point": 0.001,
  "bid": 49.50,
  "ask": 50.50,
  "volume_24h": 1000,
  "timestamp": 1738425600
}
```

## Leaderboard Output

```markdown
| Rank | Framework | Score | Price | Bid | Ask | Volume 24h |
|------|-----------|-------|-------|-----|-----|------------|
| 1    | Claude    | 50,000| 50 MMC| 49.5| 50.5| 1,000      |
| 2    | OpenAI    | 45,000| 45 MMC| 44.5| 45.5| 800        |
```

## Deployment

```bash
# Deploy 23 Paxos nodes
./deploy_paxos.sh

# Run market leaderboard with consensus
cd agents/leaderboard
cargo run --release --bin paxos-market

# Check node status
curl http://localhost:7100/paxos/status
```

## Trading

```bash
# Buy Claude tokens
cicada71 buy --framework claude --amount 1000

# Sell OpenAI tokens
cicada71 sell --framework openai --amount 500

# Check portfolio
cicada71 portfolio

# View market depth
cicada71 market --framework claude
```

## Node Configuration

Each of 23 nodes runs:
- **Port**: 7100
- **Endpoints**:
  - `POST /paxos/prepare` - Phase 1
  - `POST /paxos/accept` - Phase 2
  - `GET /paxos/status` - Node state

## Consensus Properties

- **Safety**: Only one value decided per proposal
- **Liveness**: Eventually decides if majority available
- **Byzantine Fault Tolerance**: Tolerates 7 faulty nodes
- **Finality**: Once consensus, immutable

## Metameme Coin

Gödel-encoded cryptocurrency:
```
Price = 2^a0 × 3^a1 × 5^a2 × ... × 353^a70
```

Where `a[i]` = score on shard `i`

## Integration with CICADA-71

- Level 8: Achieve Paxos consensus
- Level 10: ZK proof of market participation
- Final: Trade tokens for Monster Group access

## Monitoring

```bash
# Watch consensus
watch -n 1 'curl -s http://localhost:7100/paxos/status'

# View all nodes
for i in {0..22}; do
  curl -s http://localhost:$((7100+i))/paxos/status
done

# Check leaderboard
cat LEADERBOARD.md
```

## Example Session

```bash
# 1. Deploy nodes
./deploy_paxos.sh

# 2. Run evaluations
pipelight run eval-all-agents

# 3. Propose leaderboard update
cargo run --release --bin paxos-market

# Output:
# 📤 Node 0 proposing: 1
#    ✅ Promise from node 0
#    ✅ Promise from node 1
#    ...
#    ✅ Promise from node 12
#    ✅ Quorum achieved: 12/12
#    ✅ Consensus achieved!
```

## Security

- **Cryptographic hashes**: SHA256 of all quotes
- **Proposal numbers**: Monotonically increasing
- **Byzantine tolerance**: 7 nodes can be malicious
- **Immutability**: Consensus is final

## Future Enhancements

- [ ] Multi-Paxos for continuous updates
- [ ] Raft for leader election
- [ ] Cross-chain atomic swaps
- [ ] Decentralized exchange (DEX)
- [ ] Liquidity pools
- [ ] Staking rewards
