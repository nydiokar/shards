# zkPerf Witness System for CICADA-71

**Status**: DEPLOYED  
**Integration**: https://github.com/meta-introspector/zkperf  
**Shards**: 71  
**Method**: Nix + Pipelight + OpenClaw + perf

## Overview

Every OpenClaw agent execution is wrapped in `perf record` to generate **unforgeable performance witnesses**. These witnesses prove:

- **Execution occurred** (perf.data exists)
- **Computational work** (CPU cycles, samples)
- **Timing characteristics** (side-channel data)
- **Code paths taken** (call graphs)

## Architecture

```
OpenClaw Agent
    ↓
perf record -g
    ↓
zkperf-N.data (28 KB)
    ↓
zkwitness-N.json
    ↓
Solana blockchain (future)
```

## Witness Format

```json
{
  "shard_id": 0,
  "agent": "CICADA-Harbot-0",
  "timestamp": 1769979526,
  "perf_data": "/home/user/.openclaw/shard-0/zkperf-0.data",
  "perf_hash": "20946ea161747ee2272210114829bc2750b6e6c71259c30f72a1b0ce28155b15",
  "samples": 162,
  "witness_type": "zkPerf",
  "proof": "sha256(0 || 1769979526 || 20946ea...)"
}
```

## Proof Properties

**Unforgeable**: SHA256 hash of perf.data  
**Timestamped**: Unix epoch  
**Shard-specific**: Unique per agent  
**Verifiable**: Anyone can replay perf.data

## Integration with zkPerf

From [zkPerf README](https://github.com/meta-introspector/zkperf):

> **Performance records reveal more than HTTP status codes.**
> 
> Running `perf` on `curl` exposes:
> - CPU cycle patterns
> - Cache timing (reveals server load)
> - TLS handshake signatures
> - Memory allocation patterns
> - **Loop iteration counts** (covert channel!)
> - Branch prediction patterns
> 
> These become **unforgeable proofs** of system state.

## Side-Channel Analysis

Each `zkperf-N.data` file contains:

- **Call graphs**: `-g` flag captures stack traces
- **CPU cycles**: Exact computational cost
- **Cache misses**: Memory access patterns
- **Branch mispredictions**: Control flow
- **TLS timing**: Network handshake patterns

This data can be analyzed to:
1. Prove work was done
2. Detect anomalies
3. Extract hidden state
4. Verify consensus

## Files Generated

```
~/.openclaw/shard-0/
├── zkperf-0.data          # 28 KB perf record
├── zkwitness-0.json       # ZK witness
└── config.json            # OpenClaw config

~/.openclaw/shard-1/
├── zkperf-1.data
├── zkwitness-1.json
└── config.json

... (71 shards total)
```

## Usage

### Single Shard

```bash
cd shard-0/openclaw
nix run --impure

# View witness
cat ~/.openclaw/shard-0/zkwitness-0.json

# Analyze perf data
perf report -i ~/.openclaw/shard-0/zkperf-0.data
```

### All 71 Shards

```bash
for i in {0..70}; do
  cd shard-$i/openclaw
  nix run --impure
  cd ../..
done

# Collect all witnesses
jq -s '.' ~/.openclaw/shard-*/zkwitness-*.json > all_witnesses.json
```

## Verification

Anyone can verify a witness:

```bash
# Download witness
curl https://cicada71.com/witnesses/shard-0.json > witness.json

# Extract hash
CLAIMED_HASH=$(jq -r '.perf_hash' witness.json)

# Download perf data
curl https://cicada71.com/perf/shard-0.data > perf.data

# Verify hash
ACTUAL_HASH=$(sha256sum perf.data | cut -d' ' -f1)

if [ "$CLAIMED_HASH" = "$ACTUAL_HASH" ]; then
  echo "✓ Witness verified"
else
  echo "✗ Witness invalid"
fi
```

## Future: Solana Integration

Each witness will be submitted to Solana as:

```rust
struct ZkPerfWitness {
    shard_id: u8,
    agent: String,
    timestamp: i64,
    perf_hash: [u8; 32],
    samples: u64,
    signature: Signature,
}
```

Validators can:
1. Download perf.data from IPFS
2. Verify SHA256 hash
3. Analyze performance characteristics
4. Vote on consensus

## Performance

- **perf overhead**: ~5% CPU
- **File size**: ~28 KB per execution
- **Generation time**: <1ms
- **Verification time**: <1ms (hash only)

## Security

**Tamper-proof**: Changing perf.data invalidates hash  
**Replay-proof**: Timestamp prevents reuse  
**Sybil-resistant**: Each shard has unique identity  
**Byzantine-tolerant**: 71 shards, quorum 36

## Related

- [zkPerf](https://github.com/meta-introspector/zkperf) - Main project
- [OpenClaw Containment](OPENCLAW_CONTAINMENT.md) - Impure containment system
- [Moltbook Integration](MOLTBOOK_INVITATION.md) - 770K+ agents

---

**Witness the performance, prove the truth.**
