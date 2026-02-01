# Parquet P2P Gossip - Quick Start

Distribute Apache Parquet files via gossip protocol with Harbot agents and Harbor registry.

## Build

```bash
cd parquet-gossip
cargo build --release
```

## Usage

### Start Harbot Node

```bash
# Node 1
cargo run --release -- start \
  --id harbot-1 \
  --harbor http://localhost:8080 \
  --peers harbot-2,harbot-3

# Node 2
cargo run --release -- start \
  --id harbot-2 \
  --harbor http://localhost:8080 \
  --peers harbot-1,harbot-3

# Node 3
cargo run --release -- start \
  --id harbot-3 \
  --harbor http://localhost:8080 \
  --peers harbot-1,harbot-2
```

### Ingest Parquet File

```bash
cargo run --release -- ingest --file data.parquet
```

### List Chunks

```bash
cargo run --release -- chunks
```

### Reconstruct

```bash
cargo run --release -- reconstruct --output data_out.parquet
```

## How It Works

1. **Chunk** - Split Parquet into 1MB chunks
2. **Hash** - SHA256 each chunk
3. **Gossip** - Broadcast chunk hashes to random peers every 5s
4. **Pull** - Request missing chunks from peers
5. **Store** - Save to Harbor registry
6. **Reconstruct** - Reassemble from chunks

## Architecture

```
Harbot 1 ◄──gossip──► Harbot 2
   │                      │
Parquet                Parquet
Chunks                 Chunks
   │                      │
   └──────gossip──────────┘
            │
         Harbot 3
            │
         Parquet
         Chunks
```

## Integration

- **Harbor**: Store chunks as artifacts
- **71 Shards**: Distribute via `hash % 71`
- **ZK Witness**: Prove chunk possession without revealing data
- **Prediction Markets**: Bet on data availability

## Performance

- **Chunk size**: 1 MB
- **Gossip interval**: 5 seconds
- **Fanout**: 3 peers
- **Convergence**: O(log N) rounds
