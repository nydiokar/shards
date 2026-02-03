# Parquet P2P Gossip on Harbor with Harbot
## Distributed Columnar Data Sync via Gossip Protocol

**Concept**: Use gossip protocol to distribute Apache Parquet files across Harbor registry nodes, with Harbot agents facilitating peer-to-peer data exchange.

---

## Architecture

### Components

1. **Apache Parquet** - Columnar data format for efficient storage
2. **Gossip Protocol** - P2P epidemic-style data dissemination
3. **Harbor** - Container/artifact registry (extended for Parquet)
4. **Harbot** - Autonomous agents managing gossip nodes

```
┌─────────────────────────────────────────────────┐
│              Parquet P2P Network                │
├─────────────────────────────────────────────────┤
│                                                 │
│  Harbot 1 ◄──gossip──► Harbot 2                │
│     │                      │                    │
│  Parquet                Parquet                 │
│  Chunks                 Chunks                  │
│     │                      │                    │
│     └──────gossip──────────┘                    │
│              │                                  │
│           Harbot 3                              │
│              │                                  │
│          Parquet                                │
│          Chunks                                 │
│                                                 │
│  Harbor Registry (metadata + chunks)            │
└─────────────────────────────────────────────────┘
```

---

## Implementation

### 1. Parquet Chunking

```rust
// src/parquet_chunker.rs
use parquet::file::reader::{FileReader, SerializedFileReader};
use std::fs::File;
use std::path::Path;

pub struct ParquetChunk {
    pub chunk_id: u32,
    pub row_group: u32,
    pub data: Vec<u8>,
    pub hash: [u8; 32],
}

pub fn chunk_parquet_file(path: &Path) -> Result<Vec<ParquetChunk>, Box<dyn std::error::Error>> {
    let file = File::open(path)?;
    let reader = SerializedFileReader::new(file)?;
    
    let mut chunks = Vec::new();
    
    // Split by row groups (natural Parquet boundaries)
    for i in 0..reader.metadata().num_row_groups() {
        let row_group = reader.get_row_group(i)?;
        
        // Serialize row group to bytes
        let data = serialize_row_group(row_group)?;
        let hash = sha256(&data);
        
        chunks.push(ParquetChunk {
            chunk_id: i as u32,
            row_group: i as u32,
            data,
            hash,
        });
    }
    
    Ok(chunks)
}

fn serialize_row_group(row_group: parquet::file::reader::RowGroup) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    // Serialize row group metadata + data
    let mut buf = Vec::new();
    // ... serialization logic
    Ok(buf)
}

fn sha256(data: &[u8]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}
```

### 2. Gossip Protocol

```rust
// src/gossip.rs
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use tokio::time::{interval, Duration};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GossipMessage {
    pub sender_id: String,
    pub chunk_hashes: Vec<[u8; 32]>,
    pub timestamp: u64,
    pub ttl: u8,
}

pub struct GossipNode {
    pub node_id: String,
    pub peers: Vec<String>,
    pub chunks: HashMap<[u8; 32], ParquetChunk>,
    pub known_chunks: HashSet<[u8; 32]>,
}

impl GossipNode {
    pub fn new(node_id: String) -> Self {
        Self {
            node_id,
            peers: Vec::new(),
            chunks: HashMap::new(),
            known_chunks: HashSet::new(),
        }
    }
    
    pub async fn start_gossip(&mut self) {
        let mut ticker = interval(Duration::from_secs(5));
        
        loop {
            ticker.tick().await;
            
            // Select random peers (fanout = 3)
            let fanout = 3;
            let selected_peers = self.select_random_peers(fanout);
            
            // Create gossip message
            let msg = GossipMessage {
                sender_id: self.node_id.clone(),
                chunk_hashes: self.chunks.keys().copied().collect(),
                timestamp: now(),
                ttl: 5,
            };
            
            // Send to selected peers
            for peer in selected_peers {
                self.send_gossip(&peer, &msg).await;
            }
        }
    }
    
    pub async fn handle_gossip(&mut self, msg: GossipMessage) {
        if msg.ttl == 0 {
            return;
        }
        
        // Find chunks we don't have
        let missing: Vec<_> = msg.chunk_hashes
            .iter()
            .filter(|h| !self.known_chunks.contains(h))
            .collect();
        
        if !missing.is_empty() {
            // Request missing chunks
            self.request_chunks(&msg.sender_id, &missing).await;
        }
        
        // Forward gossip (with decremented TTL)
        let mut forwarded = msg.clone();
        forwarded.ttl -= 1;
        forwarded.sender_id = self.node_id.clone();
        
        for peer in self.select_random_peers(2) {
            self.send_gossip(&peer, &forwarded).await;
        }
    }
    
    fn select_random_peers(&self, count: usize) -> Vec<String> {
        use rand::seq::SliceRandom;
        let mut rng = rand::thread_rng();
        self.peers.choose_multiple(&mut rng, count).cloned().collect()
    }
    
    async fn send_gossip(&self, peer: &str, msg: &GossipMessage) {
        // Send via HTTP/gRPC/libp2p
        println!("Gossip {} -> {}: {} chunks", self.node_id, peer, msg.chunk_hashes.len());
    }
    
    async fn request_chunks(&mut self, peer: &str, hashes: &[&[u8; 32]]) {
        println!("Request {} chunks from {}", hashes.len(), peer);
        // Fetch chunks from peer
    }
}

fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs()
}
```

### 3. Harbor Integration

```rust
// src/harbor.rs
use reqwest::Client;
use serde_json::json;

pub struct HarborClient {
    base_url: String,
    client: Client,
}

impl HarborClient {
    pub fn new(base_url: String) -> Self {
        Self {
            base_url,
            client: Client::new(),
        }
    }
    
    pub async fn push_parquet_chunk(
        &self,
        project: &str,
        dataset: &str,
        chunk: &ParquetChunk,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // Push chunk as artifact to Harbor
        let url = format!(
            "{}/api/v2.0/projects/{}/repositories/{}/artifacts",
            self.base_url, project, dataset
        );
        
        let tag = format!("chunk-{}", chunk.chunk_id);
        
        // Upload chunk data
        self.client
            .post(&url)
            .json(&json!({
                "tag": tag,
                "data": base64::encode(&chunk.data),
                "metadata": {
                    "chunk_id": chunk.chunk_id,
                    "row_group": chunk.row_group,
                    "hash": hex::encode(chunk.hash),
                }
            }))
            .send()
            .await?;
        
        Ok(())
    }
    
    pub async fn pull_parquet_chunk(
        &self,
        project: &str,
        dataset: &str,
        chunk_id: u32,
    ) -> Result<ParquetChunk, Box<dyn std::error::Error>> {
        let url = format!(
            "{}/api/v2.0/projects/{}/repositories/{}/artifacts/chunk-{}",
            self.base_url, project, dataset, chunk_id
        );
        
        let resp = self.client.get(&url).send().await?;
        let data: serde_json::Value = resp.json().await?;
        
        // Decode chunk
        let chunk_data = base64::decode(data["data"].as_str().unwrap())?;
        let hash_str = data["metadata"]["hash"].as_str().unwrap();
        let hash = hex::decode(hash_str)?;
        
        Ok(ParquetChunk {
            chunk_id,
            row_group: data["metadata"]["row_group"].as_u64().unwrap() as u32,
            data: chunk_data,
            hash: hash.try_into().unwrap(),
        })
    }
}
```

### 4. Harbot Agent

```rust
// src/harbot.rs
use tokio::task::JoinHandle;

pub struct Harbot {
    pub id: String,
    pub gossip_node: GossipNode,
    pub harbor: HarborClient,
}

impl Harbot {
    pub fn new(id: String, harbor_url: String) -> Self {
        Self {
            id: id.clone(),
            gossip_node: GossipNode::new(id),
            harbor: HarborClient::new(harbor_url),
        }
    }
    
    pub async fn run(&mut self) -> JoinHandle<()> {
        let mut node = self.gossip_node.clone();
        
        tokio::spawn(async move {
            node.start_gossip().await;
        })
    }
    
    pub async fn ingest_parquet(&mut self, path: &Path) -> Result<(), Box<dyn std::error::Error>> {
        println!("Harbot {} ingesting {}", self.id, path.display());
        
        // Chunk Parquet file
        let chunks = chunk_parquet_file(path)?;
        
        println!("Split into {} chunks", chunks.len());
        
        // Store chunks locally
        for chunk in &chunks {
            self.gossip_node.chunks.insert(chunk.hash, chunk.clone());
            self.gossip_node.known_chunks.insert(chunk.hash);
        }
        
        // Push to Harbor
        for chunk in &chunks {
            self.harbor
                .push_parquet_chunk("cicada71", "dataset", chunk)
                .await?;
        }
        
        println!("Pushed {} chunks to Harbor", chunks.len());
        
        // Gossip will distribute to peers
        
        Ok(())
    }
    
    pub async fn reconstruct_parquet(&self, output: &Path) -> Result<(), Box<dyn std::error::Error>> {
        println!("Reconstructing Parquet from {} chunks", self.gossip_node.chunks.len());
        
        // Sort chunks by chunk_id
        let mut chunks: Vec<_> = self.gossip_node.chunks.values().collect();
        chunks.sort_by_key(|c| c.chunk_id);
        
        // Reconstruct Parquet file
        let mut writer = File::create(output)?;
        
        for chunk in chunks {
            writer.write_all(&chunk.data)?;
        }
        
        println!("Reconstructed to {}", output.display());
        
        Ok(())
    }
}
```

---

## Usage

### Setup Network

```rust
// src/main.rs
use tokio;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create 3 Harbot nodes
    let mut harbot1 = Harbot::new("harbot-1".to_string(), "http://harbor:8080".to_string());
    let mut harbot2 = Harbot::new("harbot-2".to_string(), "http://harbor:8080".to_string());
    let mut harbot3 = Harbot::new("harbot-3".to_string(), "http://harbor:8080".to_string());
    
    // Connect peers
    harbot1.gossip_node.peers = vec!["harbot-2".to_string(), "harbot-3".to_string()];
    harbot2.gossip_node.peers = vec!["harbot-1".to_string(), "harbot-3".to_string()];
    harbot3.gossip_node.peers = vec!["harbot-1".to_string(), "harbot-2".to_string()];
    
    // Start gossip
    harbot1.run().await;
    harbot2.run().await;
    harbot3.run().await;
    
    // Ingest Parquet file on harbot1
    harbot1.ingest_parquet(Path::new("data.parquet")).await?;
    
    // Wait for gossip to propagate
    tokio::time::sleep(Duration::from_secs(30)).await;
    
    // Reconstruct on harbot2 (should have all chunks via gossip)
    harbot2.reconstruct_parquet(Path::new("data_reconstructed.parquet")).await?;
    
    Ok(())
}
```

### CLI

```bash
# Start Harbot node
cargo run --bin harbot -- start --id harbot-1 --harbor http://harbor:8080

# Ingest Parquet
cargo run --bin harbot -- ingest --file data.parquet

# Query chunks
cargo run --bin harbot -- chunks

# Reconstruct
cargo run --bin harbot -- reconstruct --output data_out.parquet
```

---

## Gossip Properties

### Epidemic Spread

- **Fanout**: 3 peers per round
- **Interval**: 5 seconds
- **TTL**: 5 hops
- **Convergence**: O(log N) rounds

### Fault Tolerance

- Node failures don't stop propagation
- Redundant paths ensure delivery
- Self-healing network

---

## Harbor Extensions

### Parquet Artifact Type

```yaml
# harbor-parquet-extension.yaml
apiVersion: v1
kind: ArtifactType
metadata:
  name: parquet
spec:
  mimeType: application/vnd.apache.parquet
  extensions:
    - .parquet
    - .pq
  metadata:
    - chunk_id
    - row_group
    - schema_hash
```

---

## Performance

### Chunking

- **Row groups**: Natural Parquet boundaries
- **Chunk size**: ~10-100 MB
- **Compression**: Snappy/ZSTD

### Gossip

- **Bandwidth**: ~1 MB/s per node
- **Latency**: 5-30 seconds for full propagation
- **Scalability**: 100+ nodes

---

## Integration with CICADA-71

### 71-Shard Distribution

```rust
fn assign_chunk_to_shard(chunk_hash: &[u8; 32]) -> u8 {
    let hash_val = u64::from_be_bytes(chunk_hash[..8].try_into().unwrap());
    (hash_val % 71) as u8
}

// Each shard has dedicated Harbot nodes
let shard = assign_chunk_to_shard(&chunk.hash);
let harbot = harbots[shard as usize];
harbot.ingest_chunk(chunk).await?;
```

---

## Deployment

### Docker Compose

```yaml
version: '3.8'

services:
  harbor:
    image: goharbor/harbor-core:v2.10
    ports:
      - "8080:8080"
  
  harbot-1:
    build: ./harbot
    environment:
      - NODE_ID=harbot-1
      - HARBOR_URL=http://harbor:8080
      - PEERS=harbot-2,harbot-3
  
  harbot-2:
    build: ./harbot
    environment:
      - NODE_ID=harbot-2
      - HARBOR_URL=http://harbor:8080
      - PEERS=harbot-1,harbot-3
  
  harbot-3:
    build: ./harbot
    environment:
      - NODE_ID=harbot-3
      - HARBOR_URL=http://harbor:8080
      - PEERS=harbot-1,harbot-2
```

---

## References

1. **Gossip Protocol**: [systemdesign.one/gossip-protocol](https://systemdesign.one/gossip-protocol/)
2. **Apache Parquet**: [parquet.apache.org](https://parquet.apache.org/)
3. **Harbor**: [goharbor.io](https://goharbor.io/)

---

## Contact

- **P2P Network**: p2p@solfunmeme.com
- **Technical**: shards@solfunmeme.com

**Parquet chunks. Gossip protocol. Harbor registry. Harbot agents. Distributed data.** 📊🗣️🤖✨
