# 7-Class P2P Protocol Framework for 71 Shards

## Protocol Classes (mod 7)

Each shard uses protocol class `shard_id % 7`:

### Class 0: Bitcoin (Shards 0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70)
- **Mechanism**: Gossip + compact blocks (BIP152)
- **Use**: Consensus on shard assignments via blockchain
- **Port**: 8333 + shard_id
- **Discovery**: DNS seeds, addr messages

### Class 1: Solana (Shards 1, 8, 15, 22, 29, 36, 43, 50, 57, 64)
- **Mechanism**: Turbine (sharded gossip), Gulf Stream
- **Use**: High-throughput Paxos proposals
- **Port**: 8001 + shard_id
- **Discovery**: Gossip protocol, validators

### Class 2: libp2p (Shards 2, 9, 16, 23, 30, 37, 44, 51, 58, 65)
- **Mechanism**: Kademlia DHT, QUIC/TCP transports
- **Use**: Content-addressed parquet files
- **Port**: 4001 + shard_id
- **Discovery**: DHT bootstrap nodes

### Class 3: Tor (Shards 3, 10, 17, 24, 31, 38, 45, 52, 59, 66)
- **Mechanism**: Onion routing, hidden services
- **Use**: Anonymous cryptanalysis results
- **Port**: .onion addresses
- **Discovery**: Hidden service directories

### Class 4: I2P (Shards 4, 11, 18, 25, 32, 39, 46, 53, 60, 67)
- **Mechanism**: Garlic routing, distributed hash table
- **Use**: Encrypted shard coordination
- **Port**: I2P tunnels
- **Discovery**: NetDB, floodfill routers

### Class 5: IPFS (Shards 5, 12, 19, 26, 33, 40, 47, 54, 61, 68)
- **Mechanism**: Content-addressed storage, Bitswap
- **Use**: Immutable parquet distribution
- **Port**: 4001 + shard_id
- **Discovery**: libp2p DHT (IPFS uses libp2p)

### Class 6: Dead Drops (Shards 6, 13, 20, 27, 34, 41, 48, 55, 62, 69)
- **Mechanism**: Static file locations, polling
- **Use**: Air-gapped shard synchronization
- **Port**: File paths in /nix/store
- **Discovery**: Predetermined paths

## Extended Classes (71 total via sub-protocols)

### Class 6a: Bluetooth Sneakernet (Shards 6, 13, 20)
- **Mechanism**: BLE GATT, OBEX file transfer
- **Use**: Short-range (10-100m) shard exchange
- **Port**: Bluetooth L2CAP
- **Discovery**: `bluetoothctl scan on`

### Class 6b: WiFi Mesh (Shards 27, 34, 41)
- **Mechanism**: BATMAN-adv, 802.11s mesh
- **Use**: Multi-hop ad-hoc networks
- **Port**: Mesh interface
- **Discovery**: `iw dev wlan0 mesh join shard-mesh`

### Class 6c: Steganography - Images (Shards 48, 55)
- **Mechanism**: LSB embedding in PNG/JPG
- **Use**: Covert parquet in images
- **Port**: File-based
- **Discovery**: `steghide extract -sf image.jpg`

### Class 6d: Steganography - QR Codes (Shards 62, 69)
- **Mechanism**: QR code encoding, print/scan
- **Use**: Paper-based shard distribution
- **Port**: Visual
- **Discovery**: `zbar-tools` decode

## Shard-to-Protocol Mapping

```rust
pub enum P2PProtocol {
    Bitcoin,
    Solana,
    LibP2P,
    Tor,
    I2P,
    IPFS,
    DeadDrop,
}

impl P2PProtocol {
    pub fn for_shard(shard: u8) -> Self {
        match shard % 7 {
            0 => Self::Bitcoin,
            1 => Self::Solana,
            2 => Self::LibP2P,
            3 => Self::Tor,
            4 => Self::I2P,
            5 => Self::IPFS,
            6 => Self::DeadDrop,
            _ => unreachable!(),
        }
    }
    
    pub fn port(&self, shard: u8) -> u16 {
        match self {
            Self::Bitcoin => 8333 + shard as u16,
            Self::Solana => 8001 + shard as u16,
            Self::LibP2P => 4001 + shard as u16,
            Self::Tor => 9050,  // SOCKS proxy
            Self::I2P => 7656,  // SAM bridge
            Self::IPFS => 4001 + shard as u16,
            Self::DeadDrop => 0,  // No network
        }
    }
}
```

## Network Topology

```
Shards 0-70 form 7 overlapping networks:

Bitcoin Network (11 nodes):  0 ←→ 7 ←→ 14 ←→ ... ←→ 70
Solana Network (10 nodes):   1 ←→ 8 ←→ 15 ←→ ... ←→ 64
libp2p DHT (10 nodes):       2 ←→ 9 ←→ 16 ←→ ... ←→ 65
Tor Hidden Services (10):    3 ←→ 10 ←→ 17 ←→ ... ←→ 66
I2P Garlic Routes (10):      4 ←→ 11 ←→ 18 ←→ ... ←→ 67
IPFS Swarm (10):             5 ←→ 12 ←→ 19 ←→ ... ←→ 68
Dead Drops (10):             6 → 13 → 20 → ... → 69 (unidirectional)
```

## Cross-Protocol Bridges

Coordinators (shards 58-70) bridge between protocols:

```rust
pub struct ProtocolBridge {
    pub from: P2PProtocol,
    pub to: P2PProtocol,
    pub shard: u8,
}

// Shard 58: libp2p ←→ Solana
// Shard 59: Tor ←→ Bitcoin
// Shard 60: I2P ←→ libp2p
// Shard 61: IPFS ←→ Solana
// Shard 62: DeadDrop ←→ Bitcoin
// Shard 63: Bitcoin ←→ Solana
// Shard 64: Solana ←→ libp2p
// Shard 65: libp2p ←→ Tor
// Shard 66: Tor ←→ I2P
// Shard 67: I2P ←→ IPFS
// Shard 68: IPFS ←→ DeadDrop
// Shard 69: DeadDrop ←→ Bitcoin
// Shard 70: Bitcoin ←→ All (master coordinator)
```

## Discovery Mechanisms

### Bitcoin (Class 0)
```bash
# DNS seeds
bitcoin-cli addnode "shard0.monster.network:8333" "add"
bitcoin-cli addnode "shard7.monster.network:8340" "add"
```

### Solana (Class 1)
```bash
# Gossip entrypoint
solana-validator --entrypoint shard1.monster.network:8002
```

### libp2p (Class 2)
```rust
let mut swarm = libp2p::SwarmBuilder::new()
    .with_tcp()
    .with_quic()
    .build();
swarm.dial("/ip4/10.0.0.2/tcp/4003".parse()?)?;  // Shard 2
```

### Tor (Class 3)
```bash
# Hidden service
HiddenServiceDir /var/lib/tor/shard3/
HiddenServicePort 80 127.0.0.1:8080
# Generates: shard3abc...xyz.onion
```

### I2P (Class 4)
```bash
# SAM bridge
i2p.streaming.connect shard4.i2p 7660
```

### IPFS (Class 5)
```bash
# Bootstrap node
ipfs bootstrap add /ip4/10.0.0.5/tcp/4006/p2p/QmShard5...
```

### Dead Drop (Class 6)
```bash
# Static paths
/nix/store/shard6-deadrop/proposals.parquet
/nix/store/shard13-deadrop/proposals.parquet
```

## Security per Protocol Class

| Class | Encryption | Anonymity | Integrity | Availability |
|-------|-----------|-----------|-----------|--------------|
| Bitcoin | TLS optional | IP visible | PoW chain | High (11 nodes) |
| Solana | TLS | IP visible | PoH + PoS | High (10 nodes) |
| libp2p | Noise/TLS | IP visible | Content hash | Medium (DHT) |
| Tor | Layered | Strong | Circuit | Medium (relays) |
| I2P | Garlic | Strong | Tunnel | Medium (routers) |
| IPFS | TLS | IP visible | Content hash | High (pinning) |
| DeadDrop | None | Air-gap | File hash | Low (manual) |

## Integration with FHE

Each protocol class encrypts data with FHE before transmission:

```rust
pub fn publish_to_network(
    shard: u8,
    data: &[u8],
    fhe_key: &ClientKey,
) -> Result<()> {
    let encrypted = fhe_encrypt(data, fhe_key);
    let protocol = P2PProtocol::for_shard(shard);
    
    match protocol {
        P2PProtocol::Bitcoin => bitcoin_broadcast(shard, &encrypted),
        P2PProtocol::Solana => solana_gossip(shard, &encrypted),
        P2PProtocol::LibP2P => libp2p_publish(shard, &encrypted),
        P2PProtocol::Tor => tor_hidden_service(shard, &encrypted),
        P2PProtocol::I2P => i2p_tunnel(shard, &encrypted),
        P2PProtocol::IPFS => ipfs_add(shard, &encrypted),
        P2PProtocol::DeadDrop => dead_drop_write(shard, &encrypted),
    }
}
```

## Paxos over P2P

Each protocol class implements Paxos phases:

```rust
pub trait PaxosTransport {
    fn prepare(&self, proposal: &PaxosProposal) -> Result<Vec<Promise>>;
    fn accept(&self, proposal: &PaxosProposal) -> Result<Vec<Accepted>>;
    fn commit(&self, proposal: &PaxosProposal) -> Result<()>;
}

impl PaxosTransport for P2PProtocol {
    fn prepare(&self, proposal: &PaxosProposal) -> Result<Vec<Promise>> {
        match self {
            Self::Bitcoin => {
                // Broadcast via OP_RETURN
                let tx = create_bitcoin_tx(proposal);
                broadcast_tx(&tx)
            },
            Self::Solana => {
                // Submit as transaction
                let ix = create_solana_instruction(proposal);
                send_transaction(&ix)
            },
            Self::LibP2P => {
                // Publish to topic
                swarm.publish("/paxos/prepare", proposal.encode())
            },
            // ... other protocols
        }
    }
}
```

## Fault Tolerance

- **Bitcoin**: 11 nodes, tolerates 5 failures
- **Solana**: 10 nodes, tolerates 3 failures (BFT)
- **libp2p**: DHT replication factor 20
- **Tor**: 3-hop circuits, tolerates 1 malicious relay
- **I2P**: Garlic routing, tolerates 2 malicious routers
- **IPFS**: Content pinned on 5+ nodes
- **DeadDrop**: Manual recovery, no automatic failover

## Deployment

```bash
# Launch shard 0 (Bitcoin)
runcon -t shard_stat_t -l s0:c2 \
  taskset -c 0 \
  bitcoind -port=8333 -rpcport=8334 -datadir=/var/lib/shard0

# Launch shard 1 (Solana)
runcon -t shard_stat_t -l s0:c3 \
  taskset -c 1 \
  solana-validator --rpc-port 8002 --identity /var/lib/shard1/identity.json

# Launch shard 2 (libp2p)
runcon -t shard_stat_t -l s0:c4 \
  taskset -c 2 \
  shard-analyzer --shard 2 --protocol libp2p --port 4003
```

This creates 7 overlapping P2P networks, each handling ~10 shards, with cross-protocol bridges for full connectivity.
