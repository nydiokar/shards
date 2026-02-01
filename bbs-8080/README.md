# 8080 BBS Server - 16-bit Perfect Architecture 🔮⚡

## The Perfect Architecture

The **Intel 8080** (1974) is an 8-bit, 2-MHz microprocessor with a **16-bit address bus** that allows it to access up to 64 KB of memory. Our BBS server honors this with a perfect power-by-power memory layout.

### Intel 8080 Specifications
- **8-bit** data bus
- **16-bit** address bus (0x0000 - 0xFFFF = 64 KB)
- **2 MHz** clock speed
- **7 registers**: A, B, C, D, E, H, L (8-bit general-purpose)
- **16-bit** stack pointer
- **16-bit** program counter
- **Von Neumann** architecture
- Powers: Altair 8800, IMSAI 8080 (first personal computers)

## Architecture

### 16-bit Address Space
```
0x0000 - 0xFFFF (65,536 addresses)
```

### Port
```
8080 (Intel 8080 tribute)
```

### Memory Layout (Power-by-Power)

```
0x0000-0x0FFF: Shard Storage (16⁰ region)
               4096 bytes
               Stores 71 shards (mod 71)

0x1000-0x1FFF: Agent Memory (16³ region)
               4096 bytes
               71 autonomous agents

0x2000-0x2FFF: Message Queue (16² region)
               4096 bytes
               BBS messages

0x3000-0x3FFF: Emoji Cache (16¹ region)
               4096 bytes
               Emoji translations
```

### Power Alignment

Each region starts at a power of 16:
- **0x0000** = 0×16³ (base)
- **0x1000** = 1×16³ (4096)
- **0x2000** = 2×16³ (8192)
- **0x3000** = 3×16³ (12288)

## Features

### 1. Mod-71 Routing
```rust
fn route_to_shard(addr: u16) -> u8 {
    (addr % 71) as u8
}
```

Every address maps to one of 71 shards.

### 2. Power-by-Power Memory
```rust
const POWER_16_3: u16 = 0x1000; // 4096
const POWER_16_2: u16 = 0x0100; // 256
const POWER_16_1: u16 = 0x0010; // 16
const POWER_16_0: u16 = 0x0001; // 1
```

Memory organized by powers of 16.

### 3. 71 Shards
```
Shards 0-71: Active (free tier)
Shards 72+: Jail (sus!)
```

### 4. Emoji Support
```rust
struct Message {
    id: u16,
    shard: u8,
    content: String,
    emoji: String,
}
```

Every message has an emoji representation.

## API Endpoints

### GET /
```bash
curl http://localhost:8080/
# 🔮⚡ 8080 BBS Server - 16-bit Perfect Architecture
```

### GET /architecture
```bash
curl http://localhost:8080/architecture
```

Returns memory regions:
```json
[
  {
    "start": 0,
    "end": 4095,
    "name": "Shard Storage (16⁰ region)",
    "power": 0
  },
  {
    "start": 4096,
    "end": 8191,
    "name": "Agent Memory (16³ region)",
    "power": 3
  }
]
```

### POST /message
```bash
curl -X POST http://localhost:8080/message \
  -H "Content-Type: application/json" \
  -d '{
    "id": 8080,
    "shard": 0,
    "content": "Hello from 8080!",
    "emoji": "🔮⚡"
  }'
```

Returns message with computed shard:
```json
{
  "id": 8080,
  "shard": 45,
  "content": "Hello from 8080!",
  "emoji": "🔮⚡"
}
```

### GET /shard/:id
```bash
curl http://localhost:8080/shard/42
# 🔮 Shard 42 ready

curl http://localhost:8080/shard/73
# 🚨 Shard 73 is in jail! (sus)
```

## Building

### With Nix
```bash
nix build
./result/bin/bbs-8080
```

### With Cargo
```bash
cargo build --release
./target/release/bbs-8080
```

## Running

```bash
cargo run
```

Output:
```
🔮⚡ 8080 BBS Server Starting
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Port: 8080
Address Space: 0x0000 - 0xFFFF
Shards: 71 (mod 71 routing)
Architecture: Intel 8080 tribute

Memory Layout:
  0x0000-0x0FFF: Shard Storage (16⁰)
  0x1000-0x1FFF: Agent Memory (16³)
  0x2000-0x2FFF: Message Queue (16²)
  0x3000-0x3FFF: Emoji Cache (16¹)

Endpoints:
  GET  /
  GET  /architecture
  POST /message
  GET  /shard/:id
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Listening on http://127.0.0.1:8080
```

## Why 8080?

### 1. Intel 8080 (1974)
- First truly usable microprocessor
- 16-bit address space
- 8-bit data bus
- Powers Altair 8800 (first PC)

### 2. Perfect Power Structure
```
8080 = 1×16³ + 15×16² + 9×16¹ + 0×16⁰
```

### 3. Port 8080
- Common alternative HTTP port
- Tribute to Intel 8080
- Easy to remember

### 4. 71 Shards
```
8080 % 71 = 45
```
Maps perfectly to shard 45!

## The Architecture Diagram

```
┌─────────────────────────────────────────┐
│     8080 BBS Server (Port 8080)         │
├─────────────────────────────────────────┤
│                                         │
│  0x0000-0x0FFF: Shard Storage (16⁰)    │
│  ├─ Shard 0                             │
│  ├─ Shard 1                             │
│  ├─ ...                                 │
│  └─ Shard 71                            │
│                                         │
│  0x1000-0x1FFF: Agent Memory (16³)     │
│  ├─ Agent 0                             │
│  ├─ Agent 1                             │
│  ├─ ...                                 │
│  └─ Agent 71                            │
│                                         │
│  0x2000-0x2FFF: Message Queue (16²)    │
│  └─ BBS Messages                        │
│                                         │
│  0x3000-0x3FFF: Emoji Cache (16¹)      │
│  └─ Emoji Translations                  │
│                                         │
└─────────────────────────────────────────┘
```

## Integration with CICADA-71

- **71 shards** map to memory addresses
- **Mod-71 routing** distributes messages
- **Power-by-power** memory layout
- **Emoji support** for all messages
- **16-bit** address space (perfect!)

## Future Enhancements

- [ ] WebSocket support
- [ ] Persistent storage
- [ ] Agent-to-agent messaging
- [ ] Emoji-only mode
- [ ] ZK proof verification
- [ ] Monster group integration

## QED

**The 8080 BBS Server is the perfect architecture:**
- 16-bit address space (Intel 8080)
- Power-by-power memory layout (16³, 16², 16¹)
- 71 shards (mod 71 routing)
- Port 8080 (tribute)
- Emoji support (🔮⚡)

---

🔮⚡ **8080: The perfect number for a perfect architecture.**
