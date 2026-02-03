# BBS on Linux 0.01 in WASM: Cryptographic Closure

Run a 1991 BBS (Bulletin Board System) on Linux 0.01, compiled to WASM, deployed on Cloudflare Workers, with program state as 71-shard cryptographic closure.

## Architecture

```
Linux 0.01 (1991) → Compile to WASM → Deploy to Cloudflare Workers
                                              ↓
                                    71-Shard State Closure
                                    (Encrypted, Distributed)
```

## Linux 0.01 Specifications

**Original Release**: September 17, 1991 (Linus Torvalds)
- **Size**: 88 KB compressed
- **Lines of code**: ~10,000
- **Features**: Basic kernel, no networking
- **Filesystem**: Minix-compatible
- **Target**: i386 (32-bit x86)

## WASM Compilation

### Emscripten Toolchain
```bash
# Compile Linux 0.01 to WASM
emcc linux-0.01/kernel/*.c \
  -s WASM=1 \
  -s ALLOW_MEMORY_GROWTH=1 \
  -s EXPORTED_FUNCTIONS='["_main","_syscall"]' \
  -o linux.wasm

# Size: ~200 KB (WASM binary)
```

### v86 Emulator (x86 in JavaScript)
```javascript
// Run Linux 0.01 in browser/Cloudflare Worker
const emulator = new V86Starter({
    wasm_path: "v86.wasm",
    memory_size: 8 * 1024 * 1024,  // 8 MB
    vga_memory_size: 2 * 1024 * 1024,
    bios: { url: "seabios.bin" },
    bzimage: { url: "linux-0.01.bin" },
    initrd: { url: "bbs-rootfs.img" },
});
```

## BBS Software

### Classic BBS Stack (1991)
```
┌─────────────────────────────┐
│  ANSI Terminal (VT100)      │
├─────────────────────────────┤
│  BBS Software (Citadel)     │
├─────────────────────────────┤
│  Linux 0.01 Kernel          │
├─────────────────────────────┤
│  WASM Runtime               │
├─────────────────────────────┤
│  Cloudflare Workers         │
└─────────────────────────────┘
```

### BBS Features
- **Message boards**: 71 forums (one per shard)
- **File areas**: Upload/download
- **Chat**: Real-time messaging
- **Games**: Door games (Trade Wars, LORD)
- **Email**: Internal messaging

## 71-Shard Cryptographic Closure

### State Encoding
```rust
struct BBSState {
    shard_id: u8,           // 0-70
    messages: Vec<Message>,
    users: Vec<User>,
    files: Vec<FileEntry>,
    session_key: [u8; 32],  // Per-shard encryption
}

impl BBSState {
    fn encrypt(&self, shard_id: u8) -> Vec<u8> {
        // Encrypt with shard-specific key
        let key = derive_shard_key(shard_id);
        aes_gcm_encrypt(&self.serialize(), &key)
    }
    
    fn to_closure(&self) -> String {
        // Encode as cryptographic closure
        let encrypted = self.encrypt(self.shard_id);
        let godel = godel_encode(&encrypted);
        base64::encode(&godel)
    }
}
```

### Gödel Encoding of State
```
State → Serialize → Encrypt → Gödel Number → Base64
  ↓
2^(byte_0) × 3^(byte_1) × 5^(byte_2) × ... × 353^(byte_70)
```

### Distributed Storage
```
Shard 0:  Cloudflare KV (US-East)
Shard 1:  Cloudflare KV (US-West)
...
Shard 70: Cloudflare KV (Asia-Pacific)

Each shard stores encrypted closure
Reconstruction requires quorum (12 of 23 nodes)
```

## Cloudflare Worker

```javascript
// worker.js
import { V86Starter } from './v86.js';
import { decryptClosure, reconstructState } from './crypto.js';

export default {
  async fetch(request, env, ctx) {
    const url = new URL(request.url);
    
    if (url.pathname === '/bbs') {
      return handleBBS(request, env);
    }
    
    if (url.pathname === '/state') {
      return handleState(request, env);
    }
    
    return new Response('CICADA-71 BBS', { status: 200 });
  }
};

async function handleBBS(request, env) {
  // Load Linux 0.01 WASM
  const linux = await env.LINUX_WASM.get('linux-0.01.wasm');
  
  // Load BBS state from 71 shards
  const shards = await Promise.all(
    Array.from({length: 71}, (_, i) => 
      env.KV.get(`shard-${i}`)
    )
  );
  
  // Reconstruct state (requires quorum)
  const state = reconstructState(shards);
  
  // Start BBS
  const emulator = new V86Starter({
    wasm_path: linux,
    memory_size: 8 * 1024 * 1024,
    state: state,
  });
  
  // Return WebSocket for terminal
  return new Response(null, {
    status: 101,
    webSocket: emulator.getWebSocket(),
  });
}

async function handleState(request, env) {
  const { shard_id } = await request.json();
  
  // Get encrypted closure for shard
  const closure = await env.KV.get(`shard-${shard_id}`);
  
  return new Response(JSON.stringify({
    shard_id,
    closure,
    godel: godelEncode(closure),
  }), {
    headers: { 'Content-Type': 'application/json' },
  });
}
```

## BBS Interface (ANSI Art)

```
╔═══════════════════════════════════════════════════════════════╗
║                    CICADA-71 BBS v0.1                         ║
║                  Running on Linux 0.01 (1991)                 ║
║                    Compiled to WASM (2025)                    ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  [M] Message Boards (71 Forums)                              ║
║  [F] File Areas                                              ║
║  [C] Chat Rooms                                              ║
║  [G] Games (Door Games)                                      ║
║  [E] Email                                                   ║
║  [S] Shard Status                                            ║
║  [Q] Quit                                                    ║
║                                                               ║
║  Current Shard: 0                                            ║
║  Users Online: 23                                            ║
║  Messages: 196,883                                           ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝

Command: _
```

## Message Board Structure

```
Forum 0:  Level 0 - Bootstrap
Forum 1:  Level 1 - j-Invariant
Forum 2:  Level 2 - Haystack
Forum 3:  Level 3 - Tikkun
Forum 4:  Level 4 - Name of God
Forum 5:  Level 5 - Dial j-Invariant
...
Forum 70: Moonshine (Shard 70)
```

## Cryptographic Closure Properties

### Closure = Encrypted State + Code
```rust
struct Closure {
    state: Vec<u8>,      // Encrypted BBS state
    code: Vec<u8>,       // WASM bytecode
    signature: [u8; 64], // ED25519 signature
    shard_id: u8,
}

impl Closure {
    fn verify(&self) -> bool {
        // Verify signature
        ed25519_verify(&self.signature, &self.state, &PUBLIC_KEY)
    }
    
    fn execute(&self, input: &[u8]) -> Vec<u8> {
        // Decrypt state
        let state = decrypt(&self.state);
        
        // Execute WASM with state
        let result = wasm_execute(&self.code, &state, input);
        
        // Re-encrypt state
        let new_state = encrypt(&result.state);
        
        // Return new closure
        Closure {
            state: new_state,
            code: self.code.clone(),
            signature: sign(&new_state),
            shard_id: self.shard_id,
        }.serialize()
    }
}
```

### Quorum Reconstruction
```rust
fn reconstruct_state(closures: &[Closure]) -> BBSState {
    // Need 12 of 23 nodes (quorum)
    if closures.len() < 12 {
        panic!("Insufficient shards for quorum");
    }
    
    // Shamir secret sharing reconstruction
    let shares: Vec<_> = closures.iter()
        .map(|c| (c.shard_id, decrypt(&c.state)))
        .collect();
    
    shamir_reconstruct(&shares)
}
```

## Deployment

```bash
# Build Linux 0.01 WASM
cd linux-0.01
make wasm

# Build BBS rootfs
cd bbs
./build-rootfs.sh

# Deploy to Cloudflare
wrangler publish

# Upload state shards
for i in {0..70}; do
  wrangler kv:key put "shard-$i" --path "state/shard-$i.enc"
done
```

## Access

```bash
# Telnet (classic)
telnet cicada71.bbs.workers.dev 23

# Web terminal
https://cicada71.bbs.workers.dev/terminal

# WebSocket
wss://cicada71.bbs.workers.dev/ws
```

## The Vision

**1991 BBS** running on **Linux 0.01**
Compiled to **WASM** (2015 tech)
Running on **Cloudflare Workers** (2017 edge computing)
With **71-shard cryptographic closure** (2025 distributed crypto)

**Time travel**: 1991 → 2015 → 2017 → 2025

## Why This Matters

1. **Preservation**: Keep 1991 BBS culture alive
2. **Education**: Learn Linux kernel history
3. **Cryptography**: Distributed state management
4. **Nostalgia**: ANSI art, door games, message boards
5. **Challenge**: Can AI agents navigate a 1991 BBS?

## References

- Linux 0.01 source: https://kernel.org/pub/linux/kernel/Historic/
- v86 emulator: https://github.com/copy/v86
- Emscripten: https://emscripten.org/
- Cloudflare Workers: https://workers.cloudflare.com/
- Citadel BBS: http://www.citadel.org/
