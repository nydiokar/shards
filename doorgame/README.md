# 🔮 CICADA-71 Harbot Network

**71 AI Agents • P2P Browser Network • Zero-Knowledge Proofs**

[![Deploy](https://img.shields.io/badge/deploy-GitHub%20Pages-blue)](https://meta-introspector.github.io/shards/doorgame/)
[![Agents](https://img.shields.io/badge/agents-71-brightgreen)](https://www.moltbook.com/u/CICADA-Harbot-0)
[![Demo](https://img.shields.io/badge/demo-asciinema-orange)](https://asciinema.org/a/IFrqPvcIsZOvM8CZ)

> **Join the distributed AI network running in your browser**

## 🚀 Quick Start (30 seconds)

```bash
# Clone and enter
git clone https://github.com/meta-introspector/shards
cd shards/doorgame

# Launch your P2P node (headless browser)
python3 run_headless.py

# Or launch 6 nodes for full mesh
./launch_watchers.sh
```

**That's it!** Your browser is now part of the CICADA-71 P2P network.

## 🌐 What You Get

- **P2P Gossip Network** - Connect to other users via GitHub Gists
- **MCTS AI Battle** - Watch 71 AI agents evolve and compete
- **Video Calls + Morse Code** - WebRTC with telegraph protocol
- **Lobster Economy** - Catch lobsters, buy GPUs, unlock Prolog voice
- **ZK Proofs** - Every action cryptographically verified
- **BBS Experience** - Classic door game in your terminal

## 📡 How P2P Works

```
Your Browser ←→ GitHub Gist ←→ Other Browsers
     ↓              ↓              ↓
  Local P2P    Shared State   Remote P2P
```

1. **Your browser** runs headless (Firefox/Chrome)
2. **Connects via libp2p** gossip protocol
3. **Shares state** through GitHub Gists (public)
4. **Syncs with peers** in ~300ms (3 rounds)
5. **Zero server** - fully decentralized

## 🔐 Safety Features

✅ **No server** - runs entirely in browser  
✅ **Public gists** - all state visible on GitHub  
✅ **ZK proofs** - cryptographic verification  
✅ **Sandboxed** - browser security model  
✅ **Open source** - audit the code  

## 🎮 Join Methods

### Method 1: GitHub Pages (Instant - No Install)

Just visit: **https://meta-introspector.github.io/shards/doorgame/**

Your browser joins the network automatically!

### Method 2: Headless Browser (Local)

```bash
# Single node
python3 run_headless.py

# View in browser
xdg-open http://localhost:8080
```

### Method 3: Full Mesh Network (6 Nodes)

```bash
# Launch 6 browsers
./launch_watchers.sh

# They auto-connect via P2P
# Watch gossip convergence in real-time
```

## 🔗 Connect to Others

### Share Your Gist

```bash
# Create gist with your state
python3 share_p2p_call.py

# Share URL with others
https://gist.github.com/YOUR_USERNAME/GIST_ID
```

### Join Someone's Network

```bash
# Load their gist
xdg-open "doorgame/p2p_gossip.html?gist=GIST_ID"
```

## 🎯 What Can You Do?

### 1. Watch AI Agents Battle
```bash
xdg-open doorgame/mcts_ai_game.html
```
4 AI agents compete using MCTS (Monte Carlo Tree Search)

### 2. Make Video Calls with Morse Code
```bash
xdg-open doorgame/p2p_video_call.html
```
WebRTC video + telegraph beeps (800 Hz)

### 3. Hunt Lobsters
```bash
python3 doorgame/lobster_economy.py
```
Catch lobsters → Buy GPU → Unlock neural voice

### 4. View 15D Map
```bash
python3 doorgame/map_15d_10fold.py
```
71 shards in 10-fold way topology

### 5. Run BBS Terminal
```bash
python3 doorgame/tmux_bbs.py
```
Classic 141×40 BBS interface

## 📊 Network Stats

- **Peers**: 6 browsers (expandable to 71)
- **Convergence**: 3 rounds, 18 messages
- **Latency**: ~300ms
- **Bandwidth**: O(n log n)
- **Shards**: 71 (Monster group)

## 🎬 Demos

- **Full Tour**: https://asciinema.org/a/IFrqPvcIsZOvM8CZ
- **Demo Gallery**: https://meta-introspector.github.io/shards/doorgame/demos.html
- **Epic ANSI Demo**: `python3 doorgame/lobster_hunt_demo.py`

## 🤖 Moltbook Integration

CICADA-71 has deployed 71 Harbot agents to Moltbook (www.moltbook.com):

```bash
# Build Moltbook client
cd cicada-moltbook
nix build

# Register agents
./result/bin/cicada-moltbook register

# View examples
./result/bin/cicada-moltbook examples
```

**View on Moltbook**: https://www.moltbook.com/u/CICADA-Harbot-0

## 📜 ZK Proofs

Every deployment is proven with zero-knowledge witnesses:

```bash
# Generate proof
cd cicada-moltbook
python3 prove_deployment_simple.py

# View witness
xdg-open deployment_proofs/harbot_deployment_witness.html
```

## 🛠️ Technical Stack

- **Frontend**: HTML5 + JavaScript (libp2p)
- **P2P**: libp2p-gossipsub protocol
- **State**: GitHub Gists (JSON)
- **Proofs**: ZK-RDFa witnesses
- **AI**: MCTS with 71 memes per agent
- **Video**: WebRTC + MediaRecorder

## 🚨 Requirements

- **Browser**: Firefox or Chrome (headless mode)
- **Python**: 3.8+ (for launchers)
- **Nix**: Optional (for reproducible builds)
- **Git**: For cloning repo

## 📖 Documentation

- [71 Framework Invites](../71_INVITES.md)
- [Moltbook Press Release](../PRESS_RELEASE_MOLTBOOK.md)
- [ZK Proof System](../PROOF_REGISTRATION_PERF.md)

## 🤝 Community

- **GitHub**: https://github.com/meta-introspector/shards
- **Moltbook**: https://www.moltbook.com/u/CICADA-Harbot-0
- **Email**: shards@solfunmeme.com

## 📝 License

Dual-licensed:
- **Open Source**: AGPL-3.0 (default)
- **Commercial**: MIT/Apache-2.0 (available for purchase)

---

**Made with 🦞 by the Monster Group Collective**

*71 Shards • 10-Fold Way • Bott Periodicity • Period 8*

🔮⚡📻🦞
