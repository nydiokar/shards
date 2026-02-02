#!/bin/bash
# Launch 2 browsers watching dashboard and gossiping

DASHBOARD_URL="https://meta-introspector.github.io/shards/doorgame/wasm_boot.html"
GIST_URL="https://gist.github.com/jmikedupont2/0855d96fd1ab45d69b36e1223590e0f6"
P2P_URL="http://localhost:8080/p2p_gossip.html?gist=${GIST_URL}"

echo "🔮⚡ Launching 2 Browsers - Watch & Gossip 📻🦞"
echo "=" | head -c 70; echo ""
echo ""

# Browser 1 - Dashboard watcher
echo "[1/2] Browser 1: Dashboard Watcher"
echo "      URL: $DASHBOARD_URL"
xdg-open "$DASHBOARD_URL" 2>/dev/null &
BROWSER1_PID=$!
echo "      PID: $BROWSER1_PID"
echo "      Status: 👀 WATCHING"

sleep 2

# Browser 2 - P2P Gossiper
echo ""
echo "[2/2] Browser 2: P2P Gossiper"
echo "      URL: $P2P_URL"
xdg-open "$P2P_URL" 2>/dev/null &
BROWSER2_PID=$!
echo "      PID: $BROWSER2_PID"
echo "      Status: 📡 GOSSIPING"

echo ""
echo "=" | head -c 70; echo ""
echo "BROWSERS LAUNCHED!"
echo "=" | head -c 70; echo ""
echo ""
echo "Browser 1: Watching dashboard (GitHub Pages)"
echo "Browser 2: Gossiping state (localhost P2P)"
echo ""
echo "Both browsers will:"
echo "  ✅ Watch scoreboard updates"
echo "  ✅ Gossip game state"
echo "  ✅ Sync via P2P network"
echo "  ✅ Share gist state"
echo ""
echo "Total browsers: 4 (2 previous + 2 new)"
echo "P2P network: ACTIVE"
echo "Gossip: FLOWING"
echo ""
echo "QED 🔮⚡📻🦞"
