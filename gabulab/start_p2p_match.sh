#!/bin/bash
# Start 2 browsers playing TradeWars P2P gossip
# Then invite other Kiro to join

echo "🔮⚡📻🦞 STARTING P2P TRADEWARS MATCH"
echo "=" | head -c 70; echo ""
echo ""

# Start HTTP server if not running
if ! pgrep -f "python3 -m http.server 8080" > /dev/null; then
    cd /home/mdupont/introspector/doorgame
    python3 -m http.server 8080 > /tmp/doorgame.log 2>&1 &
    SERVER_PID=$!
    echo "✅ Started server on port 8080 (PID: $SERVER_PID)"
    sleep 2
else
    echo "✅ Server already running on port 8080"
fi

echo ""
echo "🌐 Opening browsers..."
echo ""

# Browser 1 - Player 1
echo "🎮 Browser 1: Player 1 (localhost:8080/p2p_gossip.html)"
xdg-open "http://localhost:8080/p2p_gossip.html" 2>/dev/null &
BROWSER1_PID=$!

sleep 2

# Browser 2 - Player 2  
echo "🎮 Browser 2: Player 2 (localhost:8080/p2p_gossip.html)"
xdg-open "http://localhost:8080/p2p_gossip.html" 2>/dev/null &
BROWSER2_PID=$!

echo ""
echo "=" | head -c 70; echo ""
echo "MATCH STARTED!"
echo "=" | head -c 70; echo ""
echo ""
echo "Browser 1 PID: $BROWSER1_PID"
echo "Browser 2 PID: $BROWSER2_PID"
echo ""
echo "Both browsers will gossip game state via P2P!"
echo ""
echo "=" | head -c 70; echo ""
echo "INVITING OTHER KIRO"
echo "=" | head -c 70; echo ""
echo ""
echo "To invite other Kiro (in another terminal):"
echo ""
echo "  kiro-cli chat"
echo "  > Join TradeWars P2P at http://localhost:8080/p2p_gossip.html"
echo "  > Your peer ID will auto-connect via gossip"
echo ""
echo "Or share this gist:"
echo "  https://gist.github.com/jmikedupont2/0855d96fd1ab45d69b36e1223590e0f6"
echo ""
echo "🦞 LobsterBot hunt: MULTIPLAYER MODE!"
echo "📻 All peers gossiping on 71 shards!"
echo ""
