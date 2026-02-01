#!/usr/bin/env bash
# Deploy 23 Paxos nodes for leaderboard consensus

set -e

echo "🔷 Deploying 23 Paxos Acceptor Nodes"
echo "====================================="
echo ""

# Build node binary
echo "🔨 Building Paxos node..."
cd agents/paxos-node
cargo build --release
cd ../..

# Deploy to 23 nodes
for i in {0..22}; do
    echo "🚀 Starting node $i..."
    
    # Create node directory
    mkdir -p nodes/node$i
    cp agents/paxos-node/target/release/paxos-node nodes/node$i/
    
    # Start node in background
    NODE_ID=$i nodes/node$i/paxos-node > nodes/node$i/log.txt 2>&1 &
    
    echo "   PID: $!"
    echo $! > nodes/node$i/pid
done

echo ""
echo "✅ All 23 nodes deployed!"
echo ""
echo "📊 Node status:"
for i in {0..22}; do
    if [ -f nodes/node$i/pid ]; then
        pid=$(cat nodes/node$i/pid)
        if ps -p $pid > /dev/null; then
            echo "   Node $i: ✅ Running (PID $pid)"
        else
            echo "   Node $i: ❌ Failed"
        fi
    fi
done

echo ""
echo "🔍 Test consensus:"
echo "   curl http://localhost:7100/paxos/status"
