#!/usr/bin/env bash
# Generate Monster Harmonic proofs for all 71 shards

set -e

echo "🔷 Monster Harmonic zkSNARK - Batch Proof Generator"
echo "═══════════════════════════════════════════════════"
echo ""

TOTAL_SHARDS=71
SUCCESS=0
FAILED=0

for SHARD_ID in $(seq 0 $((TOTAL_SHARDS - 1))); do
    echo "📊 Shard $SHARD_ID/$((TOTAL_SHARDS - 1))..."
    
    # Check if witness exists
    WITNESS_PATH="$HOME/.openclaw/shard-$SHARD_ID/zkwitness-$SHARD_ID.json"
    if [ ! -f "$WITNESS_PATH" ]; then
        echo "   ⚠️  No witness found, skipping"
        ((FAILED++))
        continue
    fi
    
    # Generate proof
    if cd ~/introspector/monster-zksnark && nix run . -- $SHARD_ID > /tmp/proof_$SHARD_ID.log 2>&1; then
        echo "   ✅ Proof generated"
        ((SUCCESS++))
    else
        echo "   ❌ Failed (see /tmp/proof_$SHARD_ID.log)"
        ((FAILED++))
    fi
done

echo ""
echo "═══════════════════════════════════════════════════"
echo "✅ Complete: $SUCCESS proofs generated"
echo "❌ Failed: $FAILED shards"
echo ""
echo "Proofs stored in: ~/.openclaw/shard-*/proof.json"
