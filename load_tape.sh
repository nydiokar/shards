#!/usr/bin/env bash
# Monster Game Tape Loader
# Load any game tape by shard number

SHARD=$1

if [ -z "$SHARD" ]; then
    echo "Usage: ./load_tape.sh <shard>"
    echo "Example: ./load_tape.sh 17"
    exit 1
fi

echo "🎮 LOADING TAPE FROM SHARD $SHARD"
echo "=================================="

# Find games on this shard
jq -r ".tapes[] | select(.shard == $SHARD) | "\(.tape_id): \(.name) (\(.year))"" data/game_tapes.json

echo ""
echo "✓ Tape loaded from Shard $SHARD"
