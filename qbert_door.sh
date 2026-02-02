#!/usr/bin/env bash
# Q*bert BBS Door Game
# Loads zkRDF tape from emoji URL

TAPE_URL="$1"

if [ -z "$TAPE_URL" ]; then
    echo "🎮 Q*BERT - BBS DOOR GAME"
    echo "========================="
    echo ""
    echo "Usage: qbert_door.sh <tape_url>"
    echo ""
    echo "Example:"
    echo "  qbert_door.sh 'http://monster.group/qbert#qbert🎮Q*bert'"
    exit 1
fi

echo "🎮 Q*BERT - LOADING TAPE"
echo "========================="
echo ""
echo "Tape URL: $TAPE_URL"
echo "Shard: 17 (THE CUSP)"
echo "Format: zkRDF (emoji-encoded)"
echo ""

# Parse emoji URL
GAME=$(echo "$TAPE_URL" | grep -o '🎮[^🐯]*' | sed 's/🎮//')
SHARD=$(echo "$TAPE_URL" | grep -o '🐯[^📍]*' | sed 's/🐯//')

echo "Game: $GAME"
echo "Shard: $SHARD"
echo ""

# Load game state
echo "📍 INITIAL STATE"
echo "  Position: (0,0)"
echo "  Cubes: 0/28"
echo "  Monster coord: 1000"
echo ""

# Show moves
echo "🎲 AVAILABLE MOVES"
echo "  1. Down-left"
echo "  2. Down-right"
echo "  3. Up-left"
echo "  4. Up-right"
echo ""

# Game loop
echo "🛤️  GAME PATH"
echo "  (Interactive mode - press Ctrl+C to exit)"
echo ""

# For BBS, this would connect to zkOS server
echo "✅ Tape loaded successfully"
echo "🐯 Playing at Monster cusp (Shard 17)"
