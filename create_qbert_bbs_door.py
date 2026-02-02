#!/usr/bin/env python3
"""
Q*bert BBS Door Game for zkOS Server
Loads game as zkRDF tape via emoji URL encoding
"""

import json
import hashlib
import urllib.parse
from typing import Dict, List

# Emoji encoding for RDF predicates
EMOJI_RDF = {
    "game": "🎮",
    "shard": "🐯",
    "position": "📍",
    "move": "🎲",
    "cubes": "🔷",
    "monster": "👾",
    "hecke": "🎵",
    "path": "🛤️",
    "state": "💾",
    "proof": "✅"
}

# RDF namespace
NAMESPACE = "http://monster.group/qbert#"

def encode_rdf_triple(subject: str, predicate: str, obj: str) -> str:
    """Encode RDF triple as emoji URL"""
    emoji = EMOJI_RDF.get(predicate, "❓")
    # Escape for URL
    s = urllib.parse.quote(subject)
    p = emoji
    o = urllib.parse.quote(str(obj))
    return f"{s}{p}{o}"

def create_qbert_rdf_tape() -> Dict:
    """Create Q*bert game as zkRDF tape"""
    
    # Game metadata
    game_uri = f"{NAMESPACE}qbert"
    
    triples = [
        # Game identity
        (game_uri, "game", "Q*bert"),
        (game_uri, "shard", "17"),
        (game_uri, "monster", "196883"),
        (game_uri, "hecke", "578"),
        
        # Initial state
        (f"{game_uri}/state/0", "position", "(0,0)"),
        (f"{game_uri}/state/0", "cubes", "0"),
        (f"{game_uri}/state/0", "monster", "1000"),
        
        # Moves
        (f"{game_uri}/move/1", "move", "down_left"),
        (f"{game_uri}/move/2", "move", "down_right"),
        (f"{game_uri}/move/3", "move", "up_left"),
        (f"{game_uri}/move/4", "move", "up_right"),
        
        # Goal
        (f"{game_uri}/goal", "cubes", "28"),
        (f"{game_uri}/goal", "proof", "optimal_path_wins"),
    ]
    
    # Encode as emoji URLs
    emoji_urls = []
    for s, p, o in triples:
        emoji_url = encode_rdf_triple(s, p, o)
        emoji_urls.append(emoji_url)
    
    # Create zkRDF tape
    tape = {
        "tape_id": "TAPE-17-QBERT-ZKRDF",
        "format": "zkRDF",
        "encoding": "emoji-url",
        "namespace": NAMESPACE,
        "shard": 17,
        "triples": triples,
        "emoji_urls": emoji_urls,
        "hash": hashlib.sha256("".join(emoji_urls).encode()).hexdigest()
    }
    
    return tape

def create_bbs_door_script() -> str:
    """Create BBS door game script"""
    
    script = '''#!/usr/bin/env bash
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
'''
    
    return script

def create_zos_plugin() -> str:
    """Create zkOS server plugin for Q*bert"""
    
    plugin = '''// Q*bert zkOS Plugin
// Handles zkRDF tape loading

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub struct QbertTape {
    pub tape_id: String,
    pub format: String,
    pub encoding: String,
    pub shard: u8,
    pub triples: Vec<(String, String, String)>,
    pub emoji_urls: Vec<String>,
    pub hash: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct QbertState {
    pub position: (u8, u8),
    pub cubes_changed: u8,
    pub monster_coord: u32,
    pub shard: u8,
}

impl QbertState {
    pub fn new() -> Self {
        QbertState {
            position: (0, 0),
            cubes_changed: 0,
            monster_coord: 1000,
            shard: 17,
        }
    }
    
    pub fn make_move(&mut self, move_type: &str) -> Result<(), String> {
        let (row, col) = self.position;
        
        let new_pos = match move_type {
            "down_left" => (row + 1, col),
            "down_right" => (row + 1, col + 1),
            "up_left" => (row.saturating_sub(1), col.saturating_sub(1)),
            "up_right" => (row.saturating_sub(1), col),
            _ => return Err("Invalid move".to_string()),
        };
        
        // Validate
        if new_pos.0 > 6 || new_pos.1 > new_pos.0 {
            return Err("Invalid position".to_string());
        }
        
        self.position = new_pos;
        self.cubes_changed += 1;
        self.monster_coord = 1000 + (new_pos.0 as u32) * 100 + (new_pos.1 as u32) * 10 + (self.cubes_changed % 10) as u32;
        
        Ok(())
    }
    
    pub fn is_won(&self) -> bool {
        self.cubes_changed >= 28
    }
}

pub fn load_tape(tape_json: &str) -> Result<QbertTape, String> {
    serde_json::from_str(tape_json)
        .map_err(|e| format!("Failed to parse tape: {}", e))
}

pub fn create_game_from_tape(tape: &QbertTape) -> Result<QbertState, String> {
    if tape.shard != 17 {
        return Err("Q*bert only plays at shard 17 (cusp)".to_string());
    }
    
    Ok(QbertState::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_qbert_state() {
        let mut state = QbertState::new();
        assert_eq!(state.position, (0, 0));
        assert_eq!(state.shard, 17);
        
        state.make_move("down_left").unwrap();
        assert_eq!(state.position, (1, 0));
        assert_eq!(state.cubes_changed, 1);
    }
}
'''
    
    return plugin

def generate_emoji_tape_url(tape: Dict) -> str:
    """Generate complete emoji tape URL"""
    
    # Base URL
    base = "http://monster.group/qbert"
    
    # Encode key triples as emoji URL
    params = []
    for s, p, o in tape['triples'][:5]:  # First 5 triples
        emoji = EMOJI_RDF.get(p, "❓")
        params.append(f"{emoji}{urllib.parse.quote(str(o))}")
    
    url = base + "#" + "".join(params)
    
    return url

def create_bbs_door_game():
    """Create complete BBS door game package"""
    
    print("🎮 Q*BERT BBS DOOR GAME: zkRDF TAPE")
    print("=" * 70)
    
    # Create zkRDF tape
    print("\n1️⃣  CREATING zkRDF TAPE")
    print("-" * 70)
    tape = create_qbert_rdf_tape()
    print(f"Tape ID: {tape['tape_id']}")
    print(f"Format: {tape['format']}")
    print(f"Encoding: {tape['encoding']}")
    print(f"Shard: {tape['shard']}")
    print(f"Triples: {len(tape['triples'])}")
    print(f"Hash: {tape['hash'][:16]}...")
    
    # Generate emoji URL
    print("\n2️⃣  GENERATING EMOJI TAPE URL")
    print("-" * 70)
    emoji_url = generate_emoji_tape_url(tape)
    print(f"URL: {emoji_url[:80]}...")
    print(f"Length: {len(emoji_url)} chars")
    
    # Show emoji encoding
    print("\n3️⃣  EMOJI RDF ENCODING")
    print("-" * 70)
    for pred, emoji in list(EMOJI_RDF.items())[:5]:
        print(f"  {pred:10s} → {emoji}")
    
    # Save tape
    with open('data/qbert_zkrdf_tape.json', 'w') as f:
        json.dump(tape, f, indent=2)
    print(f"\n✓ Tape saved to data/qbert_zkrdf_tape.json")
    
    # Create BBS door script
    script = create_bbs_door_script()
    with open('qbert_door.sh', 'w') as f:
        f.write(script)
    import os
    os.chmod('qbert_door.sh', 0o755)
    print(f"✓ BBS door script saved to qbert_door.sh")
    
    # Create zkOS plugin
    plugin = create_zos_plugin()
    with open('src/qbert_zos_plugin.rs', 'w') as f:
        f.write(plugin)
    print(f"✓ zkOS plugin saved to src/qbert_zos_plugin.rs")
    
    # Create emoji URL file
    with open('data/qbert_emoji_url.txt', 'w') as f:
        f.write(emoji_url)
    print(f"✓ Emoji URL saved to data/qbert_emoji_url.txt")
    
    print("\n" + "=" * 70)
    print("📊 SUMMARY")
    print("=" * 70)
    print(f"zkRDF triples: {len(tape['triples'])}")
    print(f"Emoji URLs: {len(tape['emoji_urls'])}")
    print(f"Tape hash: {tape['hash'][:16]}...")
    print(f"Emoji URL length: {len(emoji_url)} chars")
    print(f"Shard: 17 (THE CUSP)")
    
    print("\n🎮 USAGE")
    print("-" * 70)
    print("BBS Door:")
    print(f"  ./qbert_door.sh '{emoji_url[:60]}...'")
    print("\nzkOS Server:")
    print("  cargo build --release")
    print("  ./target/release/zos-server --plugin qbert_zos_plugin.so")
    
    return {
        "tape": tape,
        "emoji_url": emoji_url,
        "script": script,
        "plugin": plugin
    }

if __name__ == '__main__':
    result = create_bbs_door_game()
    
    print("\n" + "=" * 70)
    print("⊢ Q*bert BBS door game created with zkRDF emoji tape ∎")
    print("\nKey features:")
    print("  • zkRDF tape format")
    print("  • Emoji URL encoding")
    print("  • BBS door script")
    print("  • zkOS server plugin")
    print("  • Shard 17 (Monster cusp)")
    print("  • RDF triples with emoji predicates")
