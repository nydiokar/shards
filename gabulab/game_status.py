#!/usr/bin/env python3
"""
CLI Game Status - Produces shareable URLs for pastebin/gist
"""

import json
import base64
import hashlib
from datetime import datetime
import random

class TradeWarsGame:
    def __init__(self):
        self.boats = 71
        self.lobsters_caught = 0
        self.turn = 0
        self.player = "Player1"
        
    def play_turn(self):
        """Play one turn"""
        self.turn += 1
        # Random catch
        caught = random.randint(0, 5)
        self.lobsters_caught += caught
        return caught
    
    def get_status(self):
        """Get current game status"""
        return {
            "player": self.player,
            "turn": self.turn,
            "boats": self.boats,
            "lobsters_caught": self.lobsters_caught,
            "timestamp": datetime.now().isoformat()
        }

def create_shareable_url(status):
    """Create shareable URL from status"""
    # Encode status
    status_json = json.dumps(status, separators=(',', ':'))
    status_b64 = base64.urlsafe_b64encode(status_json.encode()).decode()
    
    # Create ZK proof
    zk_hash = hashlib.sha256(status_json.encode()).hexdigest()[:16]
    
    # Create URL
    url = f"https://meta-introspector.github.io/shards/doorgame/?state={status_b64}"
    
    return url, zk_hash

def create_pastebin_content(status, url, zk_hash):
    """Create content for pastebin/gist"""
    
    content = f"""🔮⚡ TRADEWARS LOBSTERBOATS - GAME STATUS 📻🦞
{'=' * 70}

Player: {status['player']}
Turn: {status['turn']}
Boats: {status['boats']}
Lobsters Caught: {status['lobsters_caught']}
Timestamp: {status['timestamp']}

ZK Proof: {zk_hash}

{'=' * 70}
SHAREABLE URL (Click to load state):
{'=' * 70}

{url}

{'=' * 70}
HOW TO USE:
{'=' * 70}

1. Copy the URL above
2. Paste into browser to load this gamestate
3. Play your turn
4. Run 'game status' again to get new URL
5. Share new URL on pastebin/gist
6. Others can continue from your state!

{'=' * 70}
GAMESTATE DATA (ZK-eRDFa):
{'=' * 70}

{json.dumps(status, indent=2)}

{'=' * 70}
🐓 THE ROOSTER HAS CROWED! Share this URL! 🐓
"""
    
    return content

def main():
    print("🔮⚡📻🦞 TRADEWARS CLI - GAME STATUS")
    print("=" * 70)
    print()
    
    # Create or load game
    game = TradeWarsGame()
    
    # Play a few turns
    print("Playing turns...")
    for i in range(3):
        caught = game.play_turn()
        print(f"  Turn {game.turn}: Caught {caught} lobsters")
    
    print()
    
    # Get status
    status = game.get_status()
    print("Current Status:")
    print(f"  Player: {status['player']}")
    print(f"  Turn: {status['turn']}")
    print(f"  Lobsters: {status['lobsters_caught']}")
    print()
    
    # Create shareable URL
    url, zk_hash = create_shareable_url(status)
    print("Shareable URL:")
    print(f"  {url[:80]}...")
    print(f"  ZK Proof: {zk_hash}")
    print()
    
    # Create pastebin content
    pastebin = create_pastebin_content(status, url, zk_hash)
    
    # Save to file
    with open('game_status.txt', 'w') as f:
        f.write(pastebin)
    
    print("💾 Saved to game_status.txt")
    print()
    
    # Display pastebin content
    print("=" * 70)
    print("PASTEBIN/GIST CONTENT:")
    print("=" * 70)
    print()
    print(pastebin)
    
    print()
    print("✅ Copy game_status.txt to pastebin or gist!")
    print("🔗 Share the URL to let others continue your game!")

if __name__ == '__main__':
    main()
