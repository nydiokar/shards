#!/usr/bin/env python3
"""
Copy game tapes and assets from data/ to www/ (not gitignored)
"""

import os
import json
import shutil

def copy_game_assets():
    """Copy game tapes and assets to www directory"""
    
    print("📦 COPYING GAME ASSETS TO WWW/")
    print("=" * 70)
    
    # Create www directory
    os.makedirs("www", exist_ok=True)
    os.makedirs("www/tapes", exist_ok=True)
    os.makedirs("www/assets", exist_ok=True)
    
    # Files to copy
    game_files = [
        ("data/game_tapes.json", "www/tapes/game_tapes.json"),
        ("data/game_monster_decomposition.json", "www/tapes/monster_decomposition.json"),
        ("data/qbert_zkrdf_tape.json", "www/tapes/zkrdf_tape.json"),
        ("data/mothers_wisdom.json", "www/tapes/mothers_wisdom.json"),
    ]
    
    copied = 0
    for src, dst in game_files:
        if os.path.exists(src):
            shutil.copy2(src, dst)
            size = os.path.getsize(dst)
            print(f"✓ {src} → {dst} ({size:,} bytes)")
            copied += 1
        else:
            print(f"✗ {src} not found")
    
    # Load and summarize game tapes
    if os.path.exists("www/tapes/game_tapes.json"):
        with open("www/tapes/game_tapes.json", 'r') as f:
            tapes = json.load(f)
        
        print(f"\n📊 GAME TAPES SUMMARY")
        print("-" * 70)
        print(f"Total games: {tapes['total_games']}")
        print(f"Unique shards: {tapes['unique_shards']}")
        
        # Show cusp games
        cusp_games = [t for t in tapes['tapes'] if t['shard'] == 17]
        if cusp_games:
            print(f"\n🐯 CUSP GAMES (Shard 17):")
            for game in cusp_games:
                print(f"  • {game['name']} ({game['year']})")
        
        # Show top shards
        shard_counts = {}
        for tape in tapes['tapes']:
            shard = tape['shard']
            shard_counts[shard] = shard_counts.get(shard, 0) + 1
        
        top_shards = sorted(shard_counts.items(), key=lambda x: x[1], reverse=True)[:5]
        print(f"\nTop 5 shards by game count:")
        for shard, count in top_shards:
            print(f"  Shard {shard:2d}: {count} games")
    
    # Create index
    create_game_index()
    
    print(f"\n✓ Copied {copied} files to www/")
    print(f"✓ Game assets ready for web deployment")

def create_game_index():
    """Create index.html for game browser"""
    
    html = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Monster-bert Game Browser</title>
    <style>
        body {
            font-family: 'Courier New', monospace;
            background: #000;
            color: #0f0;
            padding: 20px;
            max-width: 1200px;
            margin: 0 auto;
        }
        h1 { color: #0ff; text-align: center; }
        .game-grid {
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
            gap: 20px;
            margin-top: 30px;
        }
        .game-card {
            border: 2px solid #0f0;
            padding: 15px;
            background: rgba(0, 255, 0, 0.05);
            cursor: pointer;
            transition: all 0.3s;
        }
        .game-card:hover {
            background: rgba(0, 255, 0, 0.15);
            border-color: #0ff;
            transform: scale(1.05);
        }
        .game-card.cusp {
            border-color: #ff0;
            background: rgba(255, 255, 0, 0.1);
        }
        .game-title { font-size: 18px; font-weight: bold; margin-bottom: 10px; }
        .game-info { font-size: 12px; color: #0ff; }
        .shard { color: #ff0; }
        .cusp-badge {
            display: inline-block;
            background: #ff0;
            color: #000;
            padding: 2px 8px;
            font-size: 10px;
            font-weight: bold;
            margin-left: 10px;
        }
        .play-btn {
            background: #0f0;
            color: #000;
            border: none;
            padding: 10px 20px;
            margin-top: 10px;
            cursor: pointer;
            width: 100%;
            font-family: 'Courier New', monospace;
            font-weight: bold;
        }
        .play-btn:hover {
            background: #0ff;
        }
    </style>
</head>
<body>
    <h1>🐯 Monster-bert Game Browser</h1>
    <p style="text-align: center;">35 Classic Games × 71 Monster Shards</p>
    
    <div style="text-align: center; margin: 20px 0;">
        <button onclick="window.location.href='monsterbert.html'" style="background: #ff0; color: #000; border: none; padding: 15px 30px; font-size: 18px; cursor: pointer; font-family: 'Courier New', monospace; font-weight: bold;">
            🎮 Play Monster-bert BBS
        </button>
    </div>
    
    <div id="game-grid" class="game-grid"></div>

    <script>
        async function loadGames() {
            try {
                const response = await fetch('tapes/game_tapes.json');
                const data = await response.json();
                
                const grid = document.getElementById('game-grid');
                
                data.tapes.forEach(tape => {
                    const card = document.createElement('div');
                    card.className = 'game-card' + (tape.shard === 17 ? ' cusp' : '');
                    
                    card.innerHTML = `
                        <div class="game-title">
                            ${tape.name}
                            ${tape.shard === 17 ? '<span class="cusp-badge">🐯 CUSP</span>' : ''}
                        </div>
                        <div class="game-info">
                            Year: ${tape.year}<br>
                            Genre: ${tape.genre}<br>
                            Publisher: ${tape.publisher}<br>
                            <span class="shard">Shard: ${tape.shard}</span><br>
                            j-invariant: ${tape.j_invariant.toLocaleString()}<br>
                            Hecke: ${tape.hecke_eigenvalue}
                        </div>
                        <button class="play-btn" onclick="playGame('${tape.tape_id}')">
                            ▶ Load Tape
                        </button>
                    `;
                    
                    grid.appendChild(card);
                });
                
                console.log(`Loaded ${data.tapes.length} game tapes`);
            } catch (error) {
                console.error('Failed to load games:', error);
            }
        }
        
        function playGame(tapeId) {
            alert(`Loading ${tapeId}...\\n\\nThis would load the game tape and start the emulator.`);
            // In production, load the specific game tape
        }
        
        loadGames();
    </script>
</body>
</html>
'''
    
    with open('www/index.html', 'w') as f:
        f.write(html)
    
    print("✓ Created www/index.html")

if __name__ == '__main__':
    copy_game_assets()
    
    print("\n" + "=" * 70)
    print("⊢ Game assets copied to www/ (not gitignored) ∎")
    print("\nAccess at:")
    print("  • www/index.html - Game browser")
    print("  • www/monsterbert.html - BBS emulator")
    print("  • www/tapes/ - Game tapes")
