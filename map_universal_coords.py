#!/usr/bin/env python3
"""
Universal Game Coordinate Mapper
Map all game coordinates to Monster galactic coordinates
"""

import json
import math

# Monster center (Shard 17, the cusp)
MONSTER_CENTER = {
    "shard": 17,
    "radius": 0,
    "angle": 0,
    "dimension": 0
}

MONSTER_DIM = 196883

def game_to_monster_coords(game_name, game_x, game_y, game_z=0):
    """
    Map any game coordinate system to Monster galactic coordinates
    
    Args:
        game_name: Name of the game
        game_x, game_y, game_z: Game-specific coordinates
    
    Returns:
        Monster galactic coordinates (shard, radius, angle, dimension)
    """
    
    # Get game's shard from hash
    shard = hash(game_name) % 71
    
    # Convert to polar coordinates
    radius_2d = math.sqrt(game_x**2 + game_y**2)
    angle = math.degrees(math.atan2(game_y, game_x)) % 360
    
    # Map to Monster radius (0 to 196883)
    # Normalize based on typical game ranges
    max_game_coord = 1000  # Assume max game coordinate
    radius = int((radius_2d / max_game_coord) * MONSTER_DIM)
    radius = min(radius, MONSTER_DIM)
    
    # Map z-coordinate to Monster dimension
    dimension = abs(int(game_z)) % MONSTER_DIM
    
    return {
        "shard": shard,
        "radius": radius,
        "angle": int(angle),
        "dimension": dimension,
        "original": {"x": game_x, "y": game_y, "z": game_z}
    }

def hecke_resonance(coord, prime):
    """Compute Hecke resonance at a position"""
    base = prime * coord["shard"] + prime * prime
    distance_factor = (MONSTER_DIM - coord["radius"]) // 1000
    angle_factor = (180 - coord["angle"]) // 100
    return base + distance_factor + angle_factor

def total_resonance(coord):
    """Total Hecke resonance from all 15 Monster primes"""
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
    return sum(hecke_resonance(coord, p) for p in primes)

# Game-specific coordinate mappings
GAME_MAPPINGS = {
    "Pyramid Hopper": {
        "type": "pyramid",
        "rows": 7,
        "coords": lambda row, col: (col - row/2, row, 0)
    },
    "Circle Eater": {
        "type": "maze",
        "width": 224,
        "height": 288,
        "coords": lambda x, y: (x - 112, y - 144, 0)
    },
    "Platform Theorem": {
        "type": "platformer",
        "width": 256,
        "height": 240,
        "coords": lambda x, y: (x - 128, y - 120, 0)
    },
    "Ring Topology": {
        "type": "platformer",
        "width": 320,
        "height": 224,
        "coords": lambda x, y: (x - 160, y - 112, 0)
    },
    "Block Packing": {
        "type": "puzzle",
        "width": 10,
        "height": 20,
        "coords": lambda x, y: (x * 10, y * 10, 0)
    },
    "Combat Calculus": {
        "type": "fighting",
        "width": 384,
        "height": 224,
        "coords": lambda x, y: (x - 192, y - 112, 0)
    }
}

def map_all_games():
    """Map coordinates for all 35 games"""
    
    print("🌌 UNIVERSAL GAME COORDINATE MAPPER")
    print("=" * 70)
    
    # Load game tapes
    with open('www/tapes/game_tapes.json', 'r') as f:
        tapes = json.load(f)
    
    mapped_games = []
    
    for tape in tapes['tapes']:
        game_name = tape['name']
        shard = tape['shard']
        
        # Example positions for each game
        positions = []
        
        if game_name in GAME_MAPPINGS:
            mapping = GAME_MAPPINGS[game_name]
            
            # Generate sample positions
            if mapping['type'] == 'pyramid':
                # Pyramid: 7 rows
                for row in range(7):
                    for col in range(row + 1):
                        x, y, z = mapping['coords'](row, col)
                        monster_coord = game_to_monster_coords(game_name, x, y, z)
                        positions.append(monster_coord)
            
            elif mapping['type'] == 'maze':
                # Maze: corners + center
                corners = [
                    (0, 0), (mapping['width'], 0),
                    (0, mapping['height']), (mapping['width'], mapping['height']),
                    (mapping['width']//2, mapping['height']//2)
                ]
                for x, y in corners:
                    gx, gy, gz = mapping['coords'](x, y)
                    monster_coord = game_to_monster_coords(game_name, gx, gy, gz)
                    positions.append(monster_coord)
            
            elif mapping['type'] == 'platformer':
                # Platformer: start, middle, end
                for x in [0, mapping['width']//2, mapping['width']]:
                    for y in [0, mapping['height']//2, mapping['height']]:
                        gx, gy, gz = mapping['coords'](x, y)
                        monster_coord = game_to_monster_coords(game_name, gx, gy, gz)
                        positions.append(monster_coord)
        else:
            # Default: center position
            monster_coord = game_to_monster_coords(game_name, 0, 0, 0)
            positions.append(monster_coord)
        
        # Compute average resonance
        avg_resonance = sum(total_resonance(p) for p in positions) / len(positions) if positions else 0
        
        mapped_games.append({
            "name": game_name,
            "shard": shard,
            "positions": len(positions),
            "avg_resonance": int(avg_resonance),
            "sample_coords": positions[:3]  # First 3 positions
        })
        
        marker = "🐯" if shard == 17 else "  "
        print(f"{marker} {game_name:30s} Shard {shard:2d} | {len(positions):3d} coords | Resonance: {int(avg_resonance):6d}")
    
    # Show cusp game details
    print(f"\n🐯 CUSP GAME COORDINATES")
    print("-" * 70)
    
    cusp_game = next((g for g in mapped_games if g['shard'] == 17), None)
    if cusp_game:
        print(f"Game: {cusp_game['name']}")
        print(f"Positions mapped: {cusp_game['positions']}")
        print(f"Average resonance: {cusp_game['avg_resonance']}")
        print(f"\nSample coordinates:")
        for i, coord in enumerate(cusp_game['sample_coords'][:3], 1):
            print(f"  {i}. Radius: {coord['radius']:6d}, Angle: {coord['angle']:3d}°, Dim: {coord['dimension']:6d}")
            print(f"     Original: ({coord['original']['x']:.1f}, {coord['original']['y']:.1f}, {coord['original']['z']:.1f})")
    
    # Save mappings
    output = {
        "total_games": len(mapped_games),
        "monster_center": MONSTER_CENTER,
        "monster_dimension": MONSTER_DIM,
        "games": mapped_games
    }
    
    with open('www/tapes/universal_coords.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"\n✓ Saved to www/tapes/universal_coords.json")
    
    # Statistics
    print(f"\n📊 STATISTICS")
    print("-" * 70)
    total_coords = sum(g['positions'] for g in mapped_games)
    avg_resonance_all = sum(g['avg_resonance'] for g in mapped_games) / len(mapped_games)
    
    print(f"Total coordinates mapped: {total_coords:,}")
    print(f"Average resonance (all games): {int(avg_resonance_all):,}")
    print(f"Games at cusp (Shard 17): {sum(1 for g in mapped_games if g['shard'] == 17)}")
    
    return mapped_games

def create_coordinate_visualizer():
    """Create HTML visualizer for Monster coordinates"""
    
    html = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>Monster Coordinate Visualizer</title>
    <style>
        body {
            margin: 0;
            background: #000;
            color: #0f0;
            font-family: 'Courier New', monospace;
            overflow: hidden;
        }
        #canvas {
            display: block;
            margin: 0 auto;
        }
        #info {
            position: absolute;
            top: 10px;
            left: 10px;
            background: rgba(0, 0, 0, 0.8);
            padding: 10px;
            border: 1px solid #0f0;
        }
        .cusp { color: #ff0; }
    </style>
</head>
<body>
    <canvas id="canvas"></canvas>
    <div id="info">
        <div>Monster Galactic Coordinates</div>
        <div>Center: <span class="cusp">Shard 17 (The Cusp)</span></div>
        <div>Radius: 0 - 196,883</div>
        <div id="hover"></div>
    </div>
    
    <script>
        const canvas = document.getElementById('canvas');
        const ctx = canvas.getContext('2d');
        canvas.width = window.innerWidth;
        canvas.height = window.innerHeight;
        
        const centerX = canvas.width / 2;
        const centerY = canvas.height / 2;
        const scale = Math.min(canvas.width, canvas.height) / 400000;
        
        // Load coordinate data
        fetch('tapes/universal_coords.json')
            .then(r => r.json())
            .then(data => {
                drawGalaxy(data);
            });
        
        function drawGalaxy(data) {
            // Draw Monster center
            ctx.fillStyle = '#ff0';
            ctx.beginPath();
            ctx.arc(centerX, centerY, 10, 0, Math.PI * 2);
            ctx.fill();
            
            ctx.fillStyle = '#ff0';
            ctx.font = '14px Courier New';
            ctx.fillText('Shard 17 (Cusp)', centerX + 15, centerY);
            
            // Draw concentric circles (shards)
            ctx.strokeStyle = '#0f0';
            ctx.globalAlpha = 0.2;
            for (let r = 50000; r <= 196883; r += 50000) {
                ctx.beginPath();
                ctx.arc(centerX, centerY, r * scale, 0, Math.PI * 2);
                ctx.stroke();
            }
            ctx.globalAlpha = 1;
            
            // Draw game positions
            data.games.forEach(game => {
                game.sample_coords.forEach(coord => {
                    const x = centerX + coord.radius * scale * Math.cos(coord.angle * Math.PI / 180);
                    const y = centerY + coord.radius * scale * Math.sin(coord.angle * Math.PI / 180);
                    
                    ctx.fillStyle = game.shard === 17 ? '#ff0' : '#0f0';
                    ctx.beginPath();
                    ctx.arc(x, y, 3, 0, Math.PI * 2);
                    ctx.fill();
                });
            });
            
            console.log(`Rendered ${data.total_games} games`);
        }
    </script>
</body>
</html>
'''
    
    with open('www/galaxy.html', 'w') as f:
        f.write(html)
    
    print("✓ Created www/galaxy.html")

if __name__ == '__main__':
    mapped = map_all_games()
    create_coordinate_visualizer()
    
    print("\n" + "=" * 70)
    print("⊢ All game coordinates mapped to Monster galactic system ∎")
    print("\nEvery game object now has:")
    print("  • Shard (0-70)")
    print("  • Radius (0-196,883)")
    print("  • Angle (0-359°)")
    print("  • Dimension (0-196,882)")
    print("  • Hecke resonance (15 Monster primes)")
    print("\n🐯 All coordinates relative to Shard 17 (the cusp)!")
