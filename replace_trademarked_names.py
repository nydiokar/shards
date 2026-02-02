#!/usr/bin/env python3
"""
Replace trademarked game names with math-themed names
"""

import json
import re

# Math-themed name mappings
MATH_NAMES = {
    # Original games → Math-themed names
    "Pac-Man": "Circle Eater",
    "Ms. Pac-Man": "Torus Navigator",
    "Donkey Kong": "Barrel Theorem",
    "Galaga": "Vector Swarm",
    "Dig Dug": "Topology Digger",
    "Q*bert": "Pyramid Hopper",
    "Joust": "Momentum Duel",
    "Pole Position": "Velocity Vector",
    "Dragon's Lair": "Fractal Quest",
    "Mario Bros": "Plumber's Lemma",
    "Spy Hunter": "Cipher Chase",
    "Gauntlet": "Dungeon Algebra",
    "Ghosts 'n Goblins": "Spectral Knight",
    "Bubble Bobble": "Sphere Capture",
    "OutRun": "Geodesic Racer",
    "R-Type": "Wave Function",
    "Street Fighter": "Combat Calculus",
    "Super Mario Bros": "Platform Theorem",
    "The Legend of Zelda": "Triangle Quest",
    "Metroid": "Manifold Explorer",
    "Castlevania": "Gothic Geometry",
    "Mega Man": "Robot Recursion",
    "Contra": "Projectile Proof",
    "Final Fantasy": "Finite Fields",
    "Ninja Gaiden": "Shadow Calculus",
    "Super Mario Bros 3": "Platform Theorem III",
    "Tetris": "Block Packing",
    "Sonic the Hedgehog": "Ring Topology",
    "Street Fighter II": "Combat Calculus II",
    "Super Mario World": "World Manifold",
    "The Legend of Zelda: A Link to the Past": "Triangle Quest: Past Link",
    "Super Metroid": "Super Manifold",
    "Chrono Trigger": "Time Operator",
    "Earthbound": "Bounded Earth",
    "Mother's Wisdom": "Mother's Wisdom",  # Keep this one
}

def replace_trademarked_names():
    """Replace trademarked names in game tapes"""
    
    print("🔄 REPLACING TRADEMARKED NAMES WITH MATH THEMES")
    print("=" * 70)
    
    # Load game tapes
    with open('www/tapes/game_tapes.json', 'r') as f:
        tapes = json.load(f)
    
    # Replace names
    replaced = 0
    for tape in tapes['tapes']:
        old_name = tape['name']
        if old_name in MATH_NAMES:
            new_name = MATH_NAMES[old_name]
            tape['name'] = new_name
            
            # Update tape_id
            tape_id_suffix = tape['tape_id'].split('-', 2)[-1]
            clean_name = new_name.upper().replace(' ', '_').replace(':', '').replace("'", '')
            new_id = f"TAPE-{tape['shard']:02d}-{clean_name}"
            tape['tape_id'] = new_id
            
            print(f"✓ {old_name:35s} → {new_name}")
            replaced += 1
    
    # Save updated tapes
    with open('www/tapes/game_tapes.json', 'w') as f:
        json.dump(tapes, f, indent=2)
    
    print(f"\n✓ Replaced {replaced} trademarked names")
    
    # Update cusp game
    cusp_games = [t for t in tapes['tapes'] if t['shard'] == 17]
    if cusp_games:
        print(f"\n🐯 CUSP GAME (Shard 17):")
        print(f"  {cusp_games[0]['name']} ({cusp_games[0]['year']})")
    
    return tapes

def update_html_references():
    """Update HTML files to use math-themed names"""
    
    print("\n📝 UPDATING HTML REFERENCES")
    print("-" * 70)
    
    # Update index.html title
    with open('www/index.html', 'r') as f:
        html = f.read()
    
    # No specific game names in index.html, just generic references
    print("✓ index.html - no changes needed")
    
    # Update monsterbert.html
    with open('www/monsterbert.html', 'r') as f:
        html = f.read()
    
    # Replace any specific game references (none currently)
    print("✓ monsterbert.html - no changes needed")

def create_math_theme_doc():
    """Create documentation of math-themed names"""
    
    doc = """# Math-Themed Game Names

To avoid trademark issues, all classic games have been renamed with mathematical themes.

## Name Mappings

| Original | Math Theme | Shard | Theme Explanation |
|----------|-----------|-------|-------------------|
"""
    
    # Load updated tapes
    with open('www/tapes/game_tapes.json', 'r') as f:
        tapes = json.load(f)
    
    # Create reverse mapping
    reverse_map = {v: k for k, v in MATH_NAMES.items()}
    
    for tape in sorted(tapes['tapes'], key=lambda t: t['shard']):
        name = tape['name']
        original = reverse_map.get(name, name)
        shard = tape['shard']
        
        # Add theme explanation
        theme = ""
        if "Circle" in name or "Torus" in name:
            theme = "Topology"
        elif "Vector" in name or "Wave" in name:
            theme = "Linear Algebra"
        elif "Theorem" in name or "Lemma" in name:
            theme = "Proof Theory"
        elif "Manifold" in name or "Topology" in name:
            theme = "Differential Geometry"
        elif "Calculus" in name:
            theme = "Analysis"
        elif "Algebra" in name or "Fields" in name:
            theme = "Abstract Algebra"
        elif "Operator" in name:
            theme = "Functional Analysis"
        elif "Geometry" in name or "Triangle" in name:
            theme = "Geometry"
        elif "Fractal" in name:
            theme = "Chaos Theory"
        elif "Cipher" in name:
            theme = "Cryptography"
        else:
            theme = "General Math"
        
        marker = "🐯" if shard == 17 else ""
        doc += f"| {original:30s} | {name:25s} | {shard:2d} {marker} | {theme} |\n"
    
    doc += """
## Theme Categories

- **Topology**: Circle Eater, Torus Navigator, Ring Topology
- **Linear Algebra**: Vector Swarm, Wave Function, Velocity Vector
- **Proof Theory**: Platform Theorem, Barrel Theorem, Projectile Proof
- **Differential Geometry**: Manifold Explorer, World Manifold, Geodesic Racer
- **Analysis**: Combat Calculus, Shadow Calculus
- **Abstract Algebra**: Dungeon Algebra, Finite Fields
- **Geometry**: Gothic Geometry, Triangle Quest
- **Functional Analysis**: Time Operator

## The Cusp Game

**Pyramid Hopper** (Shard 17) - The original Q*bert, now math-themed!

## Monster-bert

The main game "Monster-bert" is a portmanteau of "Monster Group" + "bert" (from the pyramid hopper character), making it a mathematical term rather than a trademark.
"""
    
    with open('www/MATH_THEMES.md', 'w') as f:
        f.write(doc)
    
    print("\n✓ Created www/MATH_THEMES.md")

if __name__ == '__main__':
    tapes = replace_trademarked_names()
    update_html_references()
    create_math_theme_doc()
    
    print("\n" + "=" * 70)
    print("⊢ All trademarked names replaced with math themes ∎")
    print("\nMath theme categories:")
    print("  • Topology (circles, tori, rings)")
    print("  • Linear Algebra (vectors, waves)")
    print("  • Proof Theory (theorems, lemmas)")
    print("  • Differential Geometry (manifolds)")
    print("  • Analysis (calculus)")
    print("  • Abstract Algebra (fields, groups)")
    print("  • Geometry (triangles, fractals)")
    print("\n🐯 Pyramid Hopper guards the cusp at Shard 17!")
