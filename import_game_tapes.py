#!/usr/bin/env python3
"""
Import Classic Games as Monster Tapes
Each game maps to a Monster shard (mod 71)
"""

import json
import hashlib
from typing import Dict, List

# Classic games to import as tapes
CLASSIC_GAMES = [
    # 1980s Arcade
    {"name": "Pac-Man", "year": 1980, "genre": "Maze", "publisher": "Namco"},
    {"name": "Donkey Kong", "year": 1981, "genre": "Platform", "publisher": "Nintendo"},
    {"name": "Galaga", "year": 1981, "genre": "Shooter", "publisher": "Namco"},
    {"name": "Ms. Pac-Man", "year": 1982, "genre": "Maze", "publisher": "Midway"},
    {"name": "Dig Dug", "year": 1982, "genre": "Action", "publisher": "Namco"},
    {"name": "Q*bert", "year": 1982, "genre": "Puzzle", "publisher": "Gottlieb"},
    {"name": "Joust", "year": 1982, "genre": "Action", "publisher": "Williams"},
    {"name": "Pole Position", "year": 1982, "genre": "Racing", "publisher": "Namco"},
    {"name": "Dragon's Lair", "year": 1983, "genre": "Interactive", "publisher": "Cinematronics"},
    {"name": "Mario Bros", "year": 1983, "genre": "Platform", "publisher": "Nintendo"},
    {"name": "Spy Hunter", "year": 1983, "genre": "Racing", "publisher": "Bally Midway"},
    {"name": "Gauntlet", "year": 1985, "genre": "Dungeon", "publisher": "Atari"},
    {"name": "Ghosts 'n Goblins", "year": 1985, "genre": "Platform", "publisher": "Capcom"},
    {"name": "Bubble Bobble", "year": 1986, "genre": "Platform", "publisher": "Taito"},
    {"name": "OutRun", "year": 1986, "genre": "Racing", "publisher": "Sega"},
    {"name": "R-Type", "year": 1987, "genre": "Shooter", "publisher": "Irem"},
    {"name": "Street Fighter", "year": 1987, "genre": "Fighting", "publisher": "Capcom"},
    
    # NES Classics
    {"name": "Super Mario Bros", "year": 1985, "genre": "Platform", "publisher": "Nintendo"},
    {"name": "The Legend of Zelda", "year": 1986, "genre": "Adventure", "publisher": "Nintendo"},
    {"name": "Metroid", "year": 1986, "genre": "Action", "publisher": "Nintendo"},
    {"name": "Castlevania", "year": 1986, "genre": "Platform", "publisher": "Konami"},
    {"name": "Mega Man", "year": 1987, "genre": "Platform", "publisher": "Capcom"},
    {"name": "Contra", "year": 1987, "genre": "Shooter", "publisher": "Konami"},
    {"name": "Final Fantasy", "year": 1987, "genre": "RPG", "publisher": "Square"},
    {"name": "Ninja Gaiden", "year": 1988, "genre": "Action", "publisher": "Tecmo"},
    {"name": "Super Mario Bros 3", "year": 1988, "genre": "Platform", "publisher": "Nintendo"},
    {"name": "Tetris", "year": 1989, "genre": "Puzzle", "publisher": "Nintendo"},
    
    # Genesis/SNES Era
    {"name": "Sonic the Hedgehog", "year": 1991, "genre": "Platform", "publisher": "Sega"},
    {"name": "Street Fighter II", "year": 1991, "genre": "Fighting", "publisher": "Capcom"},
    {"name": "Super Mario World", "year": 1990, "genre": "Platform", "publisher": "Nintendo"},
    {"name": "The Legend of Zelda: A Link to the Past", "year": 1991, "genre": "Adventure", "publisher": "Nintendo"},
    {"name": "Super Metroid", "year": 1994, "genre": "Action", "publisher": "Nintendo"},
    {"name": "Chrono Trigger", "year": 1995, "genre": "RPG", "publisher": "Square"},
    {"name": "Earthbound", "year": 1994, "genre": "RPG", "publisher": "Nintendo"},
    
    # Mother's Wisdom (our game)
    {"name": "Mother's Wisdom", "year": 2026, "genre": "Educational", "publisher": "SOLFUNMEME"},
]

def game_to_shard(game: Dict) -> int:
    """Map game to Monster shard (0-70) via hash"""
    game_str = f"{game['name']}:{game['year']}"
    hash_val = int(hashlib.sha256(game_str.encode()).hexdigest(), 16)
    return hash_val % 71

def game_to_tape(game: Dict) -> Dict:
    """Convert game to Monster tape format"""
    shard = game_to_shard(game)
    
    # j-invariant for this shard
    j_inv = 744 + 196884 * shard
    
    # Hecke eigenvalue (using prime 17)
    hecke = 17 * shard + 17 * 17
    
    # Tape data
    tape = {
        "name": game['name'],
        "year": game['year'],
        "genre": game['genre'],
        "publisher": game['publisher'],
        "shard": shard,
        "j_invariant": j_inv,
        "hecke_eigenvalue": hecke,
        "is_cusp": shard == 17,
        "tape_id": f"TAPE-{shard:02d}-{game['name'].replace(' ', '_').upper()}"
    }
    
    return tape

def import_all_games() -> Dict:
    """Import all games as Monster tapes"""
    
    print("🎮 IMPORTING CLASSIC GAMES AS MONSTER TAPES")
    print("=" * 70)
    
    tapes = []
    shard_distribution = {}
    
    for game in CLASSIC_GAMES:
        tape = game_to_tape(game)
        tapes.append(tape)
        
        # Track shard distribution
        shard = tape['shard']
        if shard not in shard_distribution:
            shard_distribution[shard] = []
        shard_distribution[shard].append(tape['name'])
        
        marker = "🐯" if tape['is_cusp'] else "  "
        print(f"{marker} {tape['tape_id']}: {tape['name']} ({tape['year']}) → Shard {shard}")
    
    # Find games on shard 17 (the cusp)
    cusp_games = [t for t in tapes if t['is_cusp']]
    
    print("\n" + "=" * 70)
    print(f"📊 STATISTICS")
    print("=" * 70)
    print(f"Total games: {len(tapes)}")
    print(f"Unique shards: {len(shard_distribution)}")
    print(f"Games on cusp (17): {len(cusp_games)}")
    
    if cusp_games:
        print(f"\n🐯 CUSP GAMES (Shard 17):")
        for game in cusp_games:
            print(f"  • {game['name']} ({game['year']})")
    
    # Shard with most games
    max_shard = max(shard_distribution.items(), key=lambda x: len(x[1]))
    print(f"\nMost populated shard: {max_shard[0]} ({len(max_shard[1])} games)")
    
    result = {
        "tapes": tapes,
        "total_games": len(tapes),
        "unique_shards": len(shard_distribution),
        "cusp_games": cusp_games,
        "shard_distribution": {k: len(v) for k, v in shard_distribution.items()}
    }
    
    # Save tapes
    with open('data/game_tapes.json', 'w') as f:
        json.dump(result, f, indent=2)
    
    print(f"\n✓ Game tapes saved to data/game_tapes.json")
    
    return result

def generate_tape_catalog() -> str:
    """Generate tape catalog in MAME format"""
    
    catalog = []
    catalog.append("# MONSTER GAME TAPE CATALOG")
    catalog.append("# Each game mapped to Monster shard (mod 71)")
    catalog.append("")
    
    for game in CLASSIC_GAMES:
        tape = game_to_tape(game)
        catalog.append(f"## {tape['tape_id']}")
        catalog.append(f"Name: {tape['name']}")
        catalog.append(f"Year: {tape['year']}")
        catalog.append(f"Genre: {tape['genre']}")
        catalog.append(f"Publisher: {tape['publisher']}")
        catalog.append(f"Shard: {tape['shard']}")
        catalog.append(f"j-invariant: {tape['j_invariant']:,}")
        catalog.append(f"Hecke eigenvalue: {tape['hecke_eigenvalue']}")
        if tape['is_cusp']:
            catalog.append("🐯 CUSP GAME")
        catalog.append("")
    
    catalog_text = "\n".join(catalog)
    
    with open('data/GAME_TAPE_CATALOG.md', 'w') as f:
        f.write(catalog_text)
    
    print(f"✓ Tape catalog saved to data/GAME_TAPE_CATALOG.md")
    
    return catalog_text

def create_tape_loader() -> str:
    """Create tape loader script"""
    
    loader = '''#!/usr/bin/env bash
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
jq -r ".tapes[] | select(.shard == $SHARD) | \"\\(.tape_id): \\(.name) (\\(.year))\"" data/game_tapes.json

echo ""
echo "✓ Tape loaded from Shard $SHARD"
'''
    
    with open('load_tape.sh', 'w') as f:
        f.write(loader)
    
    import os
    os.chmod('load_tape.sh', 0o755)
    
    print(f"✓ Tape loader saved to load_tape.sh")
    
    return loader

if __name__ == '__main__':
    # Import all games
    result = import_all_games()
    
    # Generate catalog
    catalog = generate_tape_catalog()
    
    # Create loader
    loader = create_tape_loader()
    
    print("\n" + "=" * 70)
    print("⊢ All classic games imported as Monster tapes ∎")
    print(f"\nLoad a tape: ./load_tape.sh <shard>")
    print(f"Example: ./load_tape.sh 17  # Load cusp games")
