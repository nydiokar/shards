#!/usr/bin/env python3
"""
Monster-bert: 30 Maximal Subgroups as Boss Battles
Each maximal subgroup is a boss at specific shards
"""

import json
from typing import Dict, List

# 30 Maximal Subgroups of the Monster Group
MAXIMAL_SUBGROUPS = [
    # Sporadic subgroups (1-6)
    {"id": 1, "name": "Baby Monster", "order": "4,154,781,481,226,426,191,177,580,544,000,000", "shard": 2, "difficulty": 10},
    {"id": 2, "name": "Fischer Fi24", "order": "1,255,205,709,190,661,721,292,800", "shard": 5, "difficulty": 9},
    {"id": 3, "name": "Harada-Norton", "order": "273,030,912,000,000", "shard": 7, "difficulty": 8},
    {"id": 4, "name": "Held", "order": "4,030,387,200", "shard": 11, "difficulty": 7},
    {"id": 5, "name": "Thompson", "order": "90,745,943,887,872,000", "shard": 13, "difficulty": 8},
    {"id": 6, "name": "Janko J4", "order": "86,775,571,046,077,562,880", "shard": 17, "difficulty": 10},
    
    # Alternating groups (7-12)
    {"id": 7, "name": "A12", "order": "479,001,600", "shard": 19, "difficulty": 6},
    {"id": 8, "name": "A11", "order": "39,916,800", "shard": 23, "difficulty": 5},
    {"id": 9, "name": "A10", "order": "1,814,400", "shard": 29, "difficulty": 4},
    {"id": 10, "name": "A9", "order": "181,440", "shard": 31, "difficulty": 3},
    {"id": 11, "name": "A8", "order": "20,160", "shard": 37, "difficulty": 2},
    {"id": 12, "name": "A7", "order": "2,520", "shard": 41, "difficulty": 1},
    
    # Linear groups (13-18)
    {"id": 13, "name": "PSL(2,71)", "order": "182,160", "shard": 43, "difficulty": 5},
    {"id": 14, "name": "PSL(2,59)", "order": "103,740", "shard": 47, "difficulty": 5},
    {"id": 15, "name": "PSL(2,41)", "order": "34,440", "shard": 53, "difficulty": 4},
    {"id": 16, "name": "PSL(2,31)", "order": "14,880", "shard": 59, "difficulty": 4},
    {"id": 17, "name": "PSL(2,29)", "order": "12,180", "shard": 61, "difficulty": 3},
    {"id": 18, "name": "PSL(2,23)", "order": "6,072", "shard": 67, "difficulty": 3},
    
    # Symplectic groups (19-22)
    {"id": 19, "name": "PSp(4,11)", "order": "7,257,600", "shard": 3, "difficulty": 6},
    {"id": 20, "name": "PSp(4,7)", "order": "138,297,600", "shard": 6, "difficulty": 7},
    {"id": 21, "name": "PSp(4,5)", "order": "1,512,000", "shard": 9, "difficulty": 5},
    {"id": 22, "name": "PSp(4,3)", "order": "25,920", "shard": 12, "difficulty": 4},
    
    # Orthogonal groups (23-26)
    {"id": 23, "name": "PΩ+(8,3)", "order": "4,952,179,814,400", "shard": 15, "difficulty": 8},
    {"id": 24, "name": "PΩ-(8,3)", "order": "4,952,179,814,400", "shard": 18, "difficulty": 8},
    {"id": 25, "name": "PΩ(7,3)", "order": "4,585,351,680", "shard": 21, "difficulty": 7},
    {"id": 26, "name": "PΩ+(8,2)", "order": "174,182,400", "shard": 24, "difficulty": 6},
    
    # Exceptional groups (27-30)
    {"id": 27, "name": "G2(5)", "order": "5,859,000,000", "shard": 27, "difficulty": 7},
    {"id": 28, "name": "G2(4)", "order": "251,596,800", "shard": 33, "difficulty": 6},
    {"id": 29, "name": "G2(3)", "order": "4,245,696", "shard": 39, "difficulty": 5},
    {"id": 30, "name": "Suzuki Sz(8)", "order": "29,120", "shard": 45, "difficulty": 4},
]

class Boss:
    """Boss battle based on maximal subgroup"""
    
    def __init__(self, subgroup: Dict):
        self.id = subgroup['id']
        self.name = subgroup['name']
        self.order = subgroup['order']
        self.shard = subgroup['shard']
        self.difficulty = subgroup['difficulty']
        self.hp = self.difficulty * 100
        self.max_hp = self.hp
        self.attacks = self.generate_attacks()
        
    def generate_attacks(self) -> List[str]:
        """Generate boss attacks based on subgroup type"""
        if "Baby Monster" in self.name:
            return ["Sporadic Strike", "Conjugacy Crush", "Involution Impact"]
        elif "Fischer" in self.name:
            return ["Fischer Fission", "Transposition Tornado"]
        elif "PSL" in self.name:
            return ["Linear Lash", "Projective Punch"]
        elif "PSp" in self.name:
            return ["Symplectic Slam", "Bilinear Blast"]
        elif "PΩ" in self.name:
            return ["Orthogonal Obliteration", "Quadratic Quake"]
        elif "G2" in self.name:
            return ["Exceptional Explosion", "Octonion Onslaught"]
        elif self.name.startswith("A"):
            return ["Alternating Assault", "Permutation Pummel"]
        else:
            return ["Subgroup Strike", "Coset Crush"]
    
    def take_damage(self, damage: int) -> bool:
        """Boss takes damage, returns True if defeated"""
        self.hp -= damage
        return self.hp <= 0
    
    def attack_player(self) -> Tuple[str, int]:
        """Boss attacks player"""
        import random
        attack = random.choice(self.attacks)
        damage = self.difficulty * 10 + random.randint(0, 20)
        return attack, damage

class BossLevel:
    """Boss level at specific shard"""
    
    def __init__(self, boss: Boss):
        self.boss = boss
        self.player_hp = 100
        self.player_max_hp = 100
        self.turn = 0
        self.defeated = False
        
    def player_attack(self, move: str) -> int:
        """Player attacks boss with move"""
        damage_map = {
            "down_left": 15,
            "down_right": 20,
            "up_left": 10,
            "up_right": 25,
        }
        
        base_damage = damage_map.get(move, 15)
        # Bonus damage if move matches shard
        if self.boss.shard == 17:  # Cusp bonus
            base_damage *= 2
        
        return base_damage
    
    def battle_turn(self, player_move: str) -> Dict:
        """Execute one turn of battle"""
        self.turn += 1
        
        # Player attacks
        player_damage = self.player_attack(player_move)
        boss_defeated = self.boss.take_damage(player_damage)
        
        if boss_defeated:
            self.defeated = True
            return {
                "turn": self.turn,
                "player_move": player_move,
                "player_damage": player_damage,
                "boss_hp": 0,
                "result": "victory",
                "message": f"🎉 Defeated {self.boss.name}!"
            }
        
        # Boss attacks
        boss_attack, boss_damage = self.boss.attack_player()
        self.player_hp -= boss_damage
        
        if self.player_hp <= 0:
            return {
                "turn": self.turn,
                "player_move": player_move,
                "player_damage": player_damage,
                "boss_attack": boss_attack,
                "boss_damage": boss_damage,
                "player_hp": 0,
                "result": "defeat",
                "message": f"💀 Defeated by {self.boss.name}!"
            }
        
        return {
            "turn": self.turn,
            "player_move": player_move,
            "player_damage": player_damage,
            "boss_hp": self.boss.hp,
            "boss_attack": boss_attack,
            "boss_damage": boss_damage,
            "player_hp": self.player_hp,
            "result": "continue"
        }

def generate_boss_map():
    """Generate map of bosses across 71 shards"""
    
    print("🐯 MONSTER-BERT: 30 MAXIMAL SUBGROUP BOSSES")
    print("=" * 70)
    
    # Create boss map
    boss_map = {}
    for subgroup in MAXIMAL_SUBGROUPS:
        boss = Boss(subgroup)
        boss_map[boss.shard] = boss
    
    print(f"\n📍 BOSS LOCATIONS")
    print("-" * 70)
    
    # Show bosses by difficulty
    by_difficulty = {}
    for boss in boss_map.values():
        if boss.difficulty not in by_difficulty:
            by_difficulty[boss.difficulty] = []
        by_difficulty[boss.difficulty].append(boss)
    
    for diff in sorted(by_difficulty.keys()):
        print(f"\nDifficulty {diff}:")
        for boss in by_difficulty[diff]:
            marker = "🐯" if boss.shard == 17 else "  "
            print(f"{marker} Shard {boss.shard:2d}: {boss.name:20s} (HP: {boss.hp})")
    
    # Special: Janko J4 at the cusp
    print(f"\n🐯 CUSP BOSS (Shard 17)")
    print("-" * 70)
    cusp_boss = boss_map[17]
    print(f"Name: {cusp_boss.name}")
    print(f"Order: {cusp_boss.order}")
    print(f"Difficulty: {cusp_boss.difficulty}/10")
    print(f"HP: {cusp_boss.hp}")
    print(f"Attacks: {', '.join(cusp_boss.attacks)}")
    
    # Demo battle
    print(f"\n⚔️  DEMO BATTLE: Janko J4 at Shard 17")
    print("-" * 70)
    
    level = BossLevel(cusp_boss)
    moves = ["down_left", "down_right", "up_left", "up_right", "down_right"]
    
    for move in moves:
        result = level.battle_turn(move)
        print(f"\nTurn {result['turn']}:")
        print(f"  Player: {move} → {result['player_damage']} damage")
        if 'boss_attack' in result:
            print(f"  Boss: {result['boss_attack']} → {result['boss_damage']} damage")
        print(f"  Boss HP: {result.get('boss_hp', 0)}/{cusp_boss.max_hp}")
        print(f"  Player HP: {result.get('player_hp', 0)}/{level.player_max_hp}")
        
        if result['result'] != 'continue':
            print(f"\n{result['message']}")
            break
    
    # Save boss data
    output = {
        "total_bosses": len(MAXIMAL_SUBGROUPS),
        "bosses": [
            {
                "id": b.id,
                "name": b.name,
                "order": b.order,
                "shard": b.shard,
                "difficulty": b.difficulty,
                "hp": b.hp,
                "attacks": b.attacks
            }
            for b in boss_map.values()
        ],
        "cusp_boss": {
            "name": cusp_boss.name,
            "shard": 17,
            "difficulty": cusp_boss.difficulty,
            "special": "Janko J4 - The Cusp Guardian"
        }
    }
    
    with open('data/monsterbert_bosses.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"\n✓ Boss data saved to data/monsterbert_bosses.json")
    
    return boss_map

if __name__ == '__main__':
    boss_map = generate_boss_map()
    
    print("\n" + "=" * 70)
    print("⊢ 30 Maximal Subgroup bosses added to Monster-bert ∎")
    print("\nBoss categories:")
    print("  • 6 Sporadic groups (Baby Monster, Fischer, etc.)")
    print("  • 6 Alternating groups (A7-A12)")
    print("  • 6 Linear groups (PSL)")
    print("  • 4 Symplectic groups (PSp)")
    print("  • 4 Orthogonal groups (PΩ)")
    print("  • 4 Exceptional groups (G2, Suzuki)")
    print("\n🐯 Janko J4 guards the cusp at Shard 17!")
