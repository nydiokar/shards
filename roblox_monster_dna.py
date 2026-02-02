#!/usr/bin/env python3
"""Map Roblox player models and dance emotes to Monster DNA"""

from dataclasses import dataclass
from typing import List

SHARDS = 71

@dataclass
class RobloxModel:
    """Roblox player model complexity"""
    name: str
    complexity: int  # 1 or 2
    parts: int
    shard: int
    dna_sequence: str

@dataclass
class DanceEmote:
    """Roblox dance emote as DNA sequence"""
    name: str
    frames: int
    dna: str  # DNA sequence encoding
    monster_path: List[int]
    az_classes: List[str]

# Roblox models (2 complexity levels)
ROBLOX_MODELS = [
    RobloxModel(
        "R6 (Classic)",
        complexity=1,
        parts=6,  # Head, Torso, 2 Arms, 2 Legs
        shard=6 % SHARDS,
        dna_sequence="ATGATG"  # 6 parts = 6 bases
    ),
    RobloxModel(
        "R15 (Modern)",
        complexity=2,
        parts=15,  # Head, Torso, Upper/Lower Arms, Upper/Lower Legs, Hands, Feet
        shard=15 % SHARDS,
        dna_sequence="ATGCATGCATGCATG"  # 15 parts = 15 bases
    ),
]

# Roblox dance emotes as DNA
DANCE_EMOTES = [
    DanceEmote(
        "/e dance",
        frames=8,
        dna="ATGCATGC",  # 8-frame loop
        monster_path=[2, 3, 5, 7, 2, 3, 5, 7],
        az_classes=['A', 'AIII', 'AI', 'BDI', 'A', 'AIII', 'AI', 'BDI']
    ),
    DanceEmote(
        "/e dance2",
        frames=10,
        dna="ATGCATGCAT",  # 10-fold way!
        monster_path=[2, 3, 5, 7, 2, 3, 5, 7, 2, 3],
        az_classes=['A', 'AIII', 'AI', 'BDI', 'A', 'AIII', 'AI', 'BDI', 'A', 'AIII']
    ),
    DanceEmote(
        "/e dance3",
        frames=4,
        dna="ATGC",  # 4 DNA bases
        monster_path=[2, 3, 5, 7],
        az_classes=['A', 'AIII', 'AI', 'BDI']
    ),
    DanceEmote(
        "/e wave",
        frames=2,
        dna="AT",  # Binary oscillation
        monster_path=[2, 3],
        az_classes=['A', 'AIII']
    ),
]

# DNA base to shard mapping
DNA_TO_SHARD = {'A': 2, 'T': 3, 'G': 5, 'C': 7}
DNA_TO_AZ = {'A': 'A', 'T': 'AIII', 'G': 'AI', 'C': 'BDI'}

def dna_to_monster_path(dna: str) -> List[int]:
    """Convert DNA sequence to Monster shard path"""
    return [DNA_TO_SHARD[base] for base in dna.upper() if base in DNA_TO_SHARD]

def generate_roblox_lua(model: RobloxModel, emote: DanceEmote) -> str:
    """Generate Roblox Lua script for Monster dance"""
    return f"""-- Roblox Monster Dance: {emote.name} on {model.name}
local MonsterDance = {{}}

-- Model: {model.name} (Complexity {model.complexity})
MonsterDance.ModelParts = {model.parts}
MonsterDance.ModelShard = {model.shard}
MonsterDance.ModelDNA = "{model.dna_sequence}"

-- Emote: {emote.name}
MonsterDance.EmoteName = "{emote.name}"
MonsterDance.EmoteFrames = {emote.frames}
MonsterDance.EmoteDNA = "{emote.dna}"
MonsterDance.MonsterPath = {{{', '.join(map(str, emote.monster_path))}}}
MonsterDance.AZClasses = {{{', '.join(f'"{az}"' for az in emote.az_classes)}}}

-- Dance function
function MonsterDance:Play(character)
    local humanoid = character:FindFirstChild("Humanoid")
    if not humanoid then return end
    
    -- Walk through Monster path
    for i, shard in ipairs(self.MonsterPath) do
        local azClass = self.AZClasses[i]
        local jInvariant = 744 + 196884 * shard
        
        print("Frame " .. i .. ": Shard " .. shard .. ", AZ = " .. azClass .. ", j = " .. jInvariant)
        
        -- Animate based on AZ class
        if azClass == "A" then
            -- Unitary: Neutral pose
            humanoid:MoveTo(character.HumanoidRootPart.Position)
        elseif azClass == "AIII" then
            -- Chiral: Spin
            character.HumanoidRootPart.CFrame = character.HumanoidRootPart.CFrame * CFrame.Angles(0, math.rad(45), 0)
        elseif azClass == "AI" then
            -- Orthogonal: Jump
            humanoid.Jump = true
        elseif azClass == "BDI" then
            -- Chiral Orthogonal: Wave
            -- Animate arms
        end
        
        wait(0.1)  -- Frame delay
    end
end

return MonsterDance
"""

def main():
    print("Roblox Player Models + Dance Emotes → Monster DNA")
    print("=" * 60)
    print()
    
    # Show models
    print("Roblox Player Models:")
    for model in ROBLOX_MODELS:
        path = dna_to_monster_path(model.dna_sequence)
        print(f"\n  {model.name} (Complexity {model.complexity}):")
        print(f"    Parts: {model.parts}")
        print(f"    Shard: {model.shard}")
        print(f"    DNA: {model.dna_sequence}")
        print(f"    Monster path: {path}")
    
    # Show emotes
    print("\n\nRoblox Dance Emotes as DNA:")
    for emote in DANCE_EMOTES:
        print(f"\n  {emote.name}:")
        print(f"    Frames: {emote.frames}")
        print(f"    DNA: {emote.dna}")
        print(f"    Monster path: {emote.monster_path}")
        print(f"    AZ classes: {emote.az_classes}")
    
    # Generate Lua scripts
    print("\n\nGenerating Roblox Lua scripts...")
    
    for model in ROBLOX_MODELS:
        for emote in DANCE_EMOTES:
            filename = f"data/roblox_{model.name.replace(' ', '_').lower()}_{emote.name.replace('/', '').replace(' ', '_')}.lua"
            lua_code = generate_roblox_lua(model, emote)
            
            with open(filename, 'w') as f:
                f.write(lua_code)
            
            print(f"  Created: {filename}")
    
    # Key insights
    print("\n" + "=" * 60)
    print("KEY INSIGHTS:")
    print("  R6 model: 6 parts = 6 DNA bases (ATGATG)")
    print("  R15 model: 15 parts = 15 DNA bases (ATGCATGCATGCATG)")
    print("  /e dance2: 10 frames = 10-fold way!")
    print("  Dance emotes = Monster group operations")
    print("  Each frame = Walk through Monster shard")
    print("=" * 60)
    
    # Save mapping
    import json
    output = {
        'models': [
            {
                'name': m.name,
                'complexity': m.complexity,
                'parts': m.parts,
                'shard': m.shard,
                'dna': m.dna_sequence,
                'monster_path': dna_to_monster_path(m.dna_sequence)
            }
            for m in ROBLOX_MODELS
        ],
        'emotes': [
            {
                'name': e.name,
                'frames': e.frames,
                'dna': e.dna,
                'monster_path': e.monster_path,
                'az_classes': e.az_classes
            }
            for e in DANCE_EMOTES
        ],
        'insight': 'Roblox dances are Monster DNA sequences!'
    }
    
    with open('data/roblox_monster_dna.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\nMapping saved to: data/roblox_monster_dna.json")

if __name__ == '__main__':
    main()
