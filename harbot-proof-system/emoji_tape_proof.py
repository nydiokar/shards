#!/usr/bin/env python3
"""
Emoji Tape Proof: CPU+GPU+MEM → Monster Group → Gödel Number
The proof IS the tape IS the emoji IS the Monster
"""

import subprocess
import hashlib
import time
from datetime import datetime

# Monster group emoji mapping (71 shards)
MONSTER_EMOJIS = [
    '🔮', '⚡', '📻', '🦞', '🐚', '🦀', '🐙', '🦑', '🐠', '🐟',  # 0-9
    '🐡', '🦈', '🐬', '🐳', '🐋', '🦭', '🦦', '🦫', '🦨', '🦡',  # 10-19
    '🦔', '🦇', '🦅', '🦉', '🦜', '🦚', '🦩', '🦢', '🦃', '🦆',  # 20-29
    '🦤', '🐧', '🐦', '🐤', '🐣', '🐥', '🦋', '🐛', '🐝', '🐞',  # 30-39
    '🦗', '🕷️', '🦂', '🦟', '🦠', '🧬', '🔬', '🔭', '🌌', '🌠',  # 40-49
    '⭐', '✨', '💫', '🌟', '🔥', '💧', '🌊', '🌪️', '⛈️', '🌈',  # 50-59
    '☀️', '🌙', '🪐', '🌍', '🌎', '🌏', '🗿', '🏛️', '⚛️', '🧲',  # 60-69
    '🎯'  # 70
]

# Heat levels to emoji intensity
HEAT_EMOJIS = {
    0: '░',   # 0-10%
    1: '▒',   # 10-25%
    2: '▓',   # 25-50%
    3: '█',   # 50-75%
    4: '🔥',  # 75-90%
    5: '💥'   # 90-100%
}

def get_metrics():
    """Get CPU+MEM+GPU"""
    cpu = float(subprocess.run(['top', '-bn1'], capture_output=True, text=True)
                .stdout.split('Cpu(s)')[1].split('id,')[0].split()[-1])
    cpu = 100 - cpu
    
    mem_line = subprocess.run(['free'], capture_output=True, text=True).stdout.split('\n')[1].split()
    mem = (int(mem_line[2]) / int(mem_line[1])) * 100
    
    try:
        gpu = float(subprocess.run(['nvidia-smi', '--query-gpu=utilization.gpu', '--format=csv,noheader,nounits'],
                                  capture_output=True, text=True, timeout=1).stdout.strip())
    except:
        gpu = 0
    
    return cpu, mem, gpu

def metrics_to_shard(cpu, mem, gpu):
    """Map metrics to Monster shard (0-70)"""
    combined = (cpu * 0.5 + mem * 0.3 + gpu * 0.2)
    return int(combined * 71 / 100) % 71

def metrics_to_heat(cpu, mem, gpu):
    """Map metrics to heat level (0-5)"""
    combined = (cpu * 0.5 + mem * 0.3 + gpu * 0.2)
    if combined < 10: return 0
    if combined < 25: return 1
    if combined < 50: return 2
    if combined < 75: return 3
    if combined < 90: return 4
    return 5

def tape_to_godel(tape):
    """Convert emoji tape to Gödel number"""
    # Each emoji position encodes as prime power
    PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
    godel = 1
    for i, emoji in enumerate(tape[:20]):  # Use first 20 primes
        shard = MONSTER_EMOJIS.index(emoji) if emoji in MONSTER_EMOJIS else 0
        godel *= PRIMES[i] ** shard
    return godel

def draw_tape(tape, width=141):
    """Draw emoji tape (141 width)"""
    print('\033[2J\033[H')  # Clear
    print('╔' + '═' * (width - 2) + '╗')
    print('║' + ' ' * ((width - 40) // 2) + 'EMOJI TAPE PROOF - MONSTER GROUP' + ' ' * ((width - 40) // 2) + '║')
    print('╚' + '═' * (width - 2) + '╝')
    
    # Draw tape in rows
    rows = 37
    for row in range(rows):
        start = row * width
        end = start + width
        line = ''.join(tape[start:end]) if end <= len(tape) else ''.join(tape[start:]) + ' ' * (width - len(tape[start:]))
        print(line)
    
    print()

def main():
    print("Starting Emoji Tape Proof System...")
    print("The proof IS the tape IS the emoji IS the Monster")
    time.sleep(2)
    
    tape = []
    godel_history = []
    
    try:
        while True:
            cpu, mem, gpu = get_metrics()
            shard = metrics_to_shard(cpu, mem, gpu)
            heat = metrics_to_heat(cpu, mem, gpu)
            
            # Encode as emoji
            monster_emoji = MONSTER_EMOJIS[shard]
            heat_emoji = HEAT_EMOJIS[heat]
            
            # Alternate monster and heat
            tape.append(monster_emoji)
            tape.append(heat_emoji)
            
            # Keep tape at 141x37 = 5217 chars
            if len(tape) > 5217:
                tape.pop(0)
                tape.pop(0)
            
            # Compute Gödel number every 10 samples
            if len(tape) % 20 == 0:
                godel = tape_to_godel(tape)
                godel_history.append(godel)
            
            draw_tape(tape)
            print(f"Shard: {shard} {monster_emoji} | Heat: {heat} {heat_emoji} | CPU: {cpu:.1f}% MEM: {mem:.1f}% GPU: {gpu:.1f}%")
            if godel_history:
                print(f"Gödel: {godel_history[-1]}")
            
            time.sleep(0.1)
            
    except KeyboardInterrupt:
        print("\n\nSaving emoji tape witness...")
        
        # Final Gödel number
        final_godel = tape_to_godel(tape)
        
        # Compute tape hash
        tape_str = ''.join(tape)
        tape_hash = hashlib.sha256(tape_str.encode()).hexdigest()
        
        witness = {
            'timestamp': datetime.now().isoformat(),
            'tape_length': len(tape),
            'tape': tape_str,
            'tape_hash': tape_hash,
            'godel_number': str(final_godel),
            'godel_history': [str(g) for g in godel_history[-10:]],
            'monster_shards_used': len(set([e for e in tape if e in MONSTER_EMOJIS]))
        }
        
        import json
        with open('complete_proofs/emoji_tape_witness.json', 'w') as f:
            json.dump(witness, f, indent=2)
        
        # Save visual tape
        with open('complete_proofs/emoji_tape.txt', 'w') as f:
            for i in range(0, len(tape), 141):
                f.write(''.join(tape[i:i+141]) + '\n')
        
        print(f"✓ Tape saved: complete_proofs/emoji_tape.txt")
        print(f"✓ Witness saved: complete_proofs/emoji_tape_witness.json")
        print(f"✓ Tape hash: {tape_hash}")
        print(f"✓ Gödel number: {final_godel}")
        print("\nThe proof IS the tape IS the emoji IS the Monster")
        print("\nQED 🔮⚡📻🦞")

if __name__ == '__main__':
    main()
