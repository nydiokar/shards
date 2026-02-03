#!/usr/bin/env python3
"""
Visualize Monster Resonance zkPerf proof
Show distribution across 71, 59, 47, 41 shards
"""

import json
import matplotlib.pyplot as plt
import numpy as np

def load_proof(filename='tradewars71_monster_zkproof.json'):
    """Load zkPerf proof"""
    try:
        with open(filename, 'r') as f:
            return json.load(f)
    except:
        return None

def visualize_resonance(proof):
    """Visualize Monster resonance across dimensions"""
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('🎵 Monster Resonance zkPerf Visualization', fontsize=16)
    
    # CPU (71 shards)
    ax1 = axes[0, 0]
    cpu_shards = np.random.rand(71) * 100  # Mock data
    ax1.bar(range(71), cpu_shards, color='#ff6b6b', alpha=0.7)
    ax1.set_title('🐓 CPU Operations (mod 71 - Rooster Crown)')
    ax1.set_xlabel('Shard')
    ax1.set_ylabel('Operations')
    ax1.axhline(y=np.mean(cpu_shards), color='r', linestyle='--', label='Average')
    ax1.legend()
    
    # Memory (59 shards)
    ax2 = axes[0, 1]
    mem_shards = np.random.rand(59) * 1000  # Mock data
    ax2.bar(range(59), mem_shards, color='#4ecdc4', alpha=0.7)
    ax2.set_title('🦅 Memory Addresses (mod 59 - Eagle Crown)')
    ax2.set_xlabel('Shard')
    ax2.set_ylabel('Addresses')
    ax2.axhline(y=np.mean(mem_shards), color='b', linestyle='--', label='Average')
    ax2.legend()
    
    # Registers (47 shards)
    ax3 = axes[1, 0]
    reg_shards = np.random.rand(47) * 10000  # Mock data
    ax3.bar(range(47), reg_shards, color='#95e1d3', alpha=0.7)
    ax3.set_title('👹 Register Values (mod 47 - Monster Crown)')
    ax3.set_xlabel('Shard')
    ax3.set_ylabel('Values')
    ax3.axhline(y=np.mean(reg_shards), color='g', linestyle='--', label='Average')
    ax3.legend()
    
    # Functions (41 shards)
    ax4 = axes[1, 1]
    func_shards = np.random.rand(41) * 50  # Mock data
    ax4.bar(range(41), func_shards, color='#f38181', alpha=0.7)
    ax4.set_title('🔧 Function Labels (mod 41 - Monster Prime)')
    ax4.set_xlabel('Shard')
    ax4.set_ylabel('Calls')
    ax4.axhline(y=np.mean(func_shards), color='m', linestyle='--', label='Average')
    ax4.legend()
    
    plt.tight_layout()
    plt.savefig('monster_resonance_visualization.png', dpi=300, bbox_inches='tight')
    print("💾 Saved to: monster_resonance_visualization.png")
    plt.show()

def print_summary(proof):
    """Print proof summary"""
    print("\n🎵 MONSTER RESONANCE ZKPERF PROOF")
    print("="*70)
    print()
    
    if proof:
        print(f"Resonance Frequency: {proof.get('resonance_frequency', 0):.2f} Hz")
        print(f"Timestamp: {proof.get('timestamp', 0)}")
        print(f"Verified: {proof.get('verified', False)}")
        print()
        
        dims = proof.get('monster_dimensions', {})
        print("Monster Dimensions:")
        print(f"  🐓 CPU (mod 71):       {dims.get('cpu', 0)} shards")
        print(f"  🦅 Memory (mod 59):    {dims.get('memory', 0)} shards")
        print(f"  👹 Registers (mod 47): {dims.get('registers', 0)} shards")
        print(f"  🔧 Functions (mod 41): {dims.get('functions', 0)} shards")
        print(f"  📊 Total:              {dims.get('total', 0)} dimensions")
        print()
        
        print("Commitments (zkProof):")
        print(f"  CPU:      {proof.get('cpu_commitment', 'N/A')[:16]}...")
        print(f"  Memory:   {proof.get('memory_commitment', 'N/A')[:16]}...")
        print(f"  Register: {proof.get('register_commitment', 'N/A')[:16]}...")
        print(f"  Function: {proof.get('function_commitment', 'N/A')[:16]}...")
    else:
        print("No proof file found. Run game first to generate proof.")
    
    print()
    print("🐓🦅👹 The Monster measures all!")

def main():
    print("🎵 Monster Resonance Visualizer")
    print("="*70)
    print()
    
    proof = load_proof()
    print_summary(proof)
    
    print("\nGenerating visualization...")
    visualize_resonance(proof)

if __name__ == "__main__":
    main()
