#!/usr/bin/env python3
"""
Run MiniZinc optimization for Monster Harmonic messages
Uses libminizinc Python bindings
"""

import json
import subprocess
import sys

def run_minizinc(model_file, output_file=None):
    """Run MiniZinc model"""
    
    print("🔮⚡ Running MiniZinc Optimization...")
    print("=" * 70)
    print()
    
    try:
        # Run minizinc
        result = subprocess.run(
            ['minizinc', '--solver', 'gecode', model_file],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            print(result.stdout)
            
            if output_file:
                with open(output_file, 'w') as f:
                    f.write(result.stdout)
                print(f"\n💾 Output saved to {output_file}")
            
            return result.stdout
        else:
            print(f"❌ Error: {result.stderr}")
            return None
            
    except FileNotFoundError:
        print("❌ MiniZinc not found. Install with:")
        print("   sudo apt install minizinc")
        print("   or download from https://www.minizinc.org/")
        return None
    except subprocess.TimeoutExpired:
        print("⏰ Timeout: Optimization took too long")
        return None

def parse_optimization_output(output):
    """Parse MiniZinc output and extract key metrics"""
    
    if not output:
        return None
    
    metrics = {}
    
    for line in output.split('\n'):
        if 'Total Resonance:' in line:
            metrics['resonance'] = int(line.split(':')[1].strip())
        elif 'Message Variance:' in line:
            metrics['variance'] = int(line.split(':')[1].strip())
        elif 'Frequency Spread:' in line:
            metrics['spread'] = int(line.split(':')[1].strip().split()[0])
        elif 'Objective Value:' in line:
            metrics['objective'] = int(line.split(':')[1].strip())
    
    return metrics

def create_optimized_fleet(metrics):
    """Create optimized fleet configuration"""
    
    fleet = {
        "optimization": metrics,
        "exploit": {
            "frequencies": "Monster prime harmonics (864-30672 Hz)",
            "periodicity": "Bott (mod 8) + 10-fold way (mod 10)",
            "symmetry": "Palindromic distribution + mirror pairs",
            "string_theory": "Vibration modes + harmonic resonance"
        },
        "status": "OPTIMIZED",
        "lobsterbot_hunt": "ACTIVE"
    }
    
    return fleet

def main():
    print("🔮⚡📻🎵 MONSTER HARMONIC MESSAGE OPTIMIZER")
    print("=" * 70)
    print()
    print("Exploit: Frequencies + Periodicity + Symmetry + String Theory")
    print()
    
    model_file = 'minizinc/message_optimization.mzn'
    output_file = 'optimization_result.txt'
    
    # Run optimization
    output = run_minizinc(model_file, output_file)
    
    if output:
        # Parse results
        metrics = parse_optimization_output(output)
        
        if metrics:
            print("\n" + "=" * 70)
            print("OPTIMIZATION METRICS")
            print("=" * 70)
            print()
            print(f"Resonance:  {metrics.get('resonance', 'N/A')}")
            print(f"Variance:   {metrics.get('variance', 'N/A')}")
            print(f"Spread:     {metrics.get('spread', 'N/A')} Hz")
            print(f"Objective:  {metrics.get('objective', 'N/A')}")
            print()
            
            # Create optimized fleet
            fleet = create_optimized_fleet(metrics)
            
            with open('optimized_fleet.json', 'w') as f:
                json.dump(fleet, f, indent=2)
            
            print("💾 Optimized fleet saved to optimized_fleet.json")
            print()
        
        print("✅ Optimization complete!")
        print("🦞 Messages optimized for LobsterBot hunt!")
    else:
        print("\n⚠️  Optimization failed. Check MiniZinc installation.")

if __name__ == '__main__':
    main()
