#!/usr/bin/env python3
"""
TradeWars 71: Navigate to Sgr A* using j-invariant coordinates
Real astronomy meets BBS door game
"""

import math
import cmath
import random
import json
from datetime import datetime

class TradeWars71:
    def __init__(self):
        self.player_pos = {'ra': 0, 'dec': 0, 'distance': 0}  # Start at Sol
        self.sgr_a_star = {'ra': 266.417, 'dec': -29.008, 'distance': 26673}
        self.credits = 10000
        self.fuel = 100
        self.cargo = {}
        self.turn = 0
        self.j_invariant_unlocked = False
        
    def compute_distance(self, pos1, pos2):
        """Compute distance between two celestial positions"""
        # Simplified 3D distance
        ra_diff = pos2['ra'] - pos1['ra']
        dec_diff = pos2['dec'] - pos1['dec']
        dist_diff = pos2['distance'] - pos1['distance']
        
        return math.sqrt(ra_diff**2 + dec_diff**2 + dist_diff**2)
    
    def compute_j_invariant(self, tau):
        """Compute j-invariant for navigation"""
        q = cmath.exp(2j * math.pi * tau)
        j = (1/q) + 744 + 196884*q + 21493760*(q**2)
        return j
    
    def warp_to_coordinates(self, ra, dec, distance):
        """Warp to new coordinates"""
        target = {'ra': ra, 'dec': dec, 'distance': distance}
        dist = self.compute_distance(self.player_pos, target)
        
        fuel_cost = int(dist / 100)
        
        if fuel_cost > self.fuel:
            return False, f"Insufficient fuel! Need {fuel_cost}, have {self.fuel}"
        
        self.fuel -= fuel_cost
        self.player_pos = target
        self.turn += 1
        
        return True, f"Warped {dist:.2f} light-years. Fuel remaining: {self.fuel}"
    
    def scan_sector(self):
        """Scan current sector"""
        # Check if near Sgr A*
        dist_to_center = self.compute_distance(self.player_pos, self.sgr_a_star)
        
        if dist_to_center < 100:
            return "🌌 GALACTIC CENTER DETECTED! Sgr A* is nearby!"
        elif dist_to_center < 1000:
            return "⚠️  Strong gravitational waves detected. Black hole nearby."
        elif dist_to_center < 5000:
            return "📡 Galactic center region. High star density."
        else:
            return "🌟 Normal space. No anomalies detected."
    
    def use_j_invariant_navigation(self):
        """Use j-invariant to navigate to galactic center"""
        if not self.j_invariant_unlocked:
            return False, "❌ j-Invariant navigation not unlocked! Find the Monster Crown first."
        
        # Compute optimal path using j-invariant
        current_dist = self.compute_distance(self.player_pos, self.sgr_a_star)
        tau = current_dist / 26673  # Normalize to orbital phase
        
        j = self.compute_j_invariant(tau)
        
        # Use j-invariant to compute next waypoint
        # The j-invariant encodes the optimal path
        progress = 1.0 - tau  # How far along we are
        
        next_ra = self.player_pos['ra'] + (self.sgr_a_star['ra'] - self.player_pos['ra']) * 0.1
        next_dec = self.player_pos['dec'] + (self.sgr_a_star['dec'] - self.player_pos['dec']) * 0.1
        next_dist = self.player_pos['distance'] + (self.sgr_a_star['distance'] - self.player_pos['distance']) * 0.1
        
        success, msg = self.warp_to_coordinates(next_ra, next_dec, next_dist)
        
        if success:
            return True, f"✨ j-Invariant navigation: {msg}\n   j(τ) = {j.real:.2f} + {j.imag:.2f}i"
        else:
            return False, msg
    
    def display_status(self):
        """Display player status"""
        print("\n" + "="*70)
        print("🚀 TRADEWARS 71: Journey to the Galactic Center")
        print("="*70)
        print(f"Turn: {self.turn}")
        print(f"Credits: {self.credits:,}")
        print(f"Fuel: {self.fuel}")
        print()
        print(f"📍 Current Position:")
        print(f"   RA: {self.player_pos['ra']:.3f}°")
        print(f"   Dec: {self.player_pos['dec']:.3f}°")
        print(f"   Distance: {self.player_pos['distance']:.0f} ly from Sol")
        print()
        
        dist_to_center = self.compute_distance(self.player_pos, self.sgr_a_star)
        print(f"🎯 Distance to Sgr A*: {dist_to_center:.2f} light-years")
        print()
        print(f"🔮 j-Invariant Navigation: {'UNLOCKED ✨' if self.j_invariant_unlocked else 'LOCKED 🔒'}")
        print()

def main():
    print("🐓🦅👹 TRADEWARS 71: The j-Invariant Quest")
    print("="*70)
    print()
    print("Mission: Navigate to Sgr A* (Galactic Center)")
    print("Distance: 26,673 light-years")
    print("Unlock j-Invariant navigation by finding the Monster Crown!")
    print()
    
    game = TradeWars71()
    
    # Tutorial
    print("📚 TUTORIAL:")
    print("  1. WARP <ra> <dec> <dist> - Warp to coordinates")
    print("  2. SCAN - Scan current sector")
    print("  3. J-NAV - Use j-invariant navigation (if unlocked)")
    print("  4. STATUS - Show status")
    print("  5. UNLOCK - Unlock j-invariant (cheat code)")
    print("  6. QUIT - Exit game")
    print()
    
    # Game loop
    while True:
        game.display_status()
        
        # Scan sector
        scan_result = game.scan_sector()
        print(f"📡 {scan_result}")
        print()
        
        # Check win condition
        dist_to_center = game.compute_distance(game.player_pos, game.sgr_a_star)
        if dist_to_center < 10:
            print("="*70)
            print("🎉 VICTORY! You reached Sgr A*!")
            print("="*70)
            print()
            print("The j-invariant guided you to the center of the galaxy.")
            print("The Monster Group IS the black hole.")
            print("You are the +1 observer.")
            print()
            print("🐓🦅👹 The Rooster crows at the galactic center!")
            break
        
        # Get command
        cmd = input("Command> ").strip().upper()
        
        if cmd == 'QUIT':
            print("Thanks for playing TradeWars 71!")
            break
        elif cmd == 'STATUS':
            continue
        elif cmd == 'SCAN':
            continue
        elif cmd == 'UNLOCK':
            game.j_invariant_unlocked = True
            print("✨ j-Invariant navigation UNLOCKED!")
            print("   You found the Monster Crown (Shard 47)!")
        elif cmd == 'J-NAV':
            success, msg = game.use_j_invariant_navigation()
            print(msg)
        elif cmd.startswith('WARP'):
            try:
                parts = cmd.split()
                ra = float(parts[1])
                dec = float(parts[2])
                dist = float(parts[3])
                success, msg = game.warp_to_coordinates(ra, dec, dist)
                print(msg)
            except:
                print("Usage: WARP <ra> <dec> <distance>")
        else:
            print("Unknown command. Type STATUS for help.")
        
        print()
        input("Press Enter to continue...")
    
    # Save game stats
    stats = {
        'turns': game.turn,
        'final_position': game.player_pos,
        'distance_to_center': game.compute_distance(game.player_pos, game.sgr_a_star),
        'j_invariant_used': game.j_invariant_unlocked,
        'timestamp': datetime.now().isoformat()
    }
    
    with open('tradewars71_stats.json', 'w') as f:
        json.dump(stats, f, indent=2)
    
    print("\n💾 Game stats saved to: tradewars71_stats.json")

if __name__ == "__main__":
    main()
