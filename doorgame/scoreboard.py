#!/usr/bin/env python3
"""TradeWars BBS Door Game - ANSI Scoreboard"""

import sys
import time
import json
from datetime import datetime

# ANSI colors
RESET = "\033[0m"
BOLD = "\033[1m"
RED = "\033[31m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
MAGENTA = "\033[35m"
CYAN = "\033[36m"
WHITE = "\033[37m"

def clear_screen():
    print("\033[2J\033[H", end="")

def draw_box(x, y, width, height, title=""):
    """Draw ASCII box"""
    # Top
    print(f"\033[{y};{x}H╔{'═' * (width-2)}╗")
    if title:
        title_pos = x + (width - len(title)) // 2
        print(f"\033[{y};{title_pos}H{BOLD}{CYAN}{title}{RESET}")
    
    # Sides
    for i in range(1, height-1):
        print(f"\033[{y+i};{x}H║{' ' * (width-2)}║")
    
    # Bottom
    print(f"\033[{y+height-1};{x}H╚{'═' * (width-2)}╝")

def draw_scoreboard():
    """Draw main scoreboard"""
    clear_screen()
    
    # Header
    print(f"{BOLD}{CYAN}")
    print("╔═══════════════════════════════════════════════════════════════════════════╗")
    print("║                    🔮⚡ TRADEWARS P2P SCOREBOARD 📻🦞                     ║")
    print("╚═══════════════════════════════════════════════════════════════════════════╝")
    print(RESET)
    
    # Game info
    print(f"{YELLOW}┌─ GAME STATUS ─────────────────────────────────────────────────────────────┐{RESET}")
    print(f"{WHITE}│ Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}                                              │{RESET}")
    print(f"{WHITE}│ Shards: 71 │ Boats: 71 │ Peers: 2 │ Gist: Loaded                        │{RESET}")
    print(f"{YELLOW}└───────────────────────────────────────────────────────────────────────────┘{RESET}")
    print()
    
    # Player scores
    print(f"{GREEN}┌─ PLAYER SCORES ───────────────────────────────────────────────────────────┐{RESET}")
    print(f"{BOLD}{WHITE}│ Rank │ Player ID      │ Turn │ Lobsters │ Boats │ Score  │ Status    │{RESET}")
    print(f"{GREEN}├──────┼────────────────┼──────┼──────────┼───────┼────────┼───────────┤{RESET}")
    
    players = [
        {"rank": 1, "id": "peer-boat-01", "turn": 5, "lobsters": 12, "boats": 71, "score": 8520, "status": "🟢 ONLINE"},
        {"rank": 2, "id": "peer-boat-02", "turn": 5, "lobsters": 10, "boats": 71, "score": 7100, "status": "🟢 ONLINE"},
        {"rank": 3, "id": "peer-boat-03", "turn": 3, "lobsters": 6, "boats": 71, "score": 4260, "status": "🟡 IDLE"},
    ]
    
    for p in players:
        color = GREEN if p["status"] == "🟢 ONLINE" else YELLOW
        print(f"{color}│ {p['rank']:4d} │ {p['id']:14s} │ {p['turn']:4d} │ {p['lobsters']:8d} │ {p['boats']:5d} │ {p['score']:6d} │ {p['status']:9s} │{RESET}")
    
    print(f"{GREEN}└───────────────────────────────────────────────────────────────────────────┘{RESET}")
    print()
    
    # Monster harmonics
    print(f"{MAGENTA}┌─ MONSTER HARMONICS ───────────────────────────────────────────────────────┐{RESET}")
    print(f"{WHITE}│ Shard │ Frequency │ Hecke T_p │ Status                                   │{RESET}")
    print(f"{MAGENTA}├───────┼───────────┼───────────┼──────────────────────────────────────────┤{RESET}")
    
    shards = [
        {"shard": 0, "freq": "7100 Hz", "hecke": "T_2", "status": "✅ Broadcasting"},
        {"shard": 1, "freq": "7110 Hz", "hecke": "T_3", "status": "✅ Broadcasting"},
        {"shard": 70, "freq": "7800 Hz", "hecke": "T_71", "status": "✅ Broadcasting"},
    ]
    
    for s in shards:
        print(f"{MAGENTA}│ {s['shard']:5d} │ {s['freq']:9s} │ {s['hecke']:9s} │ {s['status']:40s} │{RESET}")
    
    print(f"{MAGENTA}└───────────────────────────────────────────────────────────────────────────┘{RESET}")
    print()
    
    # P2P gossip status
    print(f"{CYAN}┌─ P2P GOSSIP STATUS ───────────────────────────────────────────────────────┐{RESET}")
    print(f"{WHITE}│ Convergence: 7 rounds │ Messages: 497 │ Latency: 700ms │ Peers: 2      │{RESET}")
    print(f"{WHITE}│ Gist: https://gist.github.com/jmikedupont2/0855d96fd1ab45d69b36e1223... │{RESET}")
    print(f"{CYAN}└───────────────────────────────────────────────────────────────────────────┘{RESET}")
    print()
    
    # Footer
    print(f"{BOLD}{BLUE}[Q]uit [R]efresh [P]lay [G]ist [H]elp{RESET}")

def animate_scoreboard():
    """Animate scoreboard with live updates"""
    try:
        while True:
            draw_scoreboard()
            time.sleep(2)
    except KeyboardInterrupt:
        print(f"\n\n{GREEN}Thanks for playing TradeWars! 🔮⚡📻🦞{RESET}\n")
        sys.exit(0)

if __name__ == "__main__":
    animate_scoreboard()
