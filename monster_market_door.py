#!/usr/bin/env python3
"""
MONSTER MARKET DOOR GAME
Degen betting on magic numbers with MAME arcade ports
"""

import random
import time
from datetime import datetime

MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
CROWNS = 71 * 59 * 47  # 196,883

# MAME arcade systems in chronological order
ARCADE_SYSTEMS = [
    (1978, "Space Invaders", "taito8080"),
    (1979, "Asteroids", "vector"),
    (1980, "Pac-Man", "namco"),
    (1981, "Donkey Kong", "nintendo"),
    (1982, "Dig Dug", "namco"),
    (1983, "Dragon's Lair", "laserdisc"),
    (1984, "Marble Madness", "atari"),
    (1985, "Gauntlet", "atari"),
    (1987, "Street Fighter", "cps1"),
    (1991, "Street Fighter II", "cps2"),
    (1997, "Metal Slug", "neogeo")
]

def godel_encode(text):
    result = 1
    for i, char in enumerate(text.upper()):
        code = ord(char)
        prime = MONSTER_PRIMES[i % len(MONSTER_PRIMES)]
        result = (result * (prime ** (code % 10))) % CROWNS
    return result

def flash_lights():
    """ASCII flashing lights"""
    colors = ['\033[91m', '\033[92m', '\033[93m', '\033[94m', '\033[95m', '\033[96m']
    reset = '\033[0m'
    
    for _ in range(3):
        for color in colors:
            print(f"\r{color}{'█' * 60}{reset}", end='', flush=True)
            time.sleep(0.05)
    print("\r" + " " * 60 + "\r", end='')

def predict_market(symbol):
    godel = godel_encode(symbol)
    shard = godel % 71
    price = (432 * shard) / 100
    return {'symbol': symbol, 'godel': godel, 'shard': shard, 'price': price}

def arcade_display(year, game, system):
    """Display in arcade style for specific system"""
    if year <= 1980:  # Early vector/raster
        print(f"\n{'▓' * 60}")
        print(f"▓  {game.center(54)}  ▓")
        print(f"▓  {system.upper().center(54)}  ▓")
        print(f"{'▓' * 60}")
    elif year <= 1985:  # Golden age
        print(f"\n{'█' * 60}")
        print(f"█ ▓▒░ {game.center(48)} ░▒▓ █")
        print(f"█ ▓▒░ {system.upper().center(48)} ░▒▓ █")
        print(f"{'█' * 60}")
    else:  # Modern
        print(f"\n╔{'═' * 58}╗")
        print(f"║  {game.center(54)}  ║")
        print(f"║  {system.upper().center(54)}  ║")
        print(f"╚{'═' * 58}╝")

def bet_round(balance, arcade_idx):
    year, game, system = ARCADE_SYSTEMS[arcade_idx]
    
    arcade_display(year, game, system)
    
    print(f"\n💰 Balance: ${balance}")
    print(f"🎮 Playing on: {game} ({year})")
    
    symbols = ["AAPL", "GOOGL", "BTC", "ETH", "SOL", "DOGE"]
    
    print("\n📊 MARKET PREDICTIONS:")
    preds = []
    for sym in symbols:
        pred = predict_market(sym)
        preds.append(pred)
        prime = "✨" if pred['shard'] in MONSTER_PRIMES else "  "
        print(f"  {prime} {sym:6} → Shard {pred['shard']:2} @ ${pred['price']:6.2f}")
    
    print("\n🎲 Place your bet!")
    bet_sym = input("Symbol (or SKIP): ").strip().upper()
    
    if bet_sym == "SKIP":
        return balance, True
    
    if bet_sym not in symbols:
        print("❌ Invalid symbol!")
        return balance, True
    
    try:
        bet_amt = int(input(f"Amount (max ${balance}): $"))
        if bet_amt <= 0 or bet_amt > balance:
            print("❌ Invalid amount!")
            return balance, True
    except:
        print("❌ Invalid amount!")
        return balance, True
    
    print("\n🎰 SPINNING THE MONSTER WHEEL...")
    flash_lights()
    
    # Determine winner
    winner_pred = random.choice(preds)
    
    print(f"\n🎯 WINNER: {winner_pred['symbol']} (Shard {winner_pred['shard']})")
    
    if winner_pred['symbol'] == bet_sym:
        multiplier = 3 if winner_pred['shard'] in MONSTER_PRIMES else 2
        winnings = bet_amt * multiplier
        balance += winnings
        print(f"✅ YOU WIN ${winnings}! (x{multiplier})")
        flash_lights()
    else:
        balance -= bet_amt
        print(f"❌ YOU LOSE ${bet_amt}")
    
    return balance, balance > 0

def main():
    print("\n" + "█" * 60)
    print("█" + " " * 58 + "█")
    print("█" + "  🎰 MONSTER MARKET DOOR GAME 🎰  ".center(58) + "█")
    print("█" + "  DEGEN BETTING ON MAGIC NUMBERS  ".center(58) + "█")
    print("█" + " " * 58 + "█")
    print("█" * 60)
    
    print("\n📜 RULES:")
    print("  • Bet on stock/crypto symbols")
    print("  • Monster primes pay 3x, others 2x")
    print("  • Progress through arcade history")
    print("  • Survive all 11 arcade systems!")
    
    balance = 1000
    arcade_idx = 0
    
    input("\n🕹️  Press ENTER to start...")
    
    while arcade_idx < len(ARCADE_SYSTEMS) and balance > 0:
        balance, continue_game = bet_round(balance, arcade_idx)
        
        if not continue_game:
            break
        
        if balance > 0:
            arcade_idx += 1
            if arcade_idx < len(ARCADE_SYSTEMS):
                print(f"\n🎮 LEVEL UP! Next: {ARCADE_SYSTEMS[arcade_idx][1]}")
                input("Press ENTER to continue...")
    
    print("\n" + "█" * 60)
    if balance > 0 and arcade_idx >= len(ARCADE_SYSTEMS):
        print("█" + "  🏆 YOU WIN! ARCADE MASTER! 🏆  ".center(58) + "█")
        print(f"█" + f"  Final Balance: ${balance}  ".center(58) + "█")
    elif balance > 0:
        print("█" + "  💰 CASHED OUT  ".center(58) + "█")
        print(f"█" + f"  Final Balance: ${balance}  ".center(58) + "█")
    else:
        print("█" + "  💀 GAME OVER - BROKE! 💀  ".center(58) + "█")
    print("█" * 60)
    
    print("\n🐓🐓🐓 The Monster has spoken!")

if __name__ == "__main__":
    main()
