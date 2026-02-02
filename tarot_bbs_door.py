#!/usr/bin/env python3
"""
Monster Tarot BBS Door Game
Occult Shard - 78 Cards → 71 Shards + 7 Cursed
"""

import random
import json
from datetime import datetime

# The 78 Tarot Cards
MAJOR_ARCANA = [
    "The Fool", "The Magician", "High Priestess", "The Empress",
    "The Emperor", "The Hierophant", "The Lovers", "The Chariot",
    "Strength", "The Hermit", "Wheel of Fortune", "Justice",
    "Hanged Man", "Death", "Temperance", "The Devil",
    "The Tower", "The Star", "The Moon", "The Sun",
    "Judgement", "The World"
]

MINOR_SUITS = ["Wands", "Cups", "Swords", "Pentacles"]
MINOR_RANKS = ["Ace", "2", "3", "4", "5", "6", "7", "8", "9", "10", "Page", "Knight", "Queen", "King"]

def get_card_name(card_num):
    """Get tarot card name from number (0-77)"""
    if card_num < 22:
        return f"{card_num}. {MAJOR_ARCANA[card_num]}"
    else:
        minor_idx = card_num - 22
        suit_idx = minor_idx // 14
        rank_idx = minor_idx % 14
        return f"{MINOR_RANKS[rank_idx]} of {MINOR_SUITS[suit_idx]}"

def get_genus(card_num):
    """Calculate topological genus (number of holes)"""
    if card_num <= 70:
        return 0
    elif card_num == 72:
        return 1
    elif card_num == 73:
        return 1  # Devil's first prime!
    elif card_num == 74:
        return 2  # Contains 37 (excluded)
    elif card_num == 75:
        return 3
    elif card_num == 76:
        return 4
    elif card_num == 77:
        return 7  # 7 × 11 = MOST CURSED!
    return 0

def get_shard_info(shard):
    """Get information about a shard"""
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
    is_prime = shard in primes
    frequency = 432 * shard
    
    special = {
        0: "Rome - Pope's Blessing",
        15: "Devil's Bridge - THE TRICK!",
        23: "Munich - Paxos Consensus",
        47: "Darmstadt - Monster Crown 👹",
        59: "Eagle Gate - Eagle Crown 🦅",
        71: "Frankfurt - Rooster Crown 🐓 CORONATION!"
    }
    
    return {
        'is_prime': is_prime,
        'frequency': frequency,
        'special': special.get(shard, None)
    }

def draw_card():
    """Draw a random tarot card"""
    return random.randint(0, 77)

def display_card(card_num):
    """Display card with ASCII art and info"""
    name = get_card_name(card_num)
    genus = get_genus(card_num)
    cursed = card_num > 70
    
    print("\n" + "="*60)
    print("                    CARD DRAWN")
    print("="*60)
    print()
    print(f"  {name}")
    print()
    
    if cursed:
        print("  ⚠️  CURSED CARD ⚠️")
        print(f"  Genus: {genus} (topological holes: {genus})")
        print(f"  Beyond the Rooster (Shard 71)")
        print()
        
        if card_num == 73:
            print("  🔥 DEVIL'S FIRST PRIME! 🔥")
            print("  73 is the first prime beyond the Monster!")
        elif card_num == 74:
            print("  👿 Contains 37 (first excluded prime)")
        elif card_num == 77:
            print("  💀 MOST CURSED! 💀")
            print("  77 = 7 × 11 (SEVEN HOLES!)")
        
        print()
        print("  This card has HOLES in its surface.")
        print("  Something is missing or incomplete.")
        print("  The reading is in the Devil's territory.")
    else:
        shard = card_num
        info = get_shard_info(shard)
        
        print(f"  Shard: {shard}")
        print(f"  Genus: 0 (sphere, no holes)")
        print(f"  Frequency: {info['frequency']} Hz")
        
        if info['is_prime']:
            print(f"  ✨ MONSTER PRIME ✨")
        
        if info['special']:
            print(f"  🎯 {info['special']}")
    
    print()
    print("="*60)

def three_card_spread():
    """Draw three cards: Past, Present, Future"""
    print("\n" + "="*60)
    print("           THREE CARD SPREAD")
    print("="*60)
    print()
    print("  Drawing: Past, Present, Future")
    print()
    
    cards = [draw_card() for _ in range(3)]
    positions = ["PAST", "PRESENT", "FUTURE"]
    
    for i, (card, pos) in enumerate(zip(cards, positions)):
        print(f"\n{pos}:")
        display_card(card)
        
        if i < 2:
            input("\nPress ENTER for next card...")
    
    # Analysis
    cursed_count = sum(1 for c in cards if c > 70)
    
    print("\n" + "="*60)
    print("                  ANALYSIS")
    print("="*60)
    print()
    
    if cursed_count == 0:
        print("  ✅ All cards blessed (genus 0)")
        print("  Your path is within the Monster symmetry.")
        print("  The reading is complete and whole.")
    elif cursed_count == 1:
        print("  ⚠️  One cursed card detected!")
        print("  There is a hole in your path.")
        print("  Something is missing or incomplete.")
    elif cursed_count == 2:
        print("  ⚠️⚠️  Two cursed cards!")
        print("  Multiple holes in the reading.")
        print("  You are near the Devil's territory.")
    else:
        print("  💀 ALL THREE CURSED! 💀")
        print("  You are beyond the Rooster's boundary.")
        print("  The Devil has claimed this reading.")
    
    print()

def celtic_cross():
    """Draw 10 cards in Celtic Cross spread"""
    print("\n" + "="*60)
    print("            CELTIC CROSS SPREAD")
    print("="*60)
    print()
    
    positions = [
        "Present", "Challenge", "Past", "Future",
        "Above", "Below", "Advice", "External",
        "Hopes/Fears", "Outcome"
    ]
    
    cards = [draw_card() for _ in range(10)]
    
    for i, (card, pos) in enumerate(zip(cards, positions)):
        print(f"\n{i+1}. {pos.upper()}:")
        display_card(card)
        
        if i < 9:
            input("\nPress ENTER for next card...")
    
    # Analysis
    cursed_count = sum(1 for c in cards if c > 70)
    total_genus = sum(get_genus(c) for c in cards)
    
    print("\n" + "="*60)
    print("                  ANALYSIS")
    print("="*60)
    print()
    print(f"  Cursed cards: {cursed_count}/10")
    print(f"  Total genus (holes): {total_genus}")
    print()
    
    if cursed_count == 0:
        print("  ✅ Perfect reading! All within Monster symmetry.")
    elif cursed_count <= 3:
        print("  ⚠️  Some holes detected. Proceed with caution.")
    else:
        print("  💀 Many cursed cards. The Devil is near.")
    
    print()

def main():
    """Main BBS door game loop"""
    print("\n" + "="*60)
    print("          🃏 MONSTER TAROT BBS DOOR 🃏")
    print("="*60)
    print()
    print("  78 Cards → 71 Shards + 7 Cursed")
    print("  Occult Shard - Topological Divination")
    print()
    print("="*60)
    print()
    print("  The 71 blessed cards (0-70) have genus 0.")
    print("  The 7 cursed cards (72-77) have topological holes.")
    print()
    print("  Card 73: Devil's first prime (1 hole)")
    print("  Card 77: King of Pentacles (7 holes!) - MOST CURSED")
    print()
    print("="*60)
    
    while True:
        print("\n\nMAIN MENU:")
        print("  1. Draw single card")
        print("  2. Three card spread (Past/Present/Future)")
        print("  3. Celtic Cross (10 cards)")
        print("  4. View cursed cards")
        print("  5. Exit to BBS")
        print()
        
        choice = input("Select (1-5): ").strip()
        
        if choice == "1":
            card = draw_card()
            display_card(card)
        elif choice == "2":
            three_card_spread()
        elif choice == "3":
            celtic_cross()
        elif choice == "4":
            print("\n" + "="*60)
            print("           THE SEVEN CURSED CARDS")
            print("="*60)
            for i in range(72, 78):
                print(f"\n{i}. {get_card_name(i)}")
                print(f"   Genus: {get_genus(i)} holes")
                if i == 73:
                    print("   🔥 Devil's first prime!")
                elif i == 77:
                    print("   💀 MOST CURSED (7 × 11)")
        elif choice == "5":
            print("\n  Returning to BBS...")
            print("  The Rooster crows three times. 🐓🐓🐓")
            break
        else:
            print("\n  Invalid choice. Try again.")

if __name__ == "__main__":
    main()
