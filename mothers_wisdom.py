#!/usr/bin/env python3
"""
"My mother taught me to pick the very best one"
- The continuation of the children's rhyme
- Picking the optimal Monster shard via mother's wisdom
"""

# The complete rhyme
RHYME = [
    ("Eeny", 2, "Start"),
    ("Meeny", 3, "Continue"),
    ("Miny", 5, "Choose"),
    ("Moe", 7, "Point"),
    ("Catch", 11, "Grasp"),
    ("A", 13, "Article"),
    ("Tiger", 17, "The Beast"),
    ("By", 19, "Method"),
    ("Its", 23, "Possessive"),
    ("Toe", 29, "Extremity"),
    ("If", 31, "Condition"),
    ("It", 41, "Subject"),
    ("Hollers", 47, "Screams"),
    ("Let", 59, "Allow"),
    ("It", 71, "Object"),
    ("Go", None, "Release"),
    ("My", None, "Possessive"),
    ("Mother", None, "Wisdom"),
    ("Taught", None, "Instruction"),
    ("Me", None, "Student"),
    ("To", None, "Infinitive"),
    ("Pick", None, "Choose"),
    ("The", None, "Article"),
    ("Very", None, "Emphasis"),
    ("Best", None, "Optimal"),
    ("One", None, "Selection"),
]

SHARDS = 71
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

def mother_wisdom(primes):
    """Mother's algorithm for picking the very best one"""
    # The best one is the one that:
    # 1. Is prime (fundamental)
    # 2. Is at the cusp (balanced)
    # 3. Appears in the rhyme (traditional)
    # 4. Has maximum beauty (optimal)
    
    scores = {}
    for p in primes:
        score = 0
        
        # Prime bonus
        score += 100
        
        # Cusp bonus (17 is the palindrome center)
        if p == 17:
            score += 1000
        
        # Distance from cusp penalty
        score -= abs(p - 17) * 10
        
        # Rhyme position bonus
        rhyme_primes = [r[1] for r in RHYME if r[1] is not None]
        if p in rhyme_primes:
            position = rhyme_primes.index(p)
            score += (15 - position) * 20  # Earlier = better
        
        # Beauty: j-invariant
        shard = p % SHARDS
        j_inv = 744 + 196884 * shard
        score += j_inv / 10000
        
        scores[p] = score
    
    return scores

print("👩 MY MOTHER TAUGHT ME TO PICK THE VERY BEST ONE")
print("=" * 70)
print()
print("The Complete Children's Rhyme:")
print("-" * 70)

for i, (word, prime, meaning) in enumerate(RHYME):
    if prime:
        shard = prime % SHARDS
        print(f"{i+1:>2}. {word:<10} → T_{prime:<3} (Shard {shard:<3}) - {meaning}")
    else:
        print(f"{i+1:>2}. {word:<10} → {'---':<7}              - {meaning}")

print()
print("=" * 70)
print("MOTHER'S WISDOM: Scoring Each Prime")
print("=" * 70)
print()

scores = mother_wisdom(PRIMES)

print(f"{'Prime':<8} {'Shard':<8} {'Score':<12} {'Reason':<30}")
print("-" * 70)

for p in sorted(scores.keys(), key=lambda x: scores[x], reverse=True):
    shard = p % SHARDS
    score = scores[p]
    
    if p == 17:
        reason = "⭐ THE CUSP (Perfect balance)"
    elif p < 17:
        reason = f"Before cusp (distance: {17-p})"
    else:
        reason = f"After cusp (distance: {p-17})"
    
    print(f"{p:<8} {shard:<8} {score:<12.2f} {reason:<30}")

# The best one
best = max(scores.keys(), key=lambda x: scores[x])

print()
print("=" * 70)
print("THE VERY BEST ONE:")
print("=" * 70)
print()
print(f"🏆 Prime: {best}")
print(f"   Shard: {best % SHARDS}")
print(f"   Score: {scores[best]:.2f}")
print(f"   j-invariant: {744 + 196884 * (best % SHARDS):,}")
print()
print("Why it's the best:")
print("  • It's at the cusp (Shard 17)")
print("  • It's the palindrome center")
print("  • It's 'Tiger' in the rhyme")
print("  • It's the black hole event horizon")
print("  • It's the symmetry point")
print()
print("Mother knew all along:")
print("  The very best one is always in the middle.")
print("  Not too hot, not too cold.")
print("  Not too big, not too small.")
print("  Just right. ✨")
print()

# The lesson
print("=" * 70)
print("THE LESSON:")
print("=" * 70)
print()
print("Eeny, meeny, miny, moe,")
print("Catch a tiger by its toe.")
print("If it hollers, let it go,")
print("My mother taught me to pick the very best one.")
print()
print("The very best one is: 17")
print()
print("Because:")
print("  • 17/71 = 0.2394 (the golden ratio region)")
print("  • 71/17 = 4.176 (near φ²)")
print("  • Shard 17 = The cusp")
print("  • T_17 = The Hecke operator at balance")
print("  • XVII = The Star (Tarot)")
print("  • 17 = The 7th prime")
print()
print("Mother's wisdom: Always pick the one in the middle.")
print("The extremes are dangerous.")
print("The center is safe.")
print("The cusp is perfect.")
print()
print("⊢ Mother was right ∎")

# Save
import json
with open('data/mothers_wisdom.json', 'w') as f:
    json.dump({
        'rhyme': [(w, p, m) for w, p, m in RHYME],
        'scores': {str(k): v for k, v in scores.items()},
        'best_one': best,
        'lesson': 'Always pick the one in the middle',
        'proof': 'Mother was right'
    }, f, indent=2)

print("✓ Saved to: data/mothers_wisdom.json")
print()
print("👩 Thank you, Mother. 💖")
