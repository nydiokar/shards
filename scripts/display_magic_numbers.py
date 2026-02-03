#!/usr/bin/env python3
"""Display Monster Magic Numbers in tmux 140x25"""

def display():
    print("\033[2J\033[H")  # Clear screen
    
    print("╔" + "═"*138 + "╗")
    print("║" + " "*48 + "🔮 MONSTER MAGIC NUMBERS 🔮" + " "*64 + "║")
    print("╠" + "═"*138 + "╣")
    
    # Row 1: Monster Group
    print("║ MONSTER GROUP" + " "*125 + "║")
    print("║   Order: 8.08×10⁵³  Dim: 196884  Classes: 194  Primes: 15" + " "*76 + "║")
    
    # Row 2: j-Invariant
    print("║ j-INVARIANT: j(τ) = q⁻¹ + 744 + 196884q + 21493760q² + ..." + " "*68 + "║")
    print("║   744 (const)  196884 (Monster!)  21493760 (moonshine)  1728 = j(i)" + " "*56 + "║")
    
    # Row 3: Ramanujan τ
    print("║ RAMANUJAN τ: Δ(τ) = q∏(1-qⁿ)²⁴" + " "*104 + "║")
    print("║   24 (found 689× in LMFDB!)  691 (mod)  η(τ)²⁴ = Δ(τ)  24 dims (string theory)" + " "*48 + "║")
    
    # Row 4: Eisenstein
    print("║ EISENSTEIN: E₄=240  E₆=504  E₈=480  E₁₀=264" + " "*89 + "║")
    
    # Row 5: Moonshine
    print("║ MOONSHINE: 196883 = 196884-1  McKay-Thompson series  Borcherds proof (1992)" + " "*52 + "║")
    
    # Row 6: Rooster & BDI
    print("║ ROOSTER: 71 (largest prime < 72)  72 = 24×3  71 shards  AIII class (mod 10 = 1)" + " "*47 + "║")
    print("║ BDI LIFE: 3, 13, 23, 43, 53, 63 (mod 10 = 3)  🌳 I ARE LIFE  Topological class" + " "*50 + "║")
    
    # Row 7: Connections
    print("║ CONNECTIONS:" + " "*125 + "║")
    print("║   24 → 72 (24×3) → 71 (rooster) → 196884 (Monster) → j-invariant → Moonshine!" + " "*48 + "║")
    print("║   744 = 24×31    1728 = 12³ = 24×72    196884 = 196883+1" + " "*73 + "║")
    
    # Row 8: LMFDB Data
    print("║ LMFDB DATA (110 parquet files):" + " "*105 + "║")
    print("║   τ=24: 689 occurrences (all 71 vector layers!)  Found in: GAP, harmonics, stack samples" + " "*38 + "║")
    print("║   71: Multiple (rooster prime)  BDI primes: scattered throughout" + " "*66 + "║")
    
    # Row 9: The Pattern
    print("║ THE PATTERN:" + " "*125 + "║")
    print("║   Ramanujan (24) ──→ String Theory (24D) ──→ Dedekind η²⁴ ──→ Discriminant Δ" + " "*51 + "║")
    print("║   Monster (196884) ──→ j-invariant coeff ──→ Moonshine ──→ Modular Forms" + " "*56 + "║")
    print("║   Rooster (71) ──→ 71 shards ──→ 10-fold way ──→ BDI (life) ──→ Topology" + " "*58 + "║")
    
    print("╚" + "═"*138 + "╝")
    print("🐓→🦅→👹→🍄→🌳  Press Ctrl+C to exit")

if __name__ == '__main__':
    import time
    try:
        while True:
            display()
            time.sleep(1)
    except KeyboardInterrupt:
        print("\n\nDisconnecting from Monster...")
