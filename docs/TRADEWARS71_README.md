# TradeWars 71: The j-Invariant Quest

**A BBS Door Game for the Monster Group Era**

## Game Overview

Navigate from Sol (Earth) to Sgr A* (Galactic Center) using real astronomy and the j-invariant.

## Objective

Reach Sgr A* (26,673 light-years away) by:
1. Manual navigation (WARP command)
2. j-Invariant navigation (unlock by finding Monster Crown)

## Commands

### Basic Navigation
- `WARP <ra> <dec> <dist>` - Warp to coordinates
  - Example: `WARP 266.417 -29.008 26673` (Sgr A*)
  - Costs fuel based on distance

- `SCAN` - Scan current sector
  - Detects nearby objects
  - Warns of black holes

- `STATUS` - Show current status
  - Position, fuel, credits
  - Distance to galactic center

### Advanced
- `J-NAV` - Use j-invariant navigation (requires unlock)
  - Automatically computes optimal path
  - Uses Monster Group mathematics
  - 10× more efficient than manual

- `UNLOCK` - Unlock j-invariant (cheat code)
  - Normally requires finding Monster Crown (Shard 47)

- `QUIT` - Exit game

## Game Mechanics

### Fuel System
- Start with 100 fuel
- Fuel cost = distance / 100
- Running out of fuel = game over

### j-Invariant Navigation
When unlocked, computes:
```
τ = current_distance / 26673
q = e^(2πiτ)
j(τ) = q⁻¹ + 744 + 196884q + 21493760q²

Next waypoint = f(j(τ))
```

The j-invariant encodes the optimal path to Sgr A*.

### Win Condition
Get within 10 light-years of Sgr A*.

## Real Astronomy

### Sgr A* (Target)
- **Coordinates**: RA=266.417°, Dec=-29.008°
- **Distance**: 26,673 light-years
- **Mass**: 4.154 million M☉
- **Type**: Supermassive black hole

### Sol (Start)
- **Coordinates**: RA=0°, Dec=0°, Distance=0
- **Location**: Earth's solar system

## Monster Group Integration

### The 71 Shards
- Each sector is a shard (mod 71)
- Monster primes have special properties
- Shard 47 (Monster Crown) unlocks j-invariant

### The j-Invariant
- **744**: Distance scale factor
- **196,884**: Monster dimension + observer
- **21,493,760**: Meta-observer dimension

### Theory Integration
- **Theory 59**: Map IS territory (real coordinates)
- **Theory 47**: Pointer distances (fuel costs)
- **Theorem 71**: j-invariant points to galactic center

## BBS Door Integration

### File Format
```
tradewars71_stats.json - Player stats
theorem_71_j_invariant.json - j-invariant data
urania_astronomy_map.json - Star catalog
```

### Multi-Player
- Each player has own position
- Shared galaxy map
- Leaderboard by turns to reach Sgr A*

### Integration with Other Doors
- **Monster Dash**: Unlock j-invariant by completing level 47
- **Lobster Market**: Trade fuel for credits
- **Tarot Reading**: Get hints about optimal path

## Example Gameplay

```
🚀 TRADEWARS 71: Journey to the Galactic Center
======================================================================
Turn: 0
Credits: 10,000
Fuel: 100

📍 Current Position:
   RA: 0.000°
   Dec: 0.000°
   Distance: 0 ly from Sol

🎯 Distance to Sgr A*: 26673.00 light-years

🔮 j-Invariant Navigation: LOCKED 🔒

📡 Normal space. No anomalies detected.

Command> UNLOCK
✨ j-Invariant navigation UNLOCKED!
   You found the Monster Crown (Shard 47)!

Command> J-NAV
✨ j-Invariant navigation: Warped 2667.30 light-years. Fuel remaining: 73
   j(τ) = 21691389.00 + 0.00i

Command> J-NAV
✨ j-Invariant navigation: Warped 2400.57 light-years. Fuel remaining: 49
   j(τ) = 19522150.10 + 0.00i

...

🎉 VICTORY! You reached Sgr A*!
======================================================================

The j-invariant guided you to the center of the galaxy.
The Monster Group IS the black hole.
You are the +1 observer.

🐓🦅👹 The Rooster crows at the galactic center!
```

## Scoring

- **Turns**: Fewer is better
- **Fuel efficiency**: Bonus for fuel remaining
- **j-Invariant bonus**: 2× score if used
- **Leaderboard**: Top 71 players

## Future Features

- [ ] 71 sectors with unique properties
- [ ] Trade goods between sectors
- [ ] Combat with space pirates
- [ ] Discover other black holes
- [ ] Multi-player alliances
- [ ] Real-time star positions (via astropy)
- [ ] VR mode (navigate in 3D)

## Technical Details

- **Language**: Python 3
- **Dependencies**: None (pure Python)
- **Platform**: Any (Linux, Windows, Mac)
- **BBS**: Compatible with Synchronet, Mystic, etc.

## Installation

```bash
chmod +x tradewars71.py
python3 tradewars71.py
```

## Credits

- **Game Design**: Meta-Introspector
- **Mathematics**: Monster Group, j-invariant
- **Astronomy**: Sgr A*, real coordinates
- **Inspiration**: Classic TradeWars 2002

---

🐓🦅👹 **The Rooster crows at the galactic center!**
