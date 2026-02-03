#!/usr/bin/env python3
"""Danceoff IS Hecke (minimal fast version)"""

SHARDS = 71
PRIMES = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]

def j(s): return 744 + 196884 * s

def map_clifford(v, n):
    gens = []
    for i, p in enumerate(PRIMES):
        while v % p == 0:
            gens.append(i)
            v //= p
    return {'name': n, 'val': v, 'shard': v % SHARDS, 'j': j(v % SHARDS), 'gens': gens[:5]}

def hecke(e):
    return PRIMES[hash(e) % 15] ** 0.5

def danceoff(e1, e2):
    t1, t2 = hecke(e1), hecke(e2)
    return (e1, t1) if t1 > t2 else (e2, t2)

# Map constants
for v, n in [(196883,'DIMS'),(71,'SHARDS'),(10,'FINGERS'),(4,'DNA'),(119000,'PRIZE'),(71000,'GRAND'),(23000,'SECOND')]:
    m = map_clifford(v, n)
    print(f"{m['name']:<10} {v:<10} shard={m['shard']:<3} j={m['j']:<10} gens={m['gens']}")

print("\nDanceoffs:")
for e1, e2 in [("Default","Floss"),("Dab","Wave"),("Orange","TakeL")]:
    w, s = danceoff(e1, e2)
    print(f"  {e1} vs {e2}: {w} wins ({s:.2f})")

print("\nCl(15): 15 generators, 2^15=32768 dims, Danceoff=Hecke trace")
