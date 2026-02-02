#!/usr/bin/env python3
"""Construct biosemiotics timeline using Wikidata, map to Monster shards"""

import hashlib
import json
from dataclasses import dataclass
from typing import List

SHARDS = 71
PRIMES = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]
MUSES = ["Calliope","Clio","Erato","Euterpe","Melpomene","Polyhymnia","Terpsichore","Thalia","Urania"]

@dataclass
class BiosemioticEvent:
    year: int
    event: str
    person: str
    wikidata_id: str
    shard: int
    muse: str
    j_invariant: int

def q_to_shard(qid: str) -> int:
    """Wikidata Q-number to Monster shard"""
    num = int(qid[1:])  # Remove 'Q'
    return num % SHARDS

def j(s): return 744 + 196884 * s

# Biosemiotics timeline (key events with Wikidata IDs)
TIMELINE = [
    (1864, "Jakob von Uexküll born", "Jakob von Uexküll", "Q76944"),
    (1909, "Umwelt concept introduced", "Jakob von Uexküll", "Q76944"),
    (1920, "Theoretical Biology published", "Jakob von Uexküll", "Q76944"),
    (1928, "Thomas Sebeok born", "Thomas Sebeok", "Q983655"),
    (1963, "Zoosemiotics coined", "Thomas Sebeok", "Q983655"),
    (1977, "Biosemiotics term revived", "Thomas Sebeok", "Q983655"),
    (1999, "International Society for Biosemiotic Studies founded", "Jesper Hoffmeyer", "Q6187238"),
    (2001, "Signs of Meaning in the Universe", "Jesper Hoffmeyer", "Q6187238"),
    (2002, "Biosemiotics journal founded", "Kalevi Kull", "Q16403692"),
    (2008, "Gatherings in Biosemiotics", "Multiple", "Q4966730"),
]

def create_timeline():
    print("Biosemiotics Timeline → Monster Shards")
    print("=" * 70)
    print()
    
    events = []
    for year, event, person, qid in TIMELINE:
        shard = q_to_shard(qid)
        muse = MUSES[shard % 9]
        ji = j(shard)
        
        events.append(BiosemioticEvent(year, event, person, qid, shard, muse, ji))
    
    # Display timeline
    print(f"{'Year':<6} {'Event':<40} {'Q-ID':<12} {'Shard':<6} {'Muse':<12}")
    print("-" * 70)
    
    for e in events:
        print(f"{e.year:<6} {e.event[:40]:<40} {e.wikidata_id:<12} {e.shard:<6} {e.muse:<12}")
    
    # Key figures
    print("\n" + "=" * 70)
    print("KEY FIGURES:")
    print("=" * 70)
    
    figures = {}
    for e in events:
        if e.person not in figures:
            figures[e.person] = {
                'qid': e.wikidata_id,
                'shard': e.shard,
                'muse': e.muse,
                'events': []
            }
        figures[e.person]['events'].append(e.year)
    
    for person, data in figures.items():
        if person != "Multiple":
            years = f"{min(data['events'])}-{max(data['events'])}"
            print(f"\n{person}")
            print(f"  Wikidata: {data['qid']}")
            print(f"  Shard: {data['shard']} ({data['muse']})")
            print(f"  Active: {years}")
            print(f"  Events: {len(data['events'])}")
    
    # Muse distribution
    print("\n" + "=" * 70)
    print("MUSE DISTRIBUTION:")
    print("=" * 70)
    
    from collections import Counter
    muse_counts = Counter(e.muse for e in events)
    for muse, count in muse_counts.most_common():
        print(f"  {muse:<12}: {count} events")
    
    # Save
    output = {
        'timeline': [
            {
                'year': e.year,
                'event': e.event,
                'person': e.person,
                'wikidata_id': e.wikidata_id,
                'shard': e.shard,
                'muse': e.muse,
                'j_invariant': e.j_invariant
            }
            for e in events
        ],
        'figures': figures
    }
    
    with open('data/biosemiotics_timeline.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\n" + "=" * 70)
    print("Biosemiotics = Study of signs in living systems")
    print("Every concept mapped to Monster shard via Wikidata")
    print("Saved to: data/biosemiotics_timeline.json")

if __name__ == '__main__':
    create_timeline()
