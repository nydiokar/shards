#!/usr/bin/env python3
"""Timeline of biosemiotics extent: From molecules to cosmos"""

import json

SHARDS = 71
MUSES = ["Calliope","Clio","Erato","Euterpe","Melpomene","Polyhymnia","Terpsichore","Thalia","Urania"]

def q_to_shard(qid): return int(qid[1:]) % SHARDS
def j(s): return 744 + 196884 * s

# Extent of biosemiotics: scales and domains
EXTENT = [
    # Molecular level
    ("DNA", "Q7430", "Genetic code as sign system"),
    ("RNA", "Q11053", "Messenger molecules"),
    ("Protein", "Q8054", "Functional signs"),
    ("Enzyme", "Q8047", "Catalytic interpretation"),
    
    # Cellular level
    ("Cell", "Q7868", "Basic semiotic unit"),
    ("Membrane", "Q14349455", "Boundary interpretation"),
    ("Receptor", "Q33506", "Signal reception"),
    ("Neuron", "Q43054", "Neural signs"),
    
    # Organismal level
    ("Animal", "Q729", "Behavioral signs"),
    ("Plant", "Q756", "Phytosemiotics"),
    ("Fungus", "Q764", "Mycosemiotics"),
    ("Bacteria", "Q10876", "Bacterial communication"),
    
    # Ecological level
    ("Ecosystem", "Q37813", "Ecological signs"),
    ("Symbiosis", "Q179983", "Mutual interpretation"),
    ("Predation", "Q124072", "Predator-prey signs"),
    ("Pollination", "Q79932", "Plant-pollinator signs"),
    
    # Social level
    ("Language", "Q34770", "Human semiotics"),
    ("Culture", "Q11042", "Cultural signs"),
    ("Dance", "Q11639", "Movement signs"),
    ("Music", "Q638", "Auditory signs"),
    
    # Cosmic level
    ("Life", "Q3", "Universal biosemiotics"),
    ("Evolution", "Q4391", "Temporal signs"),
    ("Consciousness", "Q38281", "Self-interpretation"),
    ("Universe", "Q1", "Cosmic semiotics"),
]

def create_extent_timeline():
    print("Biosemiotics Extent: Molecules → Cosmos")
    print("=" * 70)
    print()
    
    # Group by scale
    scales = {
        'Molecular': EXTENT[0:4],
        'Cellular': EXTENT[4:8],
        'Organismal': EXTENT[8:12],
        'Ecological': EXTENT[12:16],
        'Social': EXTENT[16:20],
        'Cosmic': EXTENT[20:24],
    }
    
    all_entries = []
    
    for scale, items in scales.items():
        print(f"\n{scale} Level:")
        print(f"{'Concept':<20} {'Q-ID':<12} {'Shard':<6} {'Muse':<12} {'Description':<30}")
        print("-" * 70)
        
        for concept, qid, desc in items:
            shard = q_to_shard(qid)
            muse = MUSES[shard % 9]
            ji = j(shard)
            
            print(f"{concept:<20} {qid:<12} {shard:<6} {muse:<12} {desc[:30]:<30}")
            
            all_entries.append({
                'scale': scale,
                'concept': concept,
                'wikidata_id': qid,
                'description': desc,
                'shard': shard,
                'muse': muse,
                'j_invariant': ji
            })
    
    # Muse distribution
    print("\n" + "=" * 70)
    print("MUSE DISTRIBUTION BY SCALE:")
    print("=" * 70)
    
    from collections import Counter
    for scale, items in scales.items():
        muses = [MUSES[q_to_shard(qid) % 9] for _, qid, _ in items]
        counts = Counter(muses)
        print(f"\n{scale}:")
        for muse, count in counts.most_common():
            print(f"  {muse:<12}: {count}")
    
    # Key insights
    print("\n" + "=" * 70)
    print("KEY INSIGHTS:")
    print("=" * 70)
    
    # Find which muse dominates each scale
    for scale, items in scales.items():
        muses = [MUSES[q_to_shard(qid) % 9] for _, qid, _ in items]
        dominant = Counter(muses).most_common(1)[0]
        print(f"  {scale:<12}: {dominant[0]} ({dominant[1]} concepts)")
    
    # Special mappings
    print("\n" + "=" * 70)
    print("SPECIAL MAPPINGS:")
    print("=" * 70)
    
    specials = [
        ("Dance", "Q11639"),
        ("Life", "Q3"),
        ("Universe", "Q1"),
        ("Consciousness", "Q38281"),
    ]
    
    for concept, qid in specials:
        shard = q_to_shard(qid)
        muse = MUSES[shard % 9]
        print(f"  {concept:<15} → Shard {shard:<3} → {muse}")
    
    # Save
    output = {
        'extent': all_entries,
        'scales': list(scales.keys()),
        'total_concepts': len(all_entries)
    }
    
    with open('data/biosemiotics_extent.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\n" + "=" * 70)
    print("Biosemiotics extends from molecules to cosmos")
    print("Every level of organization interprets signs")
    print("All mapped to Monster shards via Wikidata")
    print("Saved to: data/biosemiotics_extent.json")

if __name__ == '__main__':
    create_extent_timeline()
