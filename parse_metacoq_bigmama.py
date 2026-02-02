#!/usr/bin/env python3
"""Parse th-desugar MetaCoq BigMama and map to Monster group"""

import re
from dataclasses import dataclass
from typing import List, Dict

SHARDS = 71

@dataclass
class MetaCoqForm:
    """A MetaCoq syntactic form"""
    name: str
    definition: str
    shard_id: int
    j_invariant: int

def parse_bigmama_forms(file_path: str) -> List[MetaCoqForm]:
    """Extract MetaCoq forms from TestMeta.org"""
    forms = []
    
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Extract BigMama definition
    bigmama_match = re.search(r'type BigMama = (.+)', content)
    if bigmama_match:
        shard = hash("BigMama") % SHARDS
        forms.append(MetaCoqForm(
            "BigMama",
            bigmama_match.group(1),
            shard,
            744 + 196884 * shard
        ))
    
    # Extract data types
    data_pattern = r'data (\w+) =\s+(.+?)(?=\ndata|\ntype|$)'
    for match in re.finditer(data_pattern, content, re.DOTALL):
        name = match.group(1)
        definition = match.group(2).strip()
        shard = hash(name) % SHARDS
        forms.append(MetaCoqForm(
            name,
            definition[:100],  # Truncate
            shard,
            744 + 196884 * shard
        ))
    
    # Extract type aliases
    type_pattern = r'type (\w+) = (.+)'
    for match in re.finditer(type_pattern, content):
        name = match.group(1)
        definition = match.group(2).strip()
        shard = hash(name) % SHARDS
        forms.append(MetaCoqForm(
            name,
            definition,
            shard,
            744 + 196884 * shard
        ))
    
    return forms

def analyze_forms(forms: List[MetaCoqForm]) -> Dict:
    """Analyze MetaCoq forms"""
    shard_counts = [0] * SHARDS
    
    for form in forms:
        shard_counts[form.shard_id] += 1
    
    return {
        'total_forms': len(forms),
        'unique_shards': len([c for c in shard_counts if c > 0]),
        'shard_distribution': shard_counts,
        'forms': [
            {
                'name': f.name,
                'definition': f.definition,
                'shard': f.shard_id,
                'j_invariant': f.j_invariant
            }
            for f in forms
        ]
    }

def main():
    file_path = '/mnt/data1/2023/07/26/th-desugar/Server/MetaCoq/TestMeta.org'
    
    print("MetaCoq BigMama → Monster Group Mapping")
    print("=" * 60)
    
    forms = parse_bigmama_forms(file_path)
    
    print(f"\nExtracted {len(forms)} MetaCoq forms:")
    print()
    
    # Show BigMama
    bigmama = [f for f in forms if f.name == "BigMama"]
    if bigmama:
        b = bigmama[0]
        print(f"BigMama (THE MONSTER):")
        print(f"  Definition: {b.definition}")
        print(f"  Shard: {b.shard_id}")
        print(f"  j-invariant: {b.j_invariant:,}")
        print()
    
    # Show key forms
    key_forms = ["Global_env", "Global_declarations", "Mutual_inductive_body", 
                 "UniversesDecl", "T_", "Nat", "MyString"]
    
    print("Key MetaCoq Forms:")
    for name in key_forms:
        matches = [f for f in forms if f.name == name]
        if matches:
            f = matches[0]
            print(f"  {f.name:25s} → Shard {f.shard_id:2d}, j = {f.j_invariant:,}")
    
    # Analyze
    analysis = analyze_forms(forms)
    
    print(f"\nAnalysis:")
    print(f"  Total forms: {analysis['total_forms']}")
    print(f"  Unique shards: {analysis['unique_shards']}")
    print(f"  Shards with forms: {[i for i, c in enumerate(analysis['shard_distribution']) if c > 0][:10]}")
    
    # Save
    import json
    output = 'data/metacoq_bigmama_monster.json'
    with open(output, 'w') as f:
        json.dump(analysis, f, indent=2)
    
    print(f"\nMapping saved to: {output}")

if __name__ == '__main__':
    main()
