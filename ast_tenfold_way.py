#!/usr/bin/env python3
"""
AST 10-Fold Way: Map AST node types to Bott periodicity classes
Each AST type corresponds to one of 10 topological classes
"""

import ast
import subprocess
from collections import defaultdict

# The 10-Fold Way (Altland-Zirnbauer classification)
TENFOLD_WAY = {
    0: "A (Unitary)",           # No symmetry
    1: "AIII (Chiral unitary)", # Chiral symmetry
    2: "AI (Orthogonal)",       # Time-reversal (T²=+1)
    3: "BDI (Chiral orthogonal)", # T + Chiral
    4: "D (Chiral)",            # Particle-hole (C²=+1)
    5: "DIII (Chiral symplectic)", # C + Chiral
    6: "AII (Symplectic)",      # Time-reversal (T²=-1)
    7: "CII (Chiral symplectic 2)", # T + C + Chiral
    8: "C (Symplectic 2)",      # Particle-hole (C²=-1)
    9: "CI (Orthogonal 2)"      # T + C
}

# Map AST node types to 10-fold classes
AST_TO_TENFOLD = {
    # Class 0: A (Unitary) - Simple expressions
    ast.Constant: 0,
    ast.Name: 0,
    ast.Load: 0,
    ast.Store: 0,
    
    # Class 1: AIII (Chiral) - Binary operations (left/right symmetry)
    ast.BinOp: 1,
    ast.Compare: 1,
    ast.BoolOp: 1,
    
    # Class 2: AI (Orthogonal) - Function definitions (time-reversible)
    ast.FunctionDef: 2,
    ast.Lambda: 2,
    ast.Return: 2,
    
    # Class 3: BDI - Loops (time + iteration symmetry)
    ast.For: 3,
    ast.While: 3,
    ast.Break: 3,
    ast.Continue: 3,
    
    # Class 4: D - Conditionals (particle-hole duality: if/else)
    ast.If: 4,
    ast.IfExp: 4,
    
    # Class 5: DIII - Try/Except (error/success duality + chiral)
    ast.Try: 5,
    ast.ExceptHandler: 5,
    ast.Raise: 5,
    
    # Class 6: AII (Symplectic) - Class definitions (complex structure)
    ast.ClassDef: 6,
    ast.Attribute: 6,
    
    # Class 7: CII - Imports (external/internal duality)
    ast.Import: 7,
    ast.ImportFrom: 7,
    
    # Class 8: C - Assignments (creation/destruction)
    ast.Assign: 8,
    ast.AugAssign: 8,
    ast.AnnAssign: 8,
    
    # Class 9: CI - Calls (function/argument duality)
    ast.Call: 9,
    ast.keyword: 9
}

def get_tenfold_class(node_type):
    """Map AST node type to 10-fold class"""
    return AST_TO_TENFOLD.get(node_type, 0)  # Default to class 0

def analyze_python_file(filepath):
    """Analyze AST and map to 10-fold way"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            code = f.read()
        tree = ast.parse(code)
    except:
        return []
    
    results = []
    
    for node in ast.walk(tree):
        node_type = type(node)
        tenfold_class = get_tenfold_class(node_type)
        
        results.append({
            'node_type': node_type.__name__,
            'tenfold_class': tenfold_class,
            'tenfold_name': TENFOLD_WAY[tenfold_class],
            'file': filepath
        })
    
    return results

def main():
    print("🔟 AST 10-Fold Way: Bott Periodicity in Code")
    print("="*70)
    print()
    
    # Get Python files
    result = subprocess.run(['git', 'ls-files'], capture_output=True, text=True)
    files = [f for f in result.stdout.strip().split('\n') if f.endswith('.py')][:10]
    
    print(f"Analyzing {len(files)} Python files...")
    print()
    
    all_nodes = []
    class_counts = defaultdict(int)
    
    for filepath in files:
        nodes = analyze_python_file(filepath)
        all_nodes.extend(nodes)
        
        for node in nodes:
            class_counts[node['tenfold_class']] += 1
    
    # Show distribution
    print("📊 10-FOLD WAY DISTRIBUTION:")
    print()
    
    total = sum(class_counts.values())
    
    for class_id in range(10):
        count = class_counts[class_id]
        pct = count / total * 100 if total > 0 else 0
        name = TENFOLD_WAY[class_id]
        
        bar = "█" * int(pct / 2)
        
        print(f"  Class {class_id}: {name:25s} | {count:5d} ({pct:5.1f}%) {bar}")
    
    print()
    print(f"Total AST nodes: {total:,}")
    print()
    
    # Show sample mappings
    print("🔍 SAMPLE AST → 10-FOLD MAPPINGS:")
    print()
    
    seen = set()
    for node in all_nodes[:50]:
        key = (node['node_type'], node['tenfold_class'])
        if key not in seen:
            seen.add(key)
            print(f"  {node['node_type']:20s} → Class {node['tenfold_class']}: {node['tenfold_name']}")
    
    print()
    print("🎯 TOPOLOGICAL INTERPRETATION:")
    print()
    print("  Each AST node type has a topological class (mod 10)")
    print("  Classes repeat with Bott periodicity (period 8 → 10 via Monster)")
    print("  Repository structure = Topological quantum code")
    print()
    print("🐓🦅👹 AST is a 10-fold symmetric Monster!")

if __name__ == "__main__":
    main()
