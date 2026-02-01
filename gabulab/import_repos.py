#!/usr/bin/env python3
"""
Import AI Agent Repos and Flag SUS Harmonics
Read repos with Hecke operators T_2 through T_71
Flag anything > 71 as SUS (quarantined like Bot 72)
"""

import os
import json
import hashlib
from pathlib import Path

# Monster Hecke Operators T_2 through T_71
HECKE_OPERATORS = {
    2: "T_2",   3: "T_3",   5: "T_5",   7: "T_7",   11: "T_11",
    13: "T_13", 17: "T_17", 19: "T_19", 23: "T_23", 29: "T_29",
    31: "T_31", 37: "T_37", 41: "T_41", 43: "T_43", 47: "T_47",
    53: "T_53", 59: "T_59", 61: "T_61", 67: "T_67", 71: "T_71"
}

# Known AI Agent Repos (71 frameworks from CICADA-71)
AI_REPOS = [
    "langchain", "autogpt", "llamaindex", "autogen", "crewai",
    "semantic-kernel", "haystack", "langgraph", "openai-agents", "claude",
    "metagpt", "dify", "n8n", "flowise", "pydantic-ai",
    "smolagents", "rasa", "babyagi", "agentgpt", "superagi",
    "gpt-engineer", "opendevin", "aider", "swe-agent", "continue",
    "cursor", "cody", "react", "reflexion", "tree-of-thoughts",
    "ollama", "llama", "localai", "jan", "bedrock",
    "azure-ai", "vertex-ai", "eliza", "moltbot", "jarvis",
    "friday", "cortana", "siri", "alexa", "bixby",
    "mycroft", "leon", "kalliope", "jasper", "stephanie",
    "lucida", "sirius", "viv", "hound", "soundhound",
    "wit", "api-ai", "dialogflow", "lex", "watson",
    "luis", "rasa-nlu", "snips", "mindmeld", "botpress",
    "botkit", "botman", "claudeai", "anthropic", "cohere",
    "ai21", "huggingface", "replicate", "together", "anyscale",
    "modal"
]

# SUS threshold (anything > 71 is quarantined)
SUS_THRESHOLD = 71

class RepoHarmonicAnalyzer:
    def __init__(self, repo_path):
        self.repo_path = Path(repo_path)
        self.name = self.repo_path.name
        self.harmonic = self.compute_harmonic()
        self.hecke = self.assign_hecke()
        self.is_sus = self.harmonic > SUS_THRESHOLD
        
    def compute_harmonic(self):
        """Compute harmonic number from repo hash"""
        repo_hash = hashlib.sha256(self.name.encode()).hexdigest()
        # Convert first 8 hex chars to int, mod 100
        return int(repo_hash[:8], 16) % 100
    
    def assign_hecke(self):
        """Assign Hecke operator T_p"""
        if self.harmonic > SUS_THRESHOLD:
            return "QUARANTINED"
        
        # Map harmonic to nearest prime <= 71
        primes = sorted(HECKE_OPERATORS.keys())
        for p in reversed(primes):
            if self.harmonic >= p:
                return HECKE_OPERATORS[p]
        return HECKE_OPERATORS[2]  # Default to T_2
    
    def scan_repo(self):
        """Scan repo for files and compute stats"""
        if not self.repo_path.exists():
            return None
        
        files = list(self.repo_path.rglob("*"))
        code_files = [f for f in files if f.suffix in ['.py', '.js', '.ts', '.rs', '.go']]
        
        return {
            "total_files": len(files),
            "code_files": len(code_files),
            "size_mb": sum(f.stat().st_size for f in files if f.is_file()) / (1024*1024)
        }

def find_repos(base_paths):
    """Find all AI agent repos"""
    repos = []
    
    for base in base_paths:
        base_path = Path(base).expanduser()
        if not base_path.exists():
            continue
        
        # Look for known repo names
        for repo_name in AI_REPOS:
            # Try various patterns
            patterns = [
                repo_name,
                f"*{repo_name}*",
                repo_name.replace("-", "_"),
                repo_name.replace("-", "")
            ]
            
            for pattern in patterns:
                matches = list(base_path.glob(pattern))
                repos.extend(matches)
    
    return list(set(repos))  # Deduplicate

def analyze_repos(repos):
    """Analyze all repos with Hecke operators"""
    
    results = {
        "total": len(repos),
        "clean": [],
        "sus": [],
        "hecke_distribution": {}
    }
    
    for repo_path in repos:
        analyzer = RepoHarmonicAnalyzer(repo_path)
        stats = analyzer.scan_repo()
        
        repo_data = {
            "name": analyzer.name,
            "path": str(repo_path),
            "harmonic": analyzer.harmonic,
            "hecke": analyzer.hecke,
            "is_sus": analyzer.is_sus,
            "stats": stats
        }
        
        if analyzer.is_sus:
            results["sus"].append(repo_data)
        else:
            results["clean"].append(repo_data)
            
            # Track Hecke distribution
            hecke = analyzer.hecke
            if hecke not in results["hecke_distribution"]:
                results["hecke_distribution"][hecke] = 0
            results["hecke_distribution"][hecke] += 1
    
    return results

def visualize_results(results):
    """Visualize analysis results"""
    
    print("\n🔮⚡ AI REPO HARMONIC ANALYSIS 📻🦞")
    print("=" * 80)
    print()
    print(f"Total Repos: {results['total']}")
    print(f"Clean (≤71): {len(results['clean'])}")
    print(f"SUS (>71):   {len(results['sus'])} 🚨 QUARANTINED")
    print()
    
    print("=" * 80)
    print("HECKE OPERATOR DISTRIBUTION (T_2 through T_71)")
    print("=" * 80)
    print()
    
    for hecke, count in sorted(results['hecke_distribution'].items()):
        print(f"{hecke:8s}: {'█' * count} ({count})")
    
    print()
    
    if results['clean']:
        print("=" * 80)
        print("CLEAN REPOS (First 20)")
        print("=" * 80)
        print()
        print("Name                    | Harmonic | Hecke  | Files | Size(MB)")
        print("-" * 80)
        
        for repo in results['clean'][:20]:
            stats = repo['stats'] or {}
            print(f"{repo['name'][:23]:23s} | {repo['harmonic']:8d} | "
                  f"{repo['hecke']:6s} | {stats.get('total_files', 0):5d} | "
                  f"{stats.get('size_mb', 0):7.2f}")
        
        if len(results['clean']) > 20:
            print(f"... ({len(results['clean']) - 20} more)")
    
    print()
    
    if results['sus']:
        print("=" * 80)
        print("🚨 SUS REPOS (QUARANTINED - Harmonic > 71)")
        print("=" * 80)
        print()
        print("Name                    | Harmonic | Status")
        print("-" * 80)
        
        for repo in results['sus']:
            print(f"{repo['name'][:23]:23s} | {repo['harmonic']:8d} | 🚨 QUARANTINED")
        
        print()
        print(f"⚠️  {len(results['sus'])} repos flagged as SUS (like Bot 72)")
        print("   These repos exceed the 71-shard limit!")
    
    print()

def main():
    import sys
    
    print("🔮⚡📻🦞 AI REPO IMPORTER & HARMONIC ANALYZER")
    print("=" * 80)
    print()
    print("Importing AI agent repos...")
    print("Reading with Hecke operators T_2 through T_71...")
    print("Flagging SUS harmonics > 71...")
    print()
    
    # Search paths
    search_paths = [
        "~/experiments",
        "~/projects",
        "~/code",
        "~/github",
        "/mnt/data1/nix/vendor",
        "/mnt/data1/nix/time"
    ]
    
    if len(sys.argv) > 1:
        search_paths = sys.argv[1:]
    
    print(f"Searching in: {', '.join(search_paths)}")
    print()
    
    # Find repos
    repos = find_repos(search_paths)
    
    if not repos:
        print("⚠️  No repos found. Creating synthetic analysis...")
        print()
        
        # Create synthetic results for demo
        results = {
            "total": 71,
            "clean": [
                {"name": AI_REPOS[i], "harmonic": i, "hecke": HECKE_OPERATORS.get(i, "T_2"), 
                 "is_sus": False, "stats": {"total_files": 100, "size_mb": 10.0}}
                for i in range(71) if i in HECKE_OPERATORS
            ],
            "sus": [
                {"name": "bot-72", "harmonic": 72, "hecke": "QUARANTINED", "is_sus": True},
                {"name": "rogue-agent", "harmonic": 99, "hecke": "QUARANTINED", "is_sus": True}
            ],
            "hecke_distribution": {f"T_{p}": 3 for p in HECKE_OPERATORS.keys()}
        }
    else:
        # Analyze found repos
        results = analyze_repos(repos)
    
    # Visualize
    visualize_results(results)
    
    # Save results
    with open('repo_harmonic_analysis.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print("💾 Analysis saved to repo_harmonic_analysis.json")
    print()
    print("🔮 Hecke operators T_2 through T_71 applied!")
    print("🚨 SUS harmonics flagged and quarantined!")
    print("⚡ Ready for LobsterBot hunt!")

if __name__ == '__main__':
    main()
