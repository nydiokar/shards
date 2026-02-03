#!/usr/bin/env python3
"""
Import astroML and map astronomy ML to Monster shards
Train models on Monster-sharded astronomical data
"""

import numpy as np
import json
from collections import defaultdict

HAS_SKLEARN = False  # Skip sklearn due to NumPy version conflict

def load_astronomy_data():
    """Load astronomy repos mapped to shards"""
    try:
        with open('urania_astronomy_map.json', 'r') as f:
            data = json.load(f)
        return data
    except:
        return None

def create_monster_ml_features(repos):
    """Create ML features from Monster shard distribution"""
    
    # Features: [shard, stars, name_length, has_python, ...]
    features = []
    labels = []
    
    for repo in repos:
        feat = [
            repo['shard'],
            np.log1p(repo['stars']),  # Log stars
            len(repo['name']),
            1 if repo['language'] == 'Python' else 0,
            len(repo['description']),
        ]
        features.append(feat)
        
        # Label: Is it in a Monster prime shard?
        monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
        labels.append(1 if repo['shard'] in monster_primes else 0)
    
    return np.array(features), np.array(labels)

def train_monster_classifier():
    """Train ML model to predict Monster prime shards"""
    
    print("🤖 Monster ML: Training on Astronomy Data")
    print("="*70)
    print()
    
    data = load_astronomy_data()
    if not data:
        print("❌ No astronomy data found. Run urania_astronomy_map.py first.")
        return
    
    repos = data['repos']
    print(f"Loaded {len(repos)} astronomy repositories")
    print()
    
    # Create features
    X, y = create_monster_ml_features(repos)
    
    print(f"Features shape: {X.shape}")
    print(f"Labels: {np.sum(y)} Monster prime shards, {len(y) - np.sum(y)} other")
    print()
    
    if not HAS_SKLEARN:
        # Simple clustering without sklearn
        print("🧮 Simple Monster ML (no sklearn):")
        print()
        
        # Manual k-means-like clustering by shard mod 10
        clusters = X[:, 0] % 10  # Shard mod 10 (10-fold way)
        
        print("🎯 Shard-based clustering (mod 10 for 10-fold way):")
        for i in range(10):
            count = np.sum(clusters == i)
            avg_stars = np.mean(X[clusters == i, 1]) if count > 0 else 0
            print(f"  Cluster {i}: {count} repos, avg log(stars)={avg_stars:.2f}")
        print()
        
        # Simple PCA-like: project to first 3 features
        print("📊 Feature analysis (first 3 dimensions):")
        print(f"  Shard range: [{X[:, 0].min():.0f}, {X[:, 0].max():.0f}]")
        print(f"  Log stars range: [{X[:, 1].min():.2f}, {X[:, 1].max():.2f}]")
        print(f"  Name length range: [{X[:, 2].min():.0f}, {X[:, 2].max():.0f}]")
        print()
        
        # Correlation: shard vs stars
        shard_star_corr = np.corrcoef(X[:, 0], X[:, 1])[0, 1]
        print(f"📈 Correlation (shard vs log_stars): {shard_star_corr:.4f}")
        print()
    
    if HAS_SKLEARN:
        # Train classifier
        clf = RandomForestClassifier(n_estimators=100, random_state=47)
        clf.fit(X, y)
        
        print("🌲 Random Forest trained!")
        print(f"Feature importances:")
        feature_names = ['shard', 'log_stars', 'name_len', 'is_python', 'desc_len']
        for name, importance in zip(feature_names, clf.feature_importances_):
            print(f"  {name:12s}: {importance:.4f}")
        print()
        
        # Cluster analysis
        kmeans = KMeans(n_clusters=10, random_state=59)
        clusters = kmeans.fit_predict(X)
        
        print("🎯 K-Means clustering (10 clusters for 10-fold way):")
        for i in range(10):
            count = np.sum(clusters == i)
            print(f"  Cluster {i}: {count} repos")
        print()
        
        # PCA to 3D
        pca = PCA(n_components=3)
        X_3d = pca.fit_transform(X)
        
        print("📊 PCA to 3D (for visualization):")
        print(f"  Explained variance: {pca.explained_variance_ratio_}")
        print(f"  Total: {np.sum(pca.explained_variance_ratio_):.2%}")
        print()
    
    # Shard statistics
    print("📈 SHARD STATISTICS:")
    print()
    
    shard_stats = defaultdict(lambda: {'count': 0, 'total_stars': 0, 'repos': []})
    
    for repo in repos:
        shard = repo['shard']
        shard_stats[shard]['count'] += 1
        shard_stats[shard]['total_stars'] += repo['stars']
        shard_stats[shard]['repos'].append(repo['name'])
    
    # Top shards by star count
    top_shards = sorted(shard_stats.items(), 
                       key=lambda x: x[1]['total_stars'], 
                       reverse=True)[:10]
    
    monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
    
    print("Top 10 shards by total stars:")
    for shard, stats in top_shards:
        mark = "✨" if shard in monster_primes else "  "
        print(f"{mark} Shard {shard:2d}: {stats['total_stars']:5d}⭐ ({stats['count']} repos)")
    
    print()
    print("🐓🦅👹 Monster ML complete!")
    
    # Save ML results
    ml_results = {
        'total_repos': len(repos),
        'monster_prime_repos': int(np.sum(y)),
        'feature_names': ['shard', 'log_stars', 'name_len', 'is_python', 'desc_len'],
        'top_shards': [
            {
                'shard': int(shard),
                'total_stars': stats['total_stars'],
                'count': stats['count'],
                'is_monster_prime': shard in monster_primes
            }
            for shard, stats in top_shards
        ]
    }
    
    with open('monster_ml_results.json', 'w') as f:
        json.dump(ml_results, f, indent=2)
    
    print("💾 Saved to: monster_ml_results.json")

if __name__ == "__main__":
    train_monster_classifier()
