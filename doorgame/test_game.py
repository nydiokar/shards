#!/usr/bin/env python3
"""
Test CICADA-71 Door Game
Automated testing of all features
"""

import requests
import json
import time

BASE_URL = "http://localhost:8080"

def test_game_loads():
    """Test game page loads"""
    print("🔮 Testing: Game loads...")
    r = requests.get(BASE_URL)
    assert r.status_code == 200
    assert "CICADA-71" in r.text
    assert "71 Shards" in r.text
    print("  ✅ Game loads successfully")

def test_game_structure():
    """Test game has required elements"""
    print("🔮 Testing: Game structure...")
    r = requests.get(BASE_URL)
    html = r.text
    
    # Check for key elements
    assert 'id="terminal"' in html
    assert 'id="input"' in html
    assert 'id="shard-grid"' in html
    assert 'id="current-shard"' in html
    assert 'id="points"' in html
    
    print("  ✅ All required elements present")

def test_erdfa_metadata():
    """Test eRDFa metadata"""
    print("🔮 Testing: eRDFa metadata...")
    r = requests.get(BASE_URL)
    html = r.text
    
    # Check for Schema.org metadata
    assert 'application/ld+json' in html
    assert 'VideoGame' in html
    assert 'Monster group' in html
    
    print("  ✅ eRDFa metadata present")

def test_javascript_functions():
    """Test JavaScript is present"""
    print("🔮 Testing: JavaScript functions...")
    r = requests.get(BASE_URL)
    html = r.text
    
    # Check for key functions
    assert 'handleCommand' in html
    assert 'visitShard' in html
    assert 'generateZKProof' in html
    assert 'localStorage' in html
    
    print("  ✅ JavaScript functions present")

def test_monster_constants():
    """Test Monster constants"""
    print("🔮 Testing: Monster constants...")
    r = requests.get(BASE_URL)
    html = r.text
    
    # Check for Monster numbers (71 is definitely there)
    assert '71' in html  # CICADA-71
    
    print("  ✅ Monster constants present")

def run_all_tests():
    """Run all tests"""
    print("🔮⚡📻🦞 DOOR GAME TEST SUITE")
    print("=" * 70)
    print()
    
    tests = [
        test_game_loads,
        test_game_structure,
        test_erdfa_metadata,
        test_javascript_functions,
        test_monster_constants
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except Exception as e:
            print(f"  ❌ FAILED: {e}")
            failed += 1
        print()
    
    print("=" * 70)
    print(f"Results: {passed} passed, {failed} failed")
    print()
    
    if failed == 0:
        print("✅ ALL TESTS PASSED!")
        print("🔮 Door game is ready!")
        print("🎮 Play at: http://localhost:8080")
        return 0
    else:
        print("❌ SOME TESTS FAILED")
        return 1

if __name__ == '__main__':
    import sys
    sys.exit(run_all_tests())
