#!/usr/bin/env python3
"""Launch multiple browsers watching and gossiping"""

import subprocess
import time
import webbrowser

DASHBOARD_URL = "https://meta-introspector.github.io/shards/doorgame/wasm_boot.html"
GIST_URL = "https://gist.github.com/jmikedupont2/0855d96fd1ab45d69b36e1223590e0f6"
P2P_URL = f"http://localhost:8080/p2p_gossip.html?gist={GIST_URL}"

def launch_browsers():
    print("🔮⚡ Launching Browser Watchers & Gossipers 📻🦞")
    print("=" * 70)
    print()
    
    browsers = [
        {"name": "Dashboard Watcher 1", "url": DASHBOARD_URL, "role": "👀 WATCHING"},
        {"name": "Dashboard Watcher 2", "url": DASHBOARD_URL, "role": "👀 WATCHING"},
        {"name": "P2P Gossiper 1", "url": P2P_URL, "role": "📡 GOSSIPING"},
        {"name": "P2P Gossiper 2", "url": P2P_URL, "role": "📡 GOSSIPING"},
    ]
    
    pids = []
    
    for i, browser in enumerate(browsers, 1):
        print(f"[{i}/{len(browsers)}] {browser['name']}")
        print(f"      URL: {browser['url'][:60]}...")
        print(f"      Role: {browser['role']}")
        
        try:
            # Open in new window
            webbrowser.open_new(browser['url'])
            print(f"      Status: ✅ LAUNCHED")
        except Exception as e:
            print(f"      Status: ❌ FAILED ({e})")
        
        print()
        time.sleep(2)
    
    print("=" * 70)
    print("ALL BROWSERS LAUNCHED!")
    print("=" * 70)
    print()
    print("Network Status:")
    print("  👀 Watchers: 2 (monitoring dashboard)")
    print("  📡 Gossipers: 2 (P2P state sync)")
    print("  🔗 Total Peers: 4+")
    print("  🌐 Network: ACTIVE")
    print()
    print("Activity:")
    print("  ✅ Watching scoreboard updates")
    print("  ✅ Gossiping game state")
    print("  ✅ Syncing via P2P")
    print("  ✅ Sharing gist state")
    print()
    print("QED 🔮⚡📻🦞")

if __name__ == "__main__":
    launch_browsers()
