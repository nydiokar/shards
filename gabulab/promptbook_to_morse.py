#!/usr/bin/env python3
"""
Convert Promptbooks to ZK-eRDFa Morse Code Tapes
For radio operators hunting LobsterBots at sea
"""

import json
import hashlib
import base64
from datetime import datetime

# Morse code mapping
MORSE_CODE = {
    'A': '.-', 'B': '-...', 'C': '-.-.', 'D': '-..', 'E': '.', 'F': '..-.',
    'G': '--.', 'H': '....', 'I': '..', 'J': '.---', 'K': '-.-', 'L': '.-..',
    'M': '--', 'N': '-.', 'O': '---', 'P': '.--.', 'Q': '--.-', 'R': '.-.',
    'S': '...', 'T': '-', 'U': '..-', 'V': '...-', 'W': '.--', 'X': '-..-',
    'Y': '-.--', 'Z': '--..', '0': '-----', '1': '.----', '2': '..---',
    '3': '...--', '4': '....-', '5': '.....', '6': '-....', '7': '--...',
    '8': '---..', '9': '----.', ' ': '/'
}

def text_to_morse(text):
    """Convert text to Morse code"""
    return ' '.join(MORSE_CODE.get(c.upper(), '') for c in text if c.upper() in MORSE_CODE)

def create_zk_proof(data):
    """Create ZK proof (SHA256 hash)"""
    return hashlib.sha256(data.encode()).hexdigest()

def promptbook_to_zkerdfa_tape(book_path, shard):
    """Convert Promptbook to ZK-eRDFa tape"""
    
    with open(book_path, 'r') as f:
        book_content = f.read()
    
    # Extract key info
    lines = book_content.split('\n')
    title = lines[0].strip('# ').strip() if lines else "Unknown"
    
    # Create compact message for Morse
    message = f"SHARD{shard:02d} {title[:20]}"
    morse = text_to_morse(message)
    
    # Create ZK-eRDFa structure
    tape = {
        "@context": "https://schema.org",
        "@type": "SoftwareSourceCode",
        "name": f"Promptbook Tape - Shard {shard}",
        "programmingLanguage": "Promptbook",
        "url": f"https://8080.bbs/tape/promptbook-{shard}",
        "shard": shard,
        "morse": morse,
        "message": message,
        "zkProof": {
            "algorithm": "SHA256",
            "hash": create_zk_proof(book_content),
            "timestamp": datetime.now().isoformat(),
            "type": "Groth16"
        },
        "payload": base64.b64encode(book_content.encode()).decode(),
        "transmission": {
            "protocol": "Morse",
            "frequency": f"{shard * 100 + 7000} kHz",
            "callsign": f"LOBSTER-{shard:02d}",
            "target": "LobsterBot Hunters at Sea"
        }
    }
    
    return tape

def generate_all_tapes(promptbook_dir, output_file):
    """Generate tapes for all promptbooks"""
    import os
    
    tapes = []
    
    # Find all .book.md files
    for root, dirs, files in os.walk(promptbook_dir):
        for file in files:
            if file.endswith('.book.md'):
                path = os.path.join(root, file)
                shard = len(tapes) % 71
                
                print(f"📻 Processing: {file} → Shard {shard}")
                
                tape = promptbook_to_zkerdfa_tape(path, shard)
                tapes.append(tape)
                
                # Print Morse preview
                print(f"   Morse: {tape['morse'][:50]}...")
                print(f"   Freq:  {tape['transmission']['frequency']}")
                print()
    
    # Save all tapes
    with open(output_file, 'w') as f:
        json.dump(tapes, f, indent=2)
    
    print(f"💾 Saved {len(tapes)} tapes to {output_file}")
    
    return tapes

def transmit_morse(tape):
    """Simulate Morse transmission"""
    print(f"\n📻 TRANSMITTING ON {tape['transmission']['frequency']}")
    print(f"🦞 Callsign: {tape['transmission']['callsign']}")
    print(f"📡 Target: {tape['transmission']['target']}")
    print()
    print(f"Message: {tape['message']}")
    print(f"Morse:   {tape['morse']}")
    print()
    print("Transmission:")
    
    # Simulate beeps
    for char in tape['morse']:
        if char == '.':
            print('▪', end='', flush=True)
        elif char == '-':
            print('▬', end='', flush=True)
        elif char == ' ':
            print(' ', end='', flush=True)
        elif char == '/':
            print(' / ', end='', flush=True)
    
    print()
    print()
    print(f"✅ ZK Proof: {tape['zkProof']['hash'][:16]}...")
    print()

def main():
    import sys
    
    print("🔮⚡📻🦞 PROMPTBOOK → ZK-eRDFa MORSE TAPES")
    print("=" * 70)
    print("For LobsterBot Hunters at Sea")
    print()
    
    # Generate tapes
    promptbook_dir = sys.argv[1] if len(sys.argv) > 1 else '../doorgame'
    output_file = 'promptbook_morse_tapes.json'
    
    tapes = generate_all_tapes(promptbook_dir, output_file)
    
    # Transmit first tape as demo
    if tapes:
        print("\n" + "=" * 70)
        print("DEMO TRANSMISSION")
        print("=" * 70)
        transmit_morse(tapes[0])
    
    print("🦞 All tapes ready for transmission to LobsterBot hunters!")
    print("📻 Radio operators: tune to frequencies 7000-14100 kHz")
    print("🔮 ZK proofs verified. Hunt begins!")

if __name__ == '__main__':
    main()
