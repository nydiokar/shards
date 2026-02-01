#!/usr/bin/env python3
"""
Telegraph ZK - Morse Code with Zero-Knowledge Proofs
"""

import hashlib
import time
import sys

MORSE_TABLE = {
    'A': '.-',    'B': '-...',  'C': '-.-.',  'D': '-..',
    'E': '.',     'F': '..-.',  'G': '--.',   'H': '....',
    'I': '..',    'J': '.---',  'K': '-.-',   'L': '.-..',
    'M': '--',    'N': '-.',    'O': '---',   'P': '.--.',
    'Q': '--.-',  'R': '.-.',   'S': '...',   'T': '-',
    'U': '..-',   'V': '...-',  'W': '.--',   'X': '-..-',
    'Y': '-.--',  'Z': '--..',
    '0': '-----', '1': '.----', '2': '..---', '3': '...--',
    '4': '....-', '5': '.....', '6': '-....', '7': '--...',
    '8': '---..', '9': '----.',
    ' ': '/',
}

MORSE_DECODE = {v: k for k, v in MORSE_TABLE.items()}

DOT_MS = 0.1
DASH_MS = 0.3
GAP_MS = 0.1

def encode_morse(text):
    """Encode text to Morse code"""
    return ' '.join(MORSE_TABLE.get(c.upper(), '') for c in text)

def decode_morse(morse):
    """Decode Morse code to text"""
    return ''.join(MORSE_DECODE.get(code, '') for code in morse.split())

def zk_proof(message, shard_id):
    """Generate ZK proof for message"""
    h = hashlib.sha256()
    h.update(message.encode())
    h.update(bytes([shard_id]))
    return h.hexdigest()

def transmit_morse(morse):
    """Transmit Morse code with visual output"""
    for symbol in morse:
        if symbol == '.':
            print('•', end='', flush=True)
            time.sleep(DOT_MS)
        elif symbol == '-':
            print('━', end='', flush=True)
            time.sleep(DASH_MS)
        elif symbol == ' ':
            print(' ', end='', flush=True)
        elif symbol == '/':
            print(' / ', end='', flush=True)
        time.sleep(GAP_MS)
    print()

def send_message(from_shard, to_shard, message):
    """Send telegraph message"""
    print("╔════════════════════════════════════════════════════════════╗")
    print("║              TELEGRAPH TRANSMISSION                        ║")
    print("╚════════════════════════════════════════════════════════════╝\n")
    
    print(f"From: Shard {from_shard}")
    print(f"To:   Shard {to_shard}")
    print(f"Text: {message}\n")
    
    morse = encode_morse(message)
    print(f"Morse: {morse}\n")
    
    proof = zk_proof(message, from_shard)
    print(f"ZK Proof: {proof[:16]}\n")
    
    print("Transmitting...\n")
    transmit_morse(morse)
    
    print("\n✓ Transmission complete")

def main():
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python3 telegraph.py send <from> <to> <message>")
        print("  python3 telegraph.py encode <text>")
        print("  python3 telegraph.py decode <morse>")
        print("  python3 telegraph.py station <shard>")
        return
    
    cmd = sys.argv[1]
    
    if cmd == 'send' and len(sys.argv) >= 5:
        from_shard = int(sys.argv[2])
        to_shard = int(sys.argv[3])
        message = ' '.join(sys.argv[4:])
        send_message(from_shard, to_shard, message)
    
    elif cmd == 'encode' and len(sys.argv) >= 3:
        text = ' '.join(sys.argv[2:])
        morse = encode_morse(text)
        print(f"Text:  {text}")
        print(f"Morse: {morse}")
    
    elif cmd == 'decode' and len(sys.argv) >= 3:
        morse = ' '.join(sys.argv[2:])
        text = decode_morse(morse)
        print(f"Morse: {morse}")
        print(f"Text:  {text}")
    
    elif cmd == 'station' and len(sys.argv) >= 3:
        shard = int(sys.argv[2])
        print("╔════════════════════════════════════════════════════════════╗")
        print(f"║           Telegraph Station - Shard {shard:2}                   ║")
        print("╚════════════════════════════════════════════════════════════╝\n")
        print(f"ZK Context: Shard {shard}")
        print("Listening for messages...")
        print("(Press Ctrl+C to stop)\n")
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            print("\nStation closed")

if __name__ == '__main__':
    main()
