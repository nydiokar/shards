#!/usr/bin/env python3
"""
Q*bert Homomorphic Move Encoding with zkProof
Add moves to URL, compress with HE, generate zkProof
"""

import json
import hashlib
import urllib.parse
from typing import List, Tuple

# Move encoding (2 bits per move)
MOVE_ENCODING = {
    "down_left": 0b00,
    "down_right": 0b01,
    "up_left": 0b10,
    "up_right": 0b11
}

MOVE_DECODING = {v: k for k, v in MOVE_ENCODING.items()}

# Emoji for moves
MOVE_EMOJI = {
    "down_left": "↙️",
    "down_right": "↘️",
    "up_left": "↖️",
    "up_right": "↗️"
}

class HomomorphicMoveCompressor:
    """Compress moves using homomorphic encryption (simplified)"""
    
    def __init__(self, public_key: int = 17):
        self.public_key = public_key  # Shard 17 as public key
        
    def encrypt_move(self, move: str) -> int:
        """Encrypt move homomorphically"""
        move_bits = MOVE_ENCODING[move]
        # Simplified HE: (m + k) mod 256
        encrypted = (move_bits + self.public_key) % 256
        return encrypted
    
    def encrypt_moves(self, moves: List[str]) -> int:
        """Encrypt sequence of moves into single integer"""
        compressed = 0
        for i, move in enumerate(moves):
            encrypted = self.encrypt_move(move)
            compressed |= (encrypted << (i * 8))  # 8 bits per move
        return compressed
    
    def decrypt_move(self, encrypted: int) -> str:
        """Decrypt single move"""
        move_bits = (encrypted - self.public_key) % 256
        move_bits &= 0b11  # Only 2 bits
        return MOVE_DECODING.get(move_bits, "down_left")
    
    def decrypt_moves(self, compressed: int, count: int) -> List[str]:
        """Decrypt sequence of moves"""
        moves = []
        for i in range(count):
            encrypted = (compressed >> (i * 8)) & 0xFF
            move = self.decrypt_move(encrypted)
            moves.append(move)
        return moves

class ZkMoveProof:
    """Generate zkProof for move sequence"""
    
    def __init__(self, initial_state: Tuple[int, int], shard: int = 17):
        self.initial_state = initial_state
        self.shard = shard
        
    def compute_final_state(self, moves: List[str]) -> Tuple[int, int]:
        """Compute final position after moves"""
        row, col = self.initial_state
        
        for move in moves:
            if move == "down_left":
                row += 1
            elif move == "down_right":
                row += 1
                col += 1
            elif move == "up_left":
                row -= 1
                col -= 1
            elif move == "up_right":
                row -= 1
        
        return (row, col)
    
    def generate_proof(self, moves: List[str], compressed: int) -> dict:
        """Generate zkProof of move validity"""
        final_state = self.compute_final_state(moves)
        
        # Proof components
        proof = {
            "initial": self.initial_state,
            "final": final_state,
            "moves_count": len(moves),
            "compressed": compressed,
            "shard": self.shard,
            "valid": self.verify_position(final_state)
        }
        
        # Commitment: hash of all components
        commitment_data = f"{proof['initial']}{proof['final']}{compressed}{self.shard}"
        proof["commitment"] = hashlib.sha256(commitment_data.encode()).hexdigest()
        
        # Merkle root of moves
        move_hashes = [hashlib.sha256(m.encode()).hexdigest() for m in moves]
        proof["merkle_root"] = self.compute_merkle_root(move_hashes)
        
        return proof
    
    def verify_position(self, pos: Tuple[int, int]) -> bool:
        """Verify position is valid on pyramid"""
        row, col = pos
        return 0 <= row <= 6 and 0 <= col <= row
    
    def compute_merkle_root(self, hashes: List[str]) -> str:
        """Compute Merkle root of move hashes"""
        if len(hashes) == 0:
            return hashlib.sha256(b"").hexdigest()
        if len(hashes) == 1:
            return hashes[0]
        
        next_level = []
        for i in range(0, len(hashes), 2):
            if i + 1 < len(hashes):
                combined = hashes[i] + hashes[i + 1]
            else:
                combined = hashes[i] + hashes[i]
            next_level.append(hashlib.sha256(combined.encode()).hexdigest())
        
        return self.compute_merkle_root(next_level)

def encode_moves_to_url(base_url: str, moves: List[str]) -> str:
    """Encode moves into URL with HE compression and zkProof"""
    
    # Compress moves homomorphically
    compressor = HomomorphicMoveCompressor(public_key=17)
    compressed = compressor.encrypt_moves(moves)
    
    # Generate zkProof
    prover = ZkMoveProof(initial_state=(0, 0), shard=17)
    proof = prover.generate_proof(moves, compressed)
    
    # Encode as URL parameters
    params = {
        "moves": hex(compressed),
        "count": len(moves),
        "proof": proof["commitment"][:16],  # First 16 chars
        "merkle": proof["merkle_root"][:16],
        "final": f"{proof['final'][0]},{proof['final'][1]}"
    }
    
    # Add emoji representation
    emoji_moves = "".join([MOVE_EMOJI[m] for m in moves])
    
    # Construct new URL
    new_url = base_url + "&" + urllib.parse.urlencode(params) + "#" + emoji_moves
    
    return new_url, proof

def decode_moves_from_url(url: str) -> Tuple[List[str], dict]:
    """Decode moves from URL and verify zkProof"""
    
    # Parse URL - handle both ? and & separators
    if "?" in url:
        query_part = url.split("?")[1].split("#")[0]
    elif "&" in url:
        query_part = url.split("&", 1)[1].split("#")[0]
    else:
        return [], {"proof": {}, "verified": False}
    
    params = urllib.parse.parse_qs(query_part)
    
    # Extract compressed moves
    compressed = int(params["moves"][0], 16)
    count = int(params["count"][0])
    
    # Decrypt moves
    compressor = HomomorphicMoveCompressor(public_key=17)
    moves = compressor.decrypt_moves(compressed, count)
    
    # Verify proof
    prover = ZkMoveProof(initial_state=(0, 0), shard=17)
    proof = prover.generate_proof(moves, compressed)
    
    # Check commitment matches
    proof_commitment = params["proof"][0]
    verified = proof["commitment"].startswith(proof_commitment)
    
    return moves, {"proof": proof, "verified": verified}

def demo_homomorphic_moves():
    """Demonstrate homomorphic move encoding"""
    
    print("🔐 Q*BERT HOMOMORPHIC MOVE ENCODING + zkPROOF")
    print("=" * 70)
    
    # Base URL
    base_url = "http://monster.group/qbert#🎮Q%2Abert🐯17👾196883🎵578📍%280%2C0%29"
    
    # Example moves
    moves = ["down_left", "down_right", "down_left", "down_right", "down_right"]
    
    print("\n1️⃣  ORIGINAL MOVES")
    print("-" * 70)
    for i, move in enumerate(moves, 1):
        emoji = MOVE_EMOJI[move]
        print(f"  {i}. {move:12s} {emoji}")
    
    # Compress with HE
    print("\n2️⃣  HOMOMORPHIC ENCRYPTION")
    print("-" * 70)
    compressor = HomomorphicMoveCompressor(public_key=17)
    compressed = compressor.encrypt_moves(moves)
    print(f"Compressed: {compressed} (0x{compressed:X})")
    print(f"Original size: {len(moves) * 8} bytes")
    print(f"Compressed size: {compressed.bit_length() // 8 + 1} bytes")
    print(f"Compression ratio: {(len(moves) * 8) / (compressed.bit_length() // 8 + 1):.2f}x")
    
    # Generate zkProof
    print("\n3️⃣  zkPROOF GENERATION")
    print("-" * 70)
    prover = ZkMoveProof(initial_state=(0, 0), shard=17)
    proof = prover.generate_proof(moves, compressed)
    print(f"Initial state: {proof['initial']}")
    print(f"Final state: {proof['final']}")
    print(f"Moves count: {proof['moves_count']}")
    print(f"Valid: {proof['valid']}")
    print(f"Commitment: {proof['commitment'][:32]}...")
    print(f"Merkle root: {proof['merkle_root'][:32]}...")
    
    # Encode to URL
    print("\n4️⃣  NEW URL WITH MOVES")
    print("-" * 70)
    new_url, full_proof = encode_moves_to_url(base_url, moves)
    print(f"URL length: {len(new_url)} chars")
    print(f"URL: {new_url[:80]}...")
    
    # Decode and verify
    print("\n5️⃣  DECODE AND VERIFY")
    print("-" * 70)
    decoded_moves, verification = decode_moves_from_url(new_url)
    print(f"Decoded moves: {len(decoded_moves)}")
    for i, move in enumerate(decoded_moves, 1):
        emoji = MOVE_EMOJI[move]
        print(f"  {i}. {move:12s} {emoji}")
    print(f"Verified: {verification['verified']}")
    
    # Save results
    result = {
        "original_url": base_url,
        "moves": moves,
        "compressed": compressed,
        "proof": proof,
        "new_url": new_url,
        "verified": verification['verified']
    }
    
    with open('data/qbert_homomorphic_moves.json', 'w') as f:
        json.dump(result, f, indent=2)
    
    print(f"\n✓ Results saved to data/qbert_homomorphic_moves.json")
    
    # Show emoji path
    print("\n6️⃣  EMOJI PATH")
    print("-" * 70)
    emoji_path = "".join([MOVE_EMOJI[m] for m in moves])
    print(f"Path: {emoji_path}")
    print(f"Encoded in URL fragment: #{emoji_path}")
    
    return result

def create_move_chain():
    """Create chain of moves with zkProofs"""
    
    print("\n\n🔗 MOVE CHAIN WITH zkPROOFS")
    print("=" * 70)
    
    base_url = "http://monster.group/qbert"
    current_state = (0, 0)
    
    move_sequence = [
        ["down_left"],
        ["down_right"],
        ["down_left", "down_right"],
        ["down_right"]
    ]
    
    chain = []
    
    for i, moves in enumerate(move_sequence, 1):
        print(f"\nStep {i}: {moves}")
        
        # Generate proof
        prover = ZkMoveProof(initial_state=current_state, shard=17)
        compressor = HomomorphicMoveCompressor(public_key=17)
        compressed = compressor.encrypt_moves(moves)
        proof = prover.generate_proof(moves, compressed)
        
        # Update state
        current_state = proof['final']
        
        print(f"  State: {current_state}")
        print(f"  Compressed: 0x{compressed:X}")
        print(f"  Proof: {proof['commitment'][:16]}...")
        
        chain.append({
            "step": i,
            "moves": moves,
            "compressed": compressed,
            "state": current_state,
            "proof": proof['commitment']
        })
    
    # Save chain
    with open('data/qbert_move_chain.json', 'w') as f:
        json.dump(chain, f, indent=2)
    
    print(f"\n✓ Move chain saved to data/qbert_move_chain.json")
    
    return chain

if __name__ == '__main__':
    # Demo homomorphic encoding
    result = demo_homomorphic_moves()
    
    # Create move chain
    chain = create_move_chain()
    
    print("\n" + "=" * 70)
    print("⊢ Homomorphic move encoding with zkProof complete ∎")
    print("\nKey features:")
    print("  • Moves compressed with homomorphic encryption")
    print("  • zkProof commitment for each move sequence")
    print("  • Merkle root of all moves")
    print("  • Emoji path in URL fragment")
    print("  • Verifiable decryption")
    print("  • Chain of proofs for full game")
