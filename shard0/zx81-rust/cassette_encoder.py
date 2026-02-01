#!/usr/bin/env python3
# cassette_encoder.py - Generate ZX81 cassette tape audio from binary

import wave
import struct
import sys

class ZX81CassetteEncoder:
    def __init__(self, sample_rate=44100):
        self.sample_rate = sample_rate
        self.mark_freq = 2400  # 1 bit
        self.space_freq = 1200  # 0 bit
        self.baud_rate = 1200
        
    def generate_tone(self, frequency, duration):
        """Generate sine wave tone"""
        samples = int(self.sample_rate * duration)
        tone = []
        for i in range(samples):
            value = int(32767 * 0.8 * 
                       (1 if (i * frequency * 2 // self.sample_rate) % 2 == 0 else -1))
            tone.append(value)
        return tone
    
    def encode_byte(self, byte):
        """Encode single byte as FSK audio"""
        audio = []
        bit_duration = 1.0 / self.baud_rate
        
        # Start bit (0)
        audio.extend(self.generate_tone(self.space_freq, bit_duration))
        
        # Data bits (LSB first)
        for i in range(8):
            bit = (byte >> i) & 1
            freq = self.mark_freq if bit else self.space_freq
            audio.extend(self.generate_tone(freq, bit_duration))
        
        # Stop bit (1)
        audio.extend(self.generate_tone(self.mark_freq, bit_duration))
        
        return audio
    
    def encode_program(self, data):
        """Encode complete ZX81 program"""
        audio = []
        
        # Leader tone (5 seconds of 2400 Hz)
        print("Generating leader tone...")
        audio.extend(self.generate_tone(self.mark_freq, 5.0))
        
        # Sync byte (0x00)
        audio.extend(self.encode_byte(0x00))
        
        # Program name (padded to 10 chars)
        name = b"CICADA    "
        print(f"Encoding name: {name.decode()}")
        for byte in name:
            audio.extend(self.encode_byte(byte))
        
        # Program length (2 bytes, little endian)
        length = len(data)
        print(f"Program length: {length} bytes")
        audio.extend(self.encode_byte(length & 0xFF))
        audio.extend(self.encode_byte((length >> 8) & 0xFF))
        
        # Program data
        print(f"Encoding {length} bytes...")
        for i, byte in enumerate(data):
            if i % 100 == 0:
                print(f"  {i}/{length} bytes...")
            audio.extend(self.encode_byte(byte))
        
        # Checksum
        checksum = sum(data) & 0xFF
        audio.extend(self.encode_byte(checksum))
        
        # Trailer tone (1 second)
        audio.extend(self.generate_tone(self.mark_freq, 1.0))
        
        return audio
    
    def save_wav(self, audio, filename):
        """Save audio to WAV file"""
        print(f"Writing {filename}...")
        with wave.open(filename, 'w') as wav:
            wav.setnchannels(1)  # Mono
            wav.setsampwidth(2)  # 16-bit
            wav.setframerate(self.sample_rate)
            
            # Convert to bytes
            audio_bytes = b''.join(struct.pack('<h', sample) for sample in audio)
            wav.writeframes(audio_bytes)
        
        duration = len(audio) / self.sample_rate
        print(f"✅ Created {filename}")
        print(f"   Duration: {duration:.1f} seconds")
        print(f"   Size: {len(audio_bytes)} bytes")

def main():
    if len(sys.argv) < 2:
        print("Usage: cassette_encoder.py <input.p> [output.wav]")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else input_file.replace('.p', '.wav')
    
    # Read ZX81 .P file
    print(f"📼 Reading {input_file}...")
    with open(input_file, 'rb') as f:
        data = f.read()
    
    print(f"Input size: {len(data)} bytes")
    
    # Encode to cassette audio
    encoder = ZX81CassetteEncoder()
    audio = encoder.encode_program(data)
    
    # Save WAV
    encoder.save_wav(audio, output_file)
    
    print("")
    print("🎵 Cassette tape audio ready!")
    print("")
    print("LOADING INSTRUCTIONS:")
    print("1. ZX81: Type LOAD \"\"")
    print("2. Press ENTER")
    print("3. Play audio file")
    print("4. Wait for loading screen")
    print("5. Type RUN when loaded")

if __name__ == "__main__":
    main()
