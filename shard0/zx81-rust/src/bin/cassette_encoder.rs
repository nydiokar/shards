// cassette_encoder.rs - Generate ZX81 cassette tape audio from binary

use std::fs::File;
use std::io::{Write, Read};
use std::f32::consts::PI;

const SAMPLE_RATE: u32 = 44100;
const MARK_FREQ: f32 = 2400.0;  // 1 bit
const SPACE_FREQ: f32 = 1200.0; // 0 bit
const BAUD_RATE: f32 = 1200.0;

fn generate_tone(frequency: f32, duration: f32) -> Vec<i16> {
    let samples = (SAMPLE_RATE as f32 * duration) as usize;
    (0..samples)
        .map(|i| {
            let t = i as f32 / SAMPLE_RATE as f32;
            (32767.0 * 0.8 * (2.0 * PI * frequency * t).sin()) as i16
        })
        .collect()
}

fn encode_byte(byte: u8) -> Vec<i16> {
    let mut audio = Vec::new();
    let bit_duration = 1.0 / BAUD_RATE;
    
    // Start bit (0)
    audio.extend(generate_tone(SPACE_FREQ, bit_duration));
    
    // Data bits (LSB first)
    for i in 0..8 {
        let bit = (byte >> i) & 1;
        let freq = if bit == 1 { MARK_FREQ } else { SPACE_FREQ };
        audio.extend(generate_tone(freq, bit_duration));
    }
    
    // Stop bit (1)
    audio.extend(generate_tone(MARK_FREQ, bit_duration));
    
    audio
}

fn encode_program(data: &[u8]) -> Vec<i16> {
    let mut audio = Vec::new();
    
    // Leader tone (5 seconds)
    println!("Generating leader tone...");
    audio.extend(generate_tone(MARK_FREQ, 5.0));
    
    // Sync byte
    audio.extend(encode_byte(0x00));
    
    // Program name (padded to 10 chars)
    let name = b"CICADA    ";
    println!("Encoding name: {}", String::from_utf8_lossy(name));
    for &byte in name {
        audio.extend(encode_byte(byte));
    }
    
    // Program length (2 bytes, little endian)
    let length = data.len() as u16;
    println!("Program length: {} bytes", length);
    audio.extend(encode_byte((length & 0xFF) as u8));
    audio.extend(encode_byte((length >> 8) as u8));
    
    // Program data
    println!("Encoding {} bytes...", length);
    for (i, &byte) in data.iter().enumerate() {
        if i % 100 == 0 {
            println!("  {}/{} bytes...", i, length);
        }
        audio.extend(encode_byte(byte));
    }
    
    // Checksum
    let checksum = data.iter().fold(0u8, |acc, &b| acc.wrapping_add(b));
    audio.extend(encode_byte(checksum));
    
    // Trailer tone (1 second)
    audio.extend(generate_tone(MARK_FREQ, 1.0));
    
    audio
}

fn write_wav(audio: &[i16], filename: &str) -> std::io::Result<()> {
    println!("Writing {}...", filename);
    
    let mut file = File::create(filename)?;
    
    let data_size = (audio.len() * 2) as u32;
    let file_size = data_size + 36;
    
    // WAV header
    file.write_all(b"RIFF")?;
    file.write_all(&file_size.to_le_bytes())?;
    file.write_all(b"WAVE")?;
    
    // fmt chunk
    file.write_all(b"fmt ")?;
    file.write_all(&16u32.to_le_bytes())?;  // Chunk size
    file.write_all(&1u16.to_le_bytes())?;   // PCM
    file.write_all(&1u16.to_le_bytes())?;   // Mono
    file.write_all(&SAMPLE_RATE.to_le_bytes())?;
    file.write_all(&(SAMPLE_RATE * 2).to_le_bytes())?; // Byte rate
    file.write_all(&2u16.to_le_bytes())?;   // Block align
    file.write_all(&16u16.to_le_bytes())?;  // Bits per sample
    
    // data chunk
    file.write_all(b"data")?;
    file.write_all(&data_size.to_le_bytes())?;
    
    // Audio samples
    for &sample in audio {
        file.write_all(&sample.to_le_bytes())?;
    }
    
    let duration = audio.len() as f32 / SAMPLE_RATE as f32;
    println!("✅ Created {}", filename);
    println!("   Duration: {:.1} seconds", duration);
    println!("   Size: {} bytes", data_size);
    
    Ok(())
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    
    if args.len() < 2 {
        eprintln!("Usage: cassette_encoder <input.p> [output.wav]");
        std::process::exit(1);
    }
    
    let input_file = &args[1];
    let output_file = if args.len() > 2 {
        args[2].clone()
    } else {
        input_file.replace(".p", ".wav")
    };
    
    // Read ZX81 .P file
    println!("📼 Reading {}...", input_file);
    let mut file = File::open(input_file)?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;
    
    println!("Input size: {} bytes", data.len());
    
    // Encode to cassette audio
    let audio = encode_program(&data);
    
    // Save WAV
    write_wav(&audio, &output_file)?;
    
    println!();
    println!("🎵 Cassette tape audio ready!");
    println!();
    println!("LOADING INSTRUCTIONS:");
    println!("1. ZX81: Type LOAD \"\"");
    println!("2. Press ENTER");
    println!("3. Play audio file");
    println!("4. Wait for loading screen");
    println!("5. Type RUN when loaded");
    
    Ok(())
}
