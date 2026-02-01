# Rust on ZX81: Z80 Cross-Compilation

## Overview

Compile Rust to Z80 machine code for the ZX81 (1KB RAM, 3.25 MHz).

## Toolchain Setup

### Install Z80 Target

```bash
# Add Z80 backend (via LLVM)
rustup target add z80-unknown-none

# Install z88dk (Z80 development kit)
nix-shell -p z88dk
```

### Cargo Configuration

```toml
# .cargo/config.toml
[build]
target = "z80-unknown-none"

[target.z80-unknown-none]
linker = "z88dk-z80asm"
rustflags = [
    "-C", "link-arg=-startup=0",
    "-C", "link-arg=-clib=sdcc_iy",
    "-C", "opt-level=z",  # Optimize for size
    "-C", "lto=fat",      # Link-time optimization
]
```

## Minimal Rust Program

```rust
// src/main.rs
#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

// ZX81 ROM routines
extern "C" {
    fn print_char(c: u8);
    fn print_string(s: *const u8);
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    unsafe {
        // Print "RUST ON ZX81"
        let msg = b"RUST ON ZX81\0";
        print_string(msg.as_ptr());
    }
    
    loop {}
}

// Gödel number calculator (fits in 1KB)
#[no_mangle]
pub extern "C" fn godel_calc(a: u8, b: u8, c: u8) -> u32 {
    let base_a = 2u32.pow(a as u32);
    let base_b = 3u32.pow(b as u32);
    let base_c = 5u32.pow(c as u32);
    
    base_a * base_b * base_c
}
```

## Memory Layout

```rust
// memory.x - Linker script for ZX81
MEMORY {
    ROM : ORIGIN = 0x0000, LENGTH = 8K
    RAM : ORIGIN = 0x4000, LENGTH = 1K
}

SECTIONS {
    .text : {
        *(.text.start)
        *(.text*)
    } > RAM
    
    .rodata : {
        *(.rodata*)
    } > RAM
    
    .data : {
        *(.data*)
    } > RAM
    
    .bss : {
        *(.bss*)
    } > RAM
}
```

## Cargo.toml

```toml
[package]
name = "zx81-rust"
version = "0.1.0"
edition = "2021"

[dependencies]
# No dependencies - bare metal only

[profile.release]
opt-level = "z"        # Optimize for size
lto = true             # Link-time optimization
codegen-units = 1      # Single codegen unit
panic = "abort"        # No unwinding
strip = true           # Strip symbols

[profile.release.package."*"]
opt-level = "z"
```

## Build Script

```bash
#!/bin/bash
# build-zx81.sh

set -e

echo "Building Rust for ZX81 (Z80)..."

# Build with size optimization
cargo build --release --target z80-unknown-none

# Convert ELF to ZX81 .P format
z88dk-appmake +zx81 \
    -b target/z80-unknown-none/release/zx81-rust \
    -o zx81-rust.p

# Show size
SIZE=$(stat -f%z zx81-rust.p)
echo "Binary size: $SIZE bytes (max 1024 for ZX81)"

if [ $SIZE -gt 1024 ]; then
    echo "ERROR: Binary too large for 1KB RAM!"
    exit 1
fi

echo "Success! Load with: LOAD \"zx81-rust.p\""
```

## Nix Flake

```nix
{
  description = "Rust on ZX81";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      system = "x86_64-linux";
      overlays = [ rust-overlay.overlays.default ];
      pkgs = import nixpkgs { inherit system overlays; };
      
      rust = pkgs.rust-bin.nightly.latest.default.override {
        extensions = [ "rust-src" "llvm-tools-preview" ];
        targets = [ "z80-unknown-none" ];
      };
    in {
      packages.${system} = {
        zx81-rust = pkgs.stdenv.mkDerivation {
          pname = "zx81-rust";
          version = "0.1.0";
          src = ./shard0/zx81-rust;
          
          nativeBuildInputs = [ rust pkgs.z88dk pkgs.python3 pkgs.ffmpeg ];
          
          buildPhase = ''
            cargo build --release --target z80-unknown-none
            z88dk-appmake +zx81 \
              -b target/z80-unknown-none/release/zx81-rust \
              -o cicada-level0.p
            
            # Generate cassette tape audio
            python3 cassette_encoder.py cicada-level0.p cicada-level0.wav
            
            # Convert to MP3
            ffmpeg -i cicada-level0.wav -codec:a libmp3lame -qscale:a 2 cicada-level0.mp3 -y
          '';
          
          installPhase = ''
            mkdir -p $out/bin $out/share
            cp cicada-level0.p $out/share/
            cp cicada-level0.wav $out/share/
            cp cicada-level0.mp3 $out/share/
            cp build-cassette.sh $out/bin/
            chmod +x $out/bin/build-cassette.sh
          '';
        };
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          rust
          pkgs.z88dk
          pkgs.zesarux
        ];
        
        shellHook = ''
          echo "🦀 Rust on ZX81 Development"
          echo "============================"
          echo "Build: ./build-zx81.sh"
          echo "Run:   zesarux zx81-rust.p"
          echo ""
          echo "Target: Z80 (1KB RAM)"
          echo "Optimization: -Oz (size)"
        '';
      };
    };
}
```

## Example: Gödel Calculator in Rust

```rust
// src/godel.rs
#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

// ZX81 display memory
const DISPLAY: *mut u8 = 0x4000 as *mut u8;

#[no_mangle]
pub extern "C" fn _start() -> ! {
    unsafe {
        // Clear screen
        for i in 0..768 {
            DISPLAY.add(i).write_volatile(0);
        }
        
        // Calculate Gödel number for Level 0
        let result = godel_calc(5, 3, 7);
        
        // Display result
        print_number(result);
    }
    
    loop {}
}

fn godel_calc(a: u8, b: u8, c: u8) -> u32 {
    let mut result = 1u32;
    
    // 2^a
    for _ in 0..a {
        result = result.wrapping_mul(2);
    }
    
    // * 3^b
    let mut temp = 1u32;
    for _ in 0..b {
        temp = temp.wrapping_mul(3);
    }
    result = result.wrapping_mul(temp);
    
    // * 5^c
    temp = 1;
    for _ in 0..c {
        temp = temp.wrapping_mul(5);
    }
    result = result.wrapping_mul(temp);
    
    result
}

unsafe fn print_number(mut n: u32) {
    let mut digits = [0u8; 10];
    let mut i = 0;
    
    if n == 0 {
        DISPLAY.write_volatile(b'0');
        return;
    }
    
    while n > 0 {
        digits[i] = (n % 10) as u8 + b'0';
        n /= 10;
        i += 1;
    }
    
    // Print in reverse
    for j in (0..i).rev() {
        DISPLAY.add(j).write_volatile(digits[j]);
    }
}
```

## Size Optimization Tricks

```rust
// Use u16 instead of u32 when possible
fn godel_small(a: u8, b: u8) -> u16 {
    (2u16.pow(a as u32)) * (3u16.pow(b as u32))
}

// Lookup table for small powers (saves code size)
const POW2: [u16; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
const POW3: [u16; 6] = [1, 3, 9, 27, 81, 243];
const POW5: [u16; 5] = [1, 5, 25, 125, 625];

fn godel_lut(a: u8, b: u8, c: u8) -> u32 {
    (POW2[a as usize] as u32) 
        * (POW3[b as usize] as u32) 
        * (POW5[c as usize] as u32)
}

// Inline assembly for critical paths
#[inline(always)]
unsafe fn fast_mul(a: u16, b: u16) -> u16 {
    let result: u16;
    core::arch::asm!(
        "ld hl, {a}",
        "ld de, {b}",
        "call 0x30A9",  // ZX81 ROM multiply
        "ld {result}, hl",
        a = in(reg) a,
        b = in(reg) b,
        result = out(reg) result,
    );
    result
}
```

## Testing

```bash
# Build
nix build .#zx81-rust

# Run in emulator
zesarux --machine ZX81 result/bin/zx81-rust.p

# Check size
ls -lh result/bin/zx81-rust.p

# Disassemble
z88dk-dis result/bin/zx81-rust.p
```

## Integration with CICADA-71

```rust
// Level 0 in Rust
#[no_mangle]
pub extern "C" fn cicada_level0() -> u32 {
    // Calculate 2^5 × 3^3 × 5^7
    godel_lut(5, 3, 7)  // Returns 67,500,000
}

// Modem interface
#[no_mangle]
pub extern "C" fn modem_dial(number: *const u8) {
    unsafe {
        // Send AT command
        let at_cmd = b"ATDT ";
        for &byte in at_cmd {
            serial_write(byte);
        }
        
        // Send number
        let mut ptr = number;
        while *ptr != 0 {
            serial_write(*ptr);
            ptr = ptr.add(1);
        }
        
        serial_write(b'\r');
    }
}

unsafe fn serial_write(byte: u8) {
    // ZX81 serial port (via expansion)
    const SERIAL: *mut u8 = 0xFB as *mut u8;
    SERIAL.write_volatile(byte);
}
```

This enables Rust development for the ZX81 with extreme size optimization to fit in 1KB RAM!
