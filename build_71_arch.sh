#!/usr/bin/env bash
# Cross-compile meme detector for 71 architectures

set -e

TARGETS=(
    # x86 family (8)
    "x86_64-unknown-linux-gnu"
    "i686-unknown-linux-gnu"
    "x86_64-unknown-linux-musl"
    "i686-unknown-linux-musl"
    "x86_64-pc-windows-gnu"
    "i686-pc-windows-gnu"
    "x86_64-apple-darwin"
    "x86_64-unknown-freebsd"
    
    # ARM family (12)
    "aarch64-unknown-linux-gnu"
    "aarch64-unknown-linux-musl"
    "arm-unknown-linux-gnueabi"
    "arm-unknown-linux-gnueabihf"
    "armv7-unknown-linux-gnueabihf"
    "aarch64-apple-darwin"
    "aarch64-apple-ios"
    "aarch64-linux-android"
    "arm-linux-androideabi"
    "armv7-linux-androideabi"
    "aarch64-pc-windows-msvc"
    "thumbv7em-none-eabihf"
    
    # RISC-V family (6)
    "riscv64gc-unknown-linux-gnu"
    "riscv32i-unknown-none-elf"
    "riscv32imac-unknown-none-elf"
    "riscv32imc-unknown-none-elf"
    "riscv64imac-unknown-none-elf"
    "riscv64gc-unknown-none-elf"
    
    # MIPS family (8)
    "mips-unknown-linux-gnu"
    "mips64-unknown-linux-gnuabi64"
    "mips64el-unknown-linux-gnuabi64"
    "mipsel-unknown-linux-gnu"
    "mips-unknown-linux-musl"
    "mipsel-unknown-linux-musl"
    "mips64-unknown-linux-muslabi64"
    "mips64el-unknown-linux-muslabi64"
    
    # PowerPC family (6)
    "powerpc-unknown-linux-gnu"
    "powerpc64-unknown-linux-gnu"
    "powerpc64le-unknown-linux-gnu"
    "powerpc-unknown-linux-musl"
    "powerpc64-unknown-linux-musl"
    "powerpc64le-unknown-linux-musl"
    
    # SPARC family (3)
    "sparc64-unknown-linux-gnu"
    "sparcv9-sun-solaris"
    "sparc-unknown-linux-gnu"
    
    # S390x family (2)
    "s390x-unknown-linux-gnu"
    "s390x-unknown-linux-musl"
    
    # WASM (3)
    "wasm32-unknown-unknown"
    "wasm32-wasi"
    "wasm32-unknown-emscripten"
    
    # Embedded (8)
    "thumbv6m-none-eabi"
    "thumbv7m-none-eabi"
    "thumbv7em-none-eabi"
    "thumbv8m.base-none-eabi"
    "thumbv8m.main-none-eabi"
    "avr-unknown-gnu-atmega328"
    "msp430-none-elf"
    "nvptx64-nvidia-cuda"
    
    # BSD family (5)
    "x86_64-unknown-netbsd"
    "x86_64-unknown-openbsd"
    "aarch64-unknown-freebsd"
    "x86_64-sun-solaris"
    "x86_64-unknown-illumos"
    
    # Exotic (10)
    "wasm64-unknown-unknown"
    "hexagon-unknown-linux-musl"
    "loongarch64-unknown-linux-gnu"
    "csky-unknown-linux-gnuabiv2"
    "m68k-unknown-linux-gnu"
    "xtensa-esp32-none-elf"
    "bpf-unknown-none"
    "asmjs-unknown-emscripten"
    "x86_64-fortanix-unknown-sgx"
    "x86_64-unknown-uefi"
)

echo "🎯 Cross-compiling meme detector for 71 architectures"
echo "=" | head -c 70
echo

cd meme-detector

# Install targets
echo "📦 Installing targets..."
for target in "${TARGETS[@]}"; do
    rustup target add "$target" 2>/dev/null || echo "  ⚠️  $target not available"
done

# Build for each target
mkdir -p ../binaries
SUCCESS=0
FAILED=0

for target in "${TARGETS[@]}"; do
    echo -n "Building $target... "
    
    if cargo build --release --target "$target" 2>/dev/null; then
        echo "✓"
        cp "target/$target/release/libmeme_detector."* "../binaries/" 2>/dev/null || true
        SUCCESS=$((SUCCESS + 1))
    else
        echo "✗"
        FAILED=$((FAILED + 1))
    fi
done

echo
echo "=" | head -c 70
echo "📊 Results: $SUCCESS succeeded, $FAILED failed"
echo "✅ Binaries saved to: ../binaries/"
