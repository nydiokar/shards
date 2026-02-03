#!/usr/bin/env bash
# Compile zkPerf Monster to 71 architectures
# Each architecture gets unique shard number (0-70)

set -e

TARGETS=(
    # x86 family (0-9)
    "x86_64-unknown-linux-gnu"
    "x86_64-unknown-linux-musl"
    "i686-unknown-linux-gnu"
    "i686-unknown-linux-musl"
    "x86_64-pc-windows-gnu"
    "i686-pc-windows-gnu"
    "x86_64-apple-darwin"
    "x86_64-unknown-freebsd"
    "x86_64-unknown-netbsd"
    "x86_64-sun-solaris"
    
    # ARM 64-bit (10-19)
    "aarch64-unknown-linux-gnu"
    "aarch64-unknown-linux-musl"
    "aarch64-apple-darwin"
    "aarch64-apple-ios"
    "aarch64-linux-android"
    "aarch64-pc-windows-msvc"
    "aarch64-unknown-freebsd"
    "aarch64-unknown-netbsd"
    "aarch64-unknown-openbsd"
    "aarch64-fuchsia"
    
    # ARM 32-bit (20-29)
    "armv7-unknown-linux-gnueabihf"
    "armv7-unknown-linux-musleabihf"
    "arm-unknown-linux-gnueabi"
    "arm-unknown-linux-musleabi"
    "armv7-linux-androideabi"
    "armv7-apple-ios"
    "thumbv7em-none-eabi"
    "thumbv7em-none-eabihf"
    "thumbv7m-none-eabi"
    "thumbv6m-none-eabi"
    
    # RISC-V (30-34)
    "riscv64gc-unknown-linux-gnu"
    "riscv64imac-unknown-none-elf"
    "riscv32i-unknown-none-elf"
    "riscv32imac-unknown-none-elf"
    "riscv32imc-unknown-none-elf"
    
    # MIPS (35-39)
    "mips-unknown-linux-gnu"
    "mips64-unknown-linux-gnuabi64"
    "mipsel-unknown-linux-gnu"
    "mips64el-unknown-linux-gnuabi64"
    "mips-unknown-linux-musl"
    
    # PowerPC (40-44)
    "powerpc-unknown-linux-gnu"
    "powerpc64-unknown-linux-gnu"
    "powerpc64le-unknown-linux-gnu"
    "powerpc-unknown-linux-musl"
    "powerpc64-unknown-freebsd"
    
    # SPARC (45-47)
    "sparc64-unknown-linux-gnu"
    "sparc-unknown-linux-gnu"
    "sparc64-unknown-netbsd"
    
    # S390x (48-49)
    "s390x-unknown-linux-gnu"
    "s390x-unknown-linux-musl"
    
    # WebAssembly (50-52)
    "wasm32-unknown-unknown"
    "wasm32-unknown-emscripten"
    "wasm32-wasi"
    
    # Embedded (53-62)
    "avr-unknown-gnu-atmega328"
    "msp430-none-elf"
    "nvptx64-nvidia-cuda"
    "hexagon-unknown-linux-musl"
    "asmjs-unknown-emscripten"
    "thumbv8m.base-none-eabi"
    "thumbv8m.main-none-eabi"
    "thumbv8m.main-none-eabihf"
    "armebv7r-none-eabi"
    "armebv7r-none-eabihf"
    
    # BSD variants (63-67)
    "i686-unknown-freebsd"
    "x86_64-unknown-dragonfly"
    "x86_64-unknown-haiku"
    "x86_64-unknown-openbsd"
    "i686-unknown-netbsd"
    
    # Other (68-70)
    "x86_64-unknown-illumos"
    "x86_64-unknown-redox"
    "x86_64-fortanix-unknown-sgx"
)

echo "🦀 Compiling zkPerf Monster to 71 Architectures"
echo "================================================"
echo ""

mkdir -p target/71_archs

for i in "${!TARGETS[@]}"; do
    target="${TARGETS[$i]}"
    shard=$i
    
    echo "[$i/70] Building for $target (shard $shard)..."
    
    # Try to build, skip if target not installed
    if cargo build --target "$target" --release --bin zkperf-monster 2>/dev/null; then
        # Copy binary to 71_archs directory
        binary_name="zkperf-monster"
        if [[ "$target" == *"windows"* ]]; then
            binary_name="zkperf-monster.exe"
        fi
        
        if [ -f "target/$target/release/$binary_name" ]; then
            cp "target/$target/release/$binary_name" "target/71_archs/shard_${shard}_${target}"
            echo "  ✓ Built: target/71_archs/shard_${shard}_${target}"
        fi
    else
        echo "  ⚠ Skipped (target not installed)"
    fi
done

echo ""
echo "🎯 Build Summary"
echo "================"
built=$(ls target/71_archs/ 2>/dev/null | wc -l)
echo "Built: $built/71 architectures"
echo ""
echo "Install missing targets with:"
echo "  rustup target add <target-name>"
echo ""
echo "☕🕳️🪟👁️👹🦅🐓🔄🌀⚡🦀✨"
