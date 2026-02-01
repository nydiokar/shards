# MMIX - Knuth's RISC Architecture

MMIX implementation of the 71-shard Monster framework, using Donald E. Knuth's educational RISC architecture from *The Art of Computer Programming*.

## Architecture

- **Word size**: 64-bit (octabyte)
- **Registers**: 256 general-purpose ($0-$255)
- **Special registers**: 32 (rA, rB, rC, etc.)
- **Instruction format**: Fixed 32-bit
- **Addressing**: 64-bit virtual memory
- **Pipeline**: Simple RISC design

## Features

- Pure RISC instruction set
- No condition codes (compare returns -1/0/1)
- Load/store architecture
- Designed for teaching algorithms
- Simulator available (mmix, mmmix)

## Build

```bash
nix build .#mmix/shard-mmix
```

## Run

```bash
nix run .#mmix
# Or directly:
mmix shard0.mmo
```

## Assembly (MMIXAL)

```mmixal
% Calculate Gödel number
SET     $0,2            % Prime base
SET     $1,5            % Exponent
MUL     $2,$2,$0        % Multiply
```

## Toolchain

- `mmixal` - Assembler (MMIXAL → MMO)
- `mmix` - Simulator
- `mmmix` - Meta-simulator (traces execution)
- `mmotype` - Object file inspector

## Why MMIX?

1. **Educational**: Designed by Knuth for TAOCP
2. **Clean**: Pure RISC, no legacy cruft
3. **64-bit**: Native support for large numbers
4. **Documented**: Complete specification in TAOCP
5. **Simulator**: No hardware needed

## Gödel Calculation

Computes: 2^5 × 3^3 × 5^7 = 67,500,000

Uses three power loops with 64-bit multiplication.

## References

- *The Art of Computer Programming* Vol. 1 Fascicle 1
- MMIX Supplement (Knuth, 1999)
- https://mmix.cs.hm.edu/
