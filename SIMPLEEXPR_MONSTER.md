# SimpleExpr → Monster Tower Integration

**Status:** ✅ Complete (2026-02-02)

## Architecture

```
Lean4 SimpleExpr → MiniZinc Optimization → Rust Compiler → Brainfuck
       ↓                    ↓                    ↓              ↓
   Formal Proof      Tower Height: 169    Type-safe JSON   8 operations
```

## Components

### 1. MiniZinc Model (`simpleexpr_monster.mzn`)
- Maps 6 constructors → 6 Monster folds
- Optimizes via crown primes (2, 71, 47, 19, 17, 13)
- Generates Brainfuck compilation table

### 2. Lean4 Proof (`SimpleExprMonster.lean`)
```lean
theorem cusp_is_max : ∀ f, fold_prime .cusp ≥ fold_prime f
theorem tower_height_bounded : sum = 170
```

### 3. Rust Compiler (`src/simpleexpr_monster.rs`)
- Parses MicroLean4 JSON
- Compiles to Brainfuck via Monster Tower
- Type-safe with serde

### 4. Nix Build (`flake_simpleexpr.nix`)
- Pure, reproducible builds
- No direct cargo calls
- Dependencies: minizinc, lean4, rustc

### 5. Pipelight Pipeline (`pipelight.toml`)
```toml
[[pipelines]]
name = "simpleexpr"
steps = [minizinc, lean4-proof, rust-build]
```

## Mapping

| SimpleExpr | Fold | Prime | Brainfuck | Meaning |
|------------|------|-------|-----------|---------|
| BVAR       | F1   | 71    | `+><`     | Cusp (self-ref) |
| SORT       | F0   | 2     | `++[>+<]` | Bootstrap |
| CONST      | F2   | 47    | `[>+<]`   | Spacetime |
| APP        | F3   | 19    | `>>+`     | Arrows |
| LAM        | F4   | 17    | `+++[>]`  | Type Symmetry |
| FORALL     | F5   | 13    | `++++[>>]`| Dependent Types |

## Usage

```bash
# Run full integration
./run_simpleexpr_nix.sh

# Or via Pipelight
pipelight run simpleexpr
```

## Tower Height

**169** = 2 + 71 + 47 + 19 + 17 + 13

The cusp (GF(71)) dominates, as proven in Lean4.

## Next Steps

- [ ] Parse 906 Brainfuck files
- [ ] Implement full Scheme→BF compiler
- [ ] Generate zkPerf proofs
- [ ] Deploy to 71 shards
