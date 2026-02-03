# Reproducible Science Lab - Nix Flake

## Quick Start

```bash
# Enter full science lab
nix develop

# Enter Monster-specific environment
nix develop .#monster

# Enter minimal environment (Lean4 + Z3 + MiniZinc)
nix develop .#minimal

# Run science lab app
nix run .#lab

# Run Monster app
nix run .#monster

# Build Docker container
nix build .#scienceLabContainer
docker load < result
```

## Available Shells

### Default (Full Science Lab)
```bash
nix develop
```

**Includes:**
- Math: GAP, PARI/GP, Maxima
- Proof: Lean4, Coq, Z3, CVC5
- Logic: SWI-Prolog
- Lisp: SBCL
- Constraint: MiniZinc
- Python: numpy, scipy, sympy, networkx, z3-solver
- Tools: bc, jq, graphviz

### Monster (Monster Group Analysis)
```bash
nix develop .#monster
```

**Includes:**
- GAP (Monster group computations)
- Lean4 (formal proofs)
- MiniZinc (symmetry optimization)
- Z3 (SMT solving)
- Python (numerical analysis)
- Tools: bc, jq, graphviz

### Minimal (Proof + Constraint)
```bash
nix develop .#minimal
```

**Includes:**
- Lean4
- Z3
- MiniZinc
- bc, jq

## Reproducibility

All packages pinned via Nix flake:
- No `pip install` (Python packages via `python311.withPackages`)
- No `npm install` (not needed)
- No `cargo install` (Rust via `rustPlatform.buildRustPackage`)
- No system dependencies (everything in Nix store)

**Hash:** `nix flake metadata` shows exact commit

## Buildkite Integration

```bash
# Upload pipeline
buildkite-agent pipeline upload .buildkite/pipeline.yml
```

**Pipeline steps:**
1. Package audit
2. GAP tests (Monster order)
3. Lean4 proofs
4. MiniZinc optimization
5. Maass spectrum analysis
6. Shard analysis
7. Integration tests
8. Container build
9. Deploy

## Docker Container

```bash
# Build
nix build .#scienceLabContainer

# Load
docker load < result

# Run
docker run -it tradewars-science-lab:latest

# Test
docker run --rm tradewars-science-lab:latest gap --version
```

## Testing

```bash
# Test all shells
./test_science_lab.sh

# Test specific shell
nix develop .#monster --command bash -c "gap --version"
```

## Advisory Board Recommendations

**Spock**: "Logical. Nix provides reproducibility via content-addressed store. No dependency hell."

**Data**: "Analysis: Flake lock ensures bit-for-bit reproducibility. 47 packages, single hash."

**Marvin**: "Oh wonderful. Nix. That'll solve everything. Until it doesn't. Life? Don't talk to me."

**HAL**: "All systems nominal. Reproducible builds within acceptable parameters. Mission critical."

## Files

- `flake.nix` - Main flake definition
- `flake.lock` - Locked dependencies (auto-generated)
- `.buildkite/pipeline.yml` - CI/CD pipeline
- `test_science_lab.sh` - Shell tests

## Commands

```bash
# Update flake
nix flake update

# Show flake info
nix flake show

# Check flake
nix flake check

# Build all packages
nix build .#scienceLabContainer

# Enter shell
nix develop

# Run app
nix run .#lab
```

∴ Reproducible science lab via Nix ✓
