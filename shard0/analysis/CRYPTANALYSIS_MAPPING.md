# 71 Cryptanalysis Methods Mapped to 71 Shards

## Shard Assignment Strategy

Each shard applies one cryptanalysis technique to the build artifacts, treating compiled code and data as "encrypted" information to be analyzed.

## Tier 1: Statistical Analysis (Shards 0-9)

**Shard 0**: Frequency analysis on byte distributions in binaries
**Shard 1**: Index of coincidence on instruction sequences
**Shard 2**: Kasiski examination on repeating code patterns (+ perf registers)
**Shard 3**: N-gram frequency (2,3,5,7-byte sequences)
**Shard 4**: Autocorrelation on function call patterns
**Shard 5**: Chi-square tests on symbol distributions
**Shard 6**: Language model scoring (assembly mnemonics)
**Shard 7**: Hill-climbing search for optimization patterns
**Shard 8**: Simulated annealing on code layout
**Shard 9**: Structural marker detection (function boundaries)

## Tier 2: Differential Analysis (Shards 10-25)

**Shard 10**: Differential analysis on compiler output variations
**Shard 11**: Truncated differential on optimization levels
**Shard 12**: Higher-order differential on inlining decisions
**Shard 13**: Impossible differential (code paths that never occur)
**Shard 14**: Improbable differential (rare optimization patterns)
**Shard 15**: Boomerang attack on build pipeline stages
**Shard 16**: Rectangle attack on multi-stage compilation
**Shard 17**: Linear approximation of compiler transformations
**Shard 18**: Multiple linear analysis on optimization passes
**Shard 19**: Differential-linear on LLVM IR → assembly
**Shard 20**: Integral analysis (XOR-sum of outputs)
**Shard 21**: Mod-n analysis on alignment and padding
**Shard 22**: Partitioning attack on code sections
**Shard 23**: Slide attack on repeated build patterns
**Shard 24**: Sandwich attack on middle compilation stages
**Shard 25**: XSL-style algebraic on instruction selection

## Tier 3: Time-Memory-Data Tradeoffs (Shards 26-31)

**Shard 26**: Brute-force search on build configurations
**Shard 27**: Meet-in-the-middle on dependency chains
**Shard 28**: Hellman tables for common code patterns
**Shard 29**: Rainbow tables for symbol hashes
**Shard 30**: Distinguished-point collision search
**Shard 31**: Hash-chain analysis on build artifacts

## Tier 4: Attack Models (Shards 32-39)

**Shard 32**: Ciphertext-only (binary-only analysis)
**Shard 33**: Known-plaintext (source + binary pairs)
**Shard 34**: Chosen-plaintext (controlled inputs)
**Shard 35**: Adaptive chosen-plaintext (iterative builds)
**Shard 36**: Chosen-ciphertext (decompilation analysis)
**Shard 37**: Adaptive chosen-ciphertext (fuzzing)
**Shard 38**: Chosen-message (signature verification)
**Shard 39**: Harvest now, decrypt later (archive for future analysis)

## Tier 5: Side-Channel Analysis (Shards 40-49)

**Shard 40**: Simple power analysis on build energy
**Shard 41**: Differential power analysis on CPU usage
**Shard 42**: Correlation power analysis
**Shard 43**: Template attacks on build profiles
**Shard 44**: Timing analysis of compilation stages
**Shard 45**: Cache-timing (Prime+Probe on builds)
**Shard 46**: EM side-channel (disk I/O patterns)
**Shard 47**: Fault analysis (corrupted builds)
**Shard 48**: Differential fault analysis
**Shard 49**: Glitch/clock/voltage fault traces

## Tier 6: Algebraic & Structural (Shards 50-56)

**Shard 50**: Polynomial equations over dependency graphs
**Shard 51**: SAT/SMT encoding of build constraints
**Shard 52**: Gröbner-basis on package relations
**Shard 53**: Group-structure analysis (version graphs)
**Shard 54**: Lattice-based analysis on build entropy
**Shard 55**: Meet-in-the-middle on version space
**Shard 56**: Weak diffusion analysis (propagation of changes)

## Tier 7: Protocol & Usage (Shards 57-65)

**Shard 57**: Key reuse analysis (same deps across builds)
**Shard 58**: Plaintext structure (ELF headers, metadata)
**Shard 59**: Padding-oracle (alignment, section padding)
**Shard 60**: Format-oracle (valid ELF, valid signatures)
**Shard 61**: Replay patterns (cached builds)
**Shard 62**: Traffic-flow (build log patterns)
**Shard 63**: Cross-protocol (Nix + Cargo + LLVM)
**Shard 64**: Version fingerprinting
**Shard 65**: Nonce/mode misuse (build IDs, timestamps)

## Tier 8: Hash/MAC/Password (Shards 66-70)

**Shard 66**: Birthday-paradox collision on hashes
**Shard 67**: Differential analysis on hash functions
**Shard 68**: Length-extension on build hashes
**Shard 69**: Password-guessing (weak keys in builds)
**Shard 70**: Entropy estimation of build randomness

## Implementation

Each shard runs its assigned cryptanalysis technique on:
- Build artifacts (binaries, libraries, objects)
- Intermediate representations (LLVM IR, MIR)
- Build logs and metadata
- Performance traces
- Dependency graphs

Results stored in `shard{N}/data/parquet/analysis.parquet`

## Usage

```bash
# Run analysis on specific shard
nix develop .#level{N}
analyze {N} <target>

# Run all 71 analyses in parallel
parallel -j 23 'analyze {} target' ::: {0..70}
```
