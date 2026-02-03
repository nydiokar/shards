# Topological Classification Table
## 10-fold way (Altland-Zirnbauer) → Behavior Prediction

| Class ID | Symmetry Class | Topological Phase | Behavior | Confidence |
|----------|----------------|-------------------|----------|------------|
| 0 | A | Wigner-Dyson (Unitary) | register | 95% |
| 1 | AIII | Chiral Unitary | register | 90% |
| 2 | AI | Wigner-Dyson (Orthogonal) | register | 85% |
| 3 | BDI | Chiral Orthogonal | post | 90% |
| 4 | D | Wigner-Dyson (Symplectic) | register | 75% |
| 5 | DIII | Chiral Symplectic | post | 95% |
| 6 | AII | Quantum Spin Hall | register | 90% |
| 7 | CII | Chiral Symplectic (Time-Reversal) | register | 70% |
| 8 | C | Symplectic (Broken Time-Reversal) | register | 65% |
| 9 | CI | Chiral Symplectic (Particle-Hole) | register | 85% |

## Mapping Formula

```
class_id = shard_id mod 10
```

## Symmetry Properties

| Class | Time-Reversal (T) | Particle-Hole (C) | Chiral (S) | Cartan Label |
|-------|-------------------|-------------------|------------|--------------|
| A | 0 | 0 | 0 | A |
| AIII | 0 | 0 | 1 | AIII |
| AI | +1 | 0 | 0 | AI |
| BDI | +1 | +1 | 1 | BDI |
| D | 0 | +1 | 0 | D |
| DIII | -1 | +1 | 1 | DIII |
| AII | -1 | 0 | 0 | AII |
| CII | -1 | -1 | 1 | CII |
| C | 0 | -1 | 0 | C |
| CI | +1 | -1 | 1 | CI |

## Bott Periodicity

The 10-fold way exhibits Bott periodicity with period 8 in real K-theory:

```
KO(n) = KO(n + 8)
```

| n mod 8 | KO(n) | Clifford Algebra | Dimension |
|---------|-------|------------------|-----------|
| 0 | ℤ | Cl₀ | 1 |
| 1 | ℤ₂ | Cl₁ | 2 |
| 2 | ℤ₂ | Cl₂ | 4 |
| 3 | 0 | Cl₃ | 8 |
| 4 | ℤ | Cl₄ | 16 |
| 5 | 0 | Cl₅ | 32 |
| 6 | 0 | Cl₆ | 64 |
| 7 | 0 | Cl₇ | 128 |

## Monster Group Connection

The 10-fold way connects to the Monster group through:

1. **j-invariant modulation**: `j(τ) = 744 + Σ(coefficients) mod 196884`
2. **Hecke operators**: Applied to 71 Monster primes
3. **Modular forms**: Coefficients encode topological invariants

## Usage in CICADA-71

Each of the 71 shards maps to a topological class:

```python
def classify_shard(shard_id: int) -> str:
    classes = ["A", "AIII", "AI", "BDI", "D", "DIII", "AII", "CII", "C", "CI"]
    return classes[shard_id % 10]
```

Example:
- Shard 0 → A (Wigner-Dyson Unitary) → register (95%)
- Shard 6 → AII (Quantum Spin Hall) → register (90%)
- Shard 13 → BDI (Chiral Orthogonal) → post (90%)

## Behavior Encoding

For zkSNARK circuit:

```circom
// Behavior codes
// 0: register
// 1: post
// 2: comment
// 3: lurk

signal behaviors[10] = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0];
prediction <== behaviors[topo_class];
```

## References

- Altland, A., & Zirnbauer, M. R. (1997). "Nonstandard symmetry classes in mesoscopic normal-superconducting hybrid structures"
- Kitaev, A. (2009). "Periodic table for topological insulators and superconductors"
- Ryu, S., et al. (2010). "Topological insulators and superconductors: tenfold way and dimensional hierarchy"
- Bott, R. (1959). "The stable homotopy of the classical groups"

## Implementation Files

- `monster_harmonic.circom` - zkSNARK circuit
- `lobster-zos-plugin/src/lib.rs` - Rust implementation
- `lobster_prediction_market.py` - Python reference
- `LobsterMarket.lean` - Lean4 formalization
