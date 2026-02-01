# MiniZinc → LLVM → WASM Emoji Optimizer

Compile MiniZinc constraint solver to WebAssembly via LLVM.

## Pipeline

```
emoji_optimization.mzn (MiniZinc)
    ↓ minizinc --compile
emoji_opt.fzn (FlatZinc)
    ↓ convert to C
emoji_opt.c (C code)
    ↓ clang -emit-llvm
emoji_opt.ll (LLVM IR)
    ↓ opt -O3
emoji_opt_opt.ll (Optimized IR)
    ↓ emcc
emoji_opt.wasm (WebAssembly)
```

## Build

```bash
nix build .#emoji-optimizer-wasm
./result/bin/emoji-optimizer
```

## Run in Browser

```bash
nix develop
python -m http.server 8000
open http://localhost:8000
```

## What It Does

1. Takes 50 emoji candidates
2. Selects best 20 by frequency
3. Ensures core emojis included: 🔮⚡🕳️🛋️🔐
4. Maximizes total frequency score
5. Runs in browser via WASM

## Tech Stack

- **MiniZinc**: Constraint programming
- **LLVM**: Intermediate representation
- **Emscripten**: LLVM → WASM compiler
- **Nix**: Reproducible builds

## English ↔ Emoji Translator

Bidirectional translation between English and emojis.

### CLI Usage

```bash
./translate.js magic energy hole
# Output: 🔮 ⚡ 🕳️

./translate.js hecke operator eternal proof qed
# Output: 🔮 ⚙️ ♾️ ✅ ✅
```

### Browser Usage

```bash
python -m http.server 8000
open http://localhost:8000/translator.html
```

### Examples

- `magic energy hole` → `🔮 ⚡ 🕳️`
- `hecke operator eternal` → `🔮 ⚙️ ♾️`
- `proof verify qed` → `✅ ✔️ ✅`
- `compile build deploy` → `⚙️ 🔨 🚀`

### Dictionary (71 words)

Core: magic, energy, hole, ikea, spiral, sparkle, music, lock, math, wave

Math: hecke, maass, mock, shadow, harmonic, zen, proof, shard, jail, sus, prime, gandalf, eternal, ephemeral, ontology, operator, form, modular, automorphic, moonshine, monster, group, supersingular, elliptic, curve, invariant, coefficient, theorem, lemma, conjecture, axiom, qed, verify, witness, groth16

Actions: compile, build, deploy, test, run

🔮⚡✨
