# Binary Function Prediction Market - Shard 1

**Shard 1**: Bet on functions and labels inside binaries. Deep dive into symbol tables, function calls, and execution paths.

## Function-Level Betting

```
Bet on:
- Function existence (does symbol exist in binary?)
- Function calls (will function be called during execution?)
- Function execution time (< 1ms?)
- Stack depth (will recursion exceed 100 levels?)
- Memory allocation (will function allocate < 1MB?)
- Return values (will function return 0?)
- Exception handling (will function throw?)
```

## Binary Analysis Market

```rust
// function_market.rs
use goblin::elf::Elf;
use std::fs;

pub struct FunctionMarket {
    pub shard: u8,
}

impl FunctionMarket {
    pub fn analyze_binary(&self, path: &str) -> BinaryAnalysis {
        let buffer = fs::read(path).unwrap();
        let elf = Elf::parse(&buffer).unwrap();
        
        let functions: Vec<String> = elf.syms
            .iter()
            .filter(|sym| sym.st_type() == goblin::elf::sym::STT_FUNC)
            .filter_map(|sym| elf.strtab.get_at(sym.st_name))
            .map(|s| s.to_string())
            .collect();
        
        BinaryAnalysis {
            path: path.to_string(),
            functions: functions.clone(),
            function_count: functions.len(),
            symbols: elf.syms.len(),
        }
    }
    
    pub fn create_function_market(&self, binary: &str, function: &str) -> Market {
        Market {
            id: format!("{}::{}", binary, function),
            question: format!("Will {} be called during execution?", function),
            binary: binary.to_string(),
            function: function.to_string(),
            yes_stake: 0,
            no_stake: 0,
        }
    }
    
    pub fn trace_function_calls(&self, binary: &str) -> Vec<String> {
        // Use perf to trace function calls
        let output = std::process::Command::new("perf")
            .args(&["record", "-e", "probe:*", "--", binary])
            .output()
            .unwrap();
        
        // Parse perf output for function calls
        vec![] // Simplified
    }
}

#[derive(Debug)]
pub struct BinaryAnalysis {
    pub path: String,
    pub functions: Vec<String>,
    pub function_count: usize,
    pub symbols: usize,
}
```

## Symbol Table Markets

```python
# symbol_market.py
import subprocess
import re

class SymbolMarket:
    """Bet on symbols in binary"""
    
    def get_symbols(self, binary_path):
        """Extract all symbols from binary"""
        result = subprocess.run(['nm', '-D', binary_path],
                              capture_output=True, text=True)
        
        symbols = []
        for line in result.stdout.split('\n'):
            match = re.match(r'[0-9a-f]+ ([TBDW]) (.+)', line)
            if match:
                symbol_type, symbol_name = match.groups()
                symbols.append({
                    'name': symbol_name,
                    'type': symbol_type,
                    'is_function': symbol_type in ['T', 't']
                })
        
        return symbols
    
    def create_symbol_market(self, binary, symbol):
        """Create market for symbol existence"""
        symbols = self.get_symbols(binary)
        exists = any(s['name'] == symbol for s in symbols)
        
        return {
            'binary': binary,
            'symbol': symbol,
            'question': f'Does {symbol} exist in {binary}?',
            'current_state': exists,
            'yes_stake': 0,
            'no_stake': 0
        }
    
    def get_function_calls(self, binary_path):
        """Get all function calls using objdump"""
        result = subprocess.run(
            ['objdump', '-d', binary_path],
            capture_output=True, text=True
        )
        
        calls = []
        for line in result.stdout.split('\n'):
            if 'call' in line:
                match = re.search(r'<(.+)>', line)
                if match:
                    calls.append(match.group(1))
        
        return calls
```

## Dynamic Analysis Market

```javascript
// dynamic_analysis_market.js
const { spawn } = require('child_process');
const fs = require('fs');

class DynamicAnalysisMarket {
  // Trace function execution with strace
  async traceFunctionCalls(binaryPath) {
    return new Promise((resolve) => {
      const strace = spawn('strace', ['-c', binaryPath]);
      let output = '';
      
      strace.stderr.on('data', (data) => {
        output += data.toString();
      });
      
      strace.on('close', () => {
        const syscalls = this.parseSyscalls(output);
        resolve(syscalls);
      });
    });
  }
  
  // Profile function execution time
  async profileFunctions(binaryPath) {
    return new Promise((resolve) => {
      const perf = spawn('perf', ['stat', '-e', 'cycles', binaryPath]);
      let output = '';
      
      perf.stderr.on('data', (data) => {
        output += data.toString();
      });
      
      perf.on('close', () => {
        const stats = this.parsePerf(output);
        resolve(stats);
      });
    });
  }
  
  // Create market for function execution time
  createExecutionTimeMarket(binary, func, threshold_ms) {
    return {
      binary: binary,
      function: func,
      question: `Will ${func} execute in < ${threshold_ms}ms?`,
      threshold: threshold_ms,
      yes_stake: 0,
      no_stake: 0
    };
  }
  
  parseSyscalls(output) {
    // Parse strace output
    return [];
  }
  
  parsePerf(output) {
    // Parse perf output
    return {};
  }
}
```

## Label Betting

```rust
// label_market.rs
use capstone::prelude::*;

pub struct LabelMarket {
    pub shard: u8,
}

impl LabelMarket {
    pub fn disassemble(&self, binary: &[u8]) -> Vec<Label> {
        let cs = Capstone::new()
            .x86()
            .mode(arch::x86::ArchMode::Mode64)
            .build()
            .unwrap();
        
        let insns = cs.disasm_all(binary, 0x1000).unwrap();
        
        let mut labels = Vec::new();
        for insn in insns.iter() {
            if insn.mnemonic().unwrap().starts_with("j") {
                // Jump instruction - potential label
                labels.push(Label {
                    address: insn.address(),
                    name: format!("label_{:x}", insn.address()),
                });
            }
        }
        
        labels
    }
    
    pub fn create_label_market(&self, binary: &str, label: &str) -> Market {
        Market {
            id: format!("{}::label::{}", binary, label),
            question: format!("Will {} be reached during execution?", label),
            yes_stake: 0,
            no_stake: 0,
        }
    }
}

#[derive(Debug)]
pub struct Label {
    pub address: u64,
    pub name: String,
}
```

## Market Types

```yaml
function_markets:
  # Function existence
  - type: function_exists
    question: "Does function X exist in binary?"
    resolution: "nm -D binary | grep function"
    
  # Function called
  - type: function_called
    question: "Will function X be called?"
    resolution: "perf record + perf script"
    
  # Execution time
  - type: exec_time
    question: "Will function execute in < 1ms?"
    resolution: "perf stat -e cycles"
    
  # Stack depth
  - type: stack_depth
    question: "Will recursion exceed 100 levels?"
    resolution: "gdb backtrace depth"
    
  # Memory allocation
  - type: memory_alloc
    question: "Will function allocate < 1MB?"
    resolution: "valgrind --tool=massif"
    
  # Return value
  - type: return_value
    question: "Will function return 0?"
    resolution: "gdb break + print $rax"
    
  # Exception handling
  - type: exception
    question: "Will function throw exception?"
    resolution: "catch throw in gdb"
```

## Automated Analysis

```bash
#!/usr/bin/env bash
# analyze_binary_functions.sh

BINARY=$1

echo "📊 Analyzing binary: $BINARY"
echo "================================"

# Extract all functions
echo "Functions:"
nm -D "$BINARY" | grep ' T ' | awk '{print $3}' > functions.txt
FUNC_COUNT=$(wc -l < functions.txt)
echo "  Total: $FUNC_COUNT"

# Create markets for each function
while read -r func; do
  cat > "markets/func_${func}.json" <<EOF
{
  "binary": "$BINARY",
  "function": "$func",
  "question": "Will $func be called?",
  "yes_stake": 0,
  "no_stake": 0,
  "created_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF
done < functions.txt

# Trace execution
echo ""
echo "Tracing execution..."
perf record -e probe:* -- "$BINARY" --version 2>&1 | head -10

# Generate report
perf script > execution_trace.txt
CALLED_FUNCS=$(grep -o '<[^>]*>' execution_trace.txt | sort -u | wc -l)
echo "  Functions called: $CALLED_FUNCS"

# Resolve markets
echo ""
echo "Resolving markets..."
while read -r func; do
  if grep -q "$func" execution_trace.txt; then
    OUTCOME="yes"
  else
    OUTCOME="no"
  fi
  
  jq ".resolved = true | .outcome = \"$OUTCOME\"" \
    "markets/func_${func}.json" > tmp.json
  mv tmp.json "markets/func_${func}.json"
done < functions.txt

echo "✅ Analysis complete!"
```

## Dashboard

```
🔬 BINARY FUNCTION PREDICTION MARKET 🔬

Binary: /nix/store/.../bin/harbot

Function Markets:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Function                  Question                    Volume    Odds
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
main                      Will be called?            $5.2K     1.01
hunt_lobsters             Will be called?            $4.8K     1.2
collect_bisque            Will be called?            $3.9K     1.5
apply_hecke_operator      Exec time < 1ms?           $3.2K     2.1
maass_shadow_lift         Stack depth < 100?         $2.7K     1.8
check_resonance           Return 0?                  $2.1K     1.6
_start                    Will be called?            $1.9K     1.01

Label Markets:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Label                     Question                    Volume    Odds
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
.L_success                Will be reached?           $1.5K     1.4
.L_error                  Will be reached?           $1.2K     3.5
.L_loop                   Will be reached?           $0.9K     1.7

Total Functions: 247
Total Labels: 89
Total Volume: $24.5K
```

## The Complete Stack

```
PREDICTION MARKET LAYERS:

Layer 5: 🦞 Real Lobsters (Shard 69)
Layer 4: 💰 Ship Profit/Loss (Shard 70)
Layer 3: 🐙 GitHub Repos (Shard 71)
Layer 2: 📦 Nix Store Paths (Shard 0)
Layer 1: 🔬 Binary Functions (Shard 1)

From lobsters to assembly labels!
Bet on every layer of the stack! 🎯
```

🔬💰 **Bet on functions and labels!** 💰🔬
