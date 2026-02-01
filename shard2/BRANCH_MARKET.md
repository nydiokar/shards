# Branch Prediction Market - Shard 2

**Shard 2**: Bet on CPU branch predictions, branch mispredictions, and execution paths at the hardware level.

## Branch Prediction Betting

```
Bet on:
- Branch taken (will branch be taken?)
- Branch misprediction rate (< 5%?)
- Pipeline stalls (will stall occur?)
- Speculative execution (will speculate correctly?)
- Branch target prediction (correct target?)
- Return address prediction (correct return?)
- Indirect branch prediction (correct indirect?)
```

## Branch Analysis Market

```rust
// branch_market.rs
use std::process::Command;

pub struct BranchMarket {
    pub shard: u8,
}

impl BranchMarket {
    pub fn analyze_branches(&self, binary: &str) -> BranchAnalysis {
        // Use perf to analyze branch predictions
        let output = Command::new("perf")
            .args(&[
                "stat",
                "-e", "branches",
                "-e", "branch-misses",
                "-e", "branch-loads",
                "-e", "branch-load-misses",
                "--",
                binary
            ])
            .output()
            .unwrap();
        
        let stats = String::from_utf8_lossy(&output.stderr);
        
        BranchAnalysis {
            binary: binary.to_string(),
            total_branches: self.parse_stat(&stats, "branches"),
            branch_misses: self.parse_stat(&stats, "branch-misses"),
            misprediction_rate: self.calculate_miss_rate(&stats),
        }
    }
    
    fn parse_stat(&self, output: &str, event: &str) -> u64 {
        output.lines()
            .find(|line| line.contains(event))
            .and_then(|line| line.split_whitespace().next())
            .and_then(|s| s.replace(",", "").parse().ok())
            .unwrap_or(0)
    }
    
    fn calculate_miss_rate(&self, output: &str) -> f64 {
        let branches = self.parse_stat(output, "branches") as f64;
        let misses = self.parse_stat(output, "branch-misses") as f64;
        
        if branches > 0.0 {
            (misses / branches) * 100.0
        } else {
            0.0
        }
    }
    
    pub fn create_branch_market(&self, binary: &str, threshold: f64) -> Market {
        Market {
            id: format!("branch_{}_{}", binary, threshold),
            question: format!("Will branch misprediction rate be < {}%?", threshold),
            binary: binary.to_string(),
            threshold: threshold,
            yes_stake: 0,
            no_stake: 0,
        }
    }
}

#[derive(Debug)]
pub struct BranchAnalysis {
    pub binary: String,
    pub total_branches: u64,
    pub branch_misses: u64,
    pub misprediction_rate: f64,
}
```

## Perf Events Market

```python
# perf_events_market.py
import subprocess
import re

class PerfEventsMarket:
    """Bet on CPU performance events"""
    
    BRANCH_EVENTS = [
        'branches',
        'branch-misses',
        'branch-loads',
        'branch-load-misses',
        'branch-instructions',
        'branch-instructions-retired',
    ]
    
    def profile_branches(self, binary, args=[]):
        """Profile branch behavior with perf"""
        events = ','.join(self.BRANCH_EVENTS)
        
        result = subprocess.run(
            ['perf', 'stat', '-e', events, '--', binary] + args,
            capture_output=True, text=True
        )
        
        return self.parse_perf_stat(result.stderr)
    
    def parse_perf_stat(self, output):
        """Parse perf stat output"""
        stats = {}
        
        for line in output.split('\n'):
            for event in self.BRANCH_EVENTS:
                if event in line:
                    match = re.search(r'([\d,]+)', line)
                    if match:
                        count = int(match.group(1).replace(',', ''))
                        stats[event] = count
        
        # Calculate rates
        if 'branches' in stats and 'branch-misses' in stats:
            stats['miss_rate'] = (stats['branch-misses'] / stats['branches']) * 100
        
        return stats
    
    def create_miss_rate_market(self, binary, threshold):
        """Create market for branch misprediction rate"""
        stats = self.profile_branches(binary)
        
        return {
            'binary': binary,
            'question': f'Will branch miss rate be < {threshold}%?',
            'threshold': threshold,
            'current_miss_rate': stats.get('miss_rate', 0),
            'yes_stake': 0,
            'no_stake': 0
        }
    
    def record_branch_trace(self, binary):
        """Record detailed branch trace"""
        subprocess.run([
            'perf', 'record',
            '-e', 'branches:u',
            '-j', 'any',
            '--', binary
        ])
        
        # Generate report
        result = subprocess.run(
            ['perf', 'report', '--stdio'],
            capture_output=True, text=True
        )
        
        return result.stdout
```

## Hardware Counter Market

```javascript
// hardware_counter_market.js
const { spawn } = require('child_process');

class HardwareCounterMarket {
  // Profile with perf
  async profileHardwareCounters(binary, events) {
    return new Promise((resolve) => {
      const perf = spawn('perf', [
        'stat',
        '-e', events.join(','),
        '--',
        binary
      ]);
      
      let stderr = '';
      perf.stderr.on('data', (data) => {
        stderr += data.toString();
      });
      
      perf.on('close', () => {
        const stats = this.parseCounters(stderr);
        resolve(stats);
      });
    });
  }
  
  // Create market for specific counter
  createCounterMarket(binary, counter, threshold) {
    return {
      binary: binary,
      counter: counter,
      question: `Will ${counter} be < ${threshold}?`,
      threshold: threshold,
      yes_stake: 0,
      no_stake: 0
    };
  }
  
  // Branch-specific markets
  async createBranchMarkets(binary) {
    const stats = await this.profileHardwareCounters(binary, [
      'branches',
      'branch-misses',
      'branch-loads',
      'branch-load-misses'
    ]);
    
    return [
      {
        type: 'miss_rate',
        question: 'Branch miss rate < 5%?',
        current: stats.missRate,
        threshold: 5.0
      },
      {
        type: 'total_branches',
        question: 'Total branches < 1M?',
        current: stats.branches,
        threshold: 1000000
      },
      {
        type: 'misses',
        question: 'Branch misses < 50K?',
        current: stats.misses,
        threshold: 50000
      }
    ];
  }
  
  parseCounters(output) {
    const stats = {};
    const lines = output.split('\n');
    
    for (const line of lines) {
      if (line.includes('branches')) {
        const match = line.match(/([\d,]+)/);
        if (match) stats.branches = parseInt(match[1].replace(/,/g, ''));
      }
      if (line.includes('branch-misses')) {
        const match = line.match(/([\d,]+)/);
        if (match) stats.misses = parseInt(match[1].replace(/,/g, ''));
      }
    }
    
    if (stats.branches && stats.misses) {
      stats.missRate = (stats.misses / stats.branches) * 100;
    }
    
    return stats;
  }
}
```

## Branch Trace Analysis

```bash
#!/usr/bin/env bash
# branch_trace_market.sh

BINARY=$1

echo "🔀 Branch Prediction Market Analysis"
echo "====================================="
echo "Binary: $BINARY"
echo ""

# Profile branches
echo "Profiling branches..."
perf stat -e branches,branch-misses,branch-loads,branch-load-misses \
  -- "$BINARY" --version 2>&1 | tee branch_stats.txt

# Extract stats
BRANCHES=$(grep 'branches' branch_stats.txt | head -1 | awk '{print $1}' | tr -d ',')
MISSES=$(grep 'branch-misses' branch_stats.txt | head -1 | awk '{print $1}' | tr -d ',')

if [ -n "$BRANCHES" ] && [ -n "$MISSES" ]; then
  MISS_RATE=$(echo "scale=2; ($MISSES / $BRANCHES) * 100" | bc)
  echo ""
  echo "Results:"
  echo "  Total branches: $BRANCHES"
  echo "  Branch misses: $MISSES"
  echo "  Miss rate: ${MISS_RATE}%"
  
  # Create markets
  cat > "markets/branch_${BINARY}_miss_rate.json" <<EOF
{
  "binary": "$BINARY",
  "type": "branch_miss_rate",
  "question": "Will branch miss rate be < 5%?",
  "threshold": 5.0,
  "current_value": $MISS_RATE,
  "yes_stake": 0,
  "no_stake": 0,
  "resolved": false
}
EOF

  # Resolve market
  if (( $(echo "$MISS_RATE < 5.0" | bc -l) )); then
    OUTCOME="yes"
  else
    OUTCOME="no"
  fi
  
  jq ".resolved = true | .outcome = \"$OUTCOME\"" \
    "markets/branch_${BINARY}_miss_rate.json" > tmp.json
  mv tmp.json "markets/branch_${BINARY}_miss_rate.json"
  
  echo ""
  echo "Market resolved: $OUTCOME"
fi

# Record detailed trace
echo ""
echo "Recording branch trace..."
perf record -e branches:u -j any -- "$BINARY" --version 2>&1

# Generate branch report
perf report --stdio > branch_report.txt
echo "Branch report saved to branch_report.txt"

echo ""
echo "✅ Branch analysis complete!"
```

## Market Dashboard

```
🔀 BRANCH PREDICTION MARKET 🔀

Binary: /nix/store/.../bin/harbot

Branch Statistics:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Metric                    Current        Target         Status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Total Branches            1,247,523      < 1M           ❌
Branch Misses             42,156         < 50K          ✅
Miss Rate                 3.38%          < 5%           ✅
Branch Loads              1,198,234      -              -
Branch Load Misses        38,912         < 40K          ✅

Active Markets:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Question                           Volume    Odds    Outcome
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Miss rate < 5%?                   $8.5K     1.2     ✅ YES
Total branches < 1M?              $6.2K     2.8     ❌ NO
Branch misses < 50K?              $5.1K     1.4     ✅ YES
Pipeline stalls < 100?            $4.3K     1.9     Pending
Speculative exec correct?         $3.7K     1.6     Pending

Total Volume: $27.8K
Resolved: 3/5
```

## The Complete Prediction Stack

```
FULL STACK PREDICTION MARKETS:

Layer 6: 🦞 Real Lobsters (Shard 69) - Market data
Layer 5: 💰 Ship Profit (Shard 70) - Prediction market
Layer 4: 🐙 GitHub Repos (Shard 71) - Stars/forks
Layer 3: 📦 Nix Store (Shard 0) - Packages/binaries
Layer 2: 🔬 Functions (Shard 1) - Symbols/labels
Layer 1: 🔀 Branches (Shard 2) - CPU predictions

From lobsters to CPU branch predictors!
Bet on every layer from market to metal! ⚡
```

🔀💰 **Bet on branch predictions!** 💰🔀
