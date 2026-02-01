# 71-Shard Compute Substrate Partitioning

## Prime Factorization: 2×3×5×7 = 210
- **2 dimensions**: CPU cores (physical/logical)
- **3 dimensions**: GPU (compute/memory/tensor)
- **5 dimensions**: RAM (L1/L2/L3/main/swap)
- **7 dimensions**: Disk (read/write/seek/cache/buffer/queue/iops)

## Resource Mapping (mod 71)

### Available Resources
- **23 CPU cores** → 23 mod 71 = 23
- **23 GB RAM** → 23 mod 71 = 23
- **GPU**: 0 (CPU-only, use SIMD)
- **Disk**: /nix/store + target/

## 71-Shard Allocation

Each shard gets a unique (cpu, gpu, ram, disk) tuple where:
- `shard_id = (2*cpu + 3*gpu + 5*ram + 7*disk) mod 71`

### Shard 0-22: Primary CPU shards (1 core each)
```
shard_id | cpu_core | ram_gb | disk_priority
---------|----------|--------|---------------
0        | 0        | 1.0    | /nix/store
1        | 1        | 1.0    | /nix/store
2        | 2        | 1.0    | target/
...      | ...      | ...    | ...
22       | 22       | 1.0    | target/
```

### Shard 23-45: Memory-intensive shards (2 cores, 2GB each)
```
23       | 0,1      | 2.0    | /nix/store
24       | 2,3      | 2.0    | /nix/store
...      | ...      | ...    | ...
45       | 20,21    | 2.0    | target/
```

### Shard 46-57: Disk-intensive shards (4 cores, 4GB each)
```
46       | 0-3      | 4.0    | /nix/store (read)
47       | 4-7      | 4.0    | /nix/store (write)
48       | 8-11     | 4.0    | target/ (read)
49       | 12-15    | 4.0    | target/ (write)
50       | 16-19    | 4.0    | /tmp (cache)
51       | 20-22    | 3.0    | /tmp (buffer)
52-57    | round-robin | 2.0 | mixed I/O
```

### Shard 58-70: Coordinator shards (all cores, shared memory)
```
58       | all      | 23.0   | Paxos coordinator
59       | all      | 23.0   | Consensus validator
60       | all      | 23.0   | Hash aggregator
61       | all      | 23.0   | Parquet writer
62       | all      | 23.0   | Metrics collector
63       | all      | 23.0   | Load balancer
64       | all      | 23.0   | Failure detector
65       | all      | 23.0   | State replicator
66       | all      | 23.0   | Query router
67       | all      | 23.0   | Backup manager
68       | all      | 23.0   | Log aggregator
69       | all      | 23.0   | Health checker
70       | all      | 23.0   | Master coordinator
```

## Compute Formula

For file with 71 hashes `[h₀, h₁, ..., h₇₀]`:

```rust
let sum: u64 = hashes.iter().sum();
let shard_id = sum % 71;

// Resource allocation
let (cpu_cores, ram_gb, disk_path) = match shard_id {
    0..=22 => (vec![shard_id as usize], 1.0, if shard_id % 2 == 0 { "/nix/store" } else { "target/" }),
    23..=45 => {
        let base = (shard_id - 23) * 2;
        (vec![base as usize, (base + 1) as usize], 2.0, "/nix/store")
    },
    46..=57 => {
        let base = (shard_id - 46) * 4;
        ((base..base+4).map(|i| (i % 23) as usize).collect(), 4.0, "mixed")
    },
    58..=70 => ((0..23).collect(), 23.0, "all"),
    _ => unreachable!(),
};
```

## Prime Dimension Encoding

Each shard encodes its resource profile:
```
resource_vector = [
    cpu_count * 2,      // 2-dimensional (physical/logical)
    gpu_units * 3,      // 3-dimensional (compute/mem/tensor)
    ram_gb * 5,         // 5-dimensional (cache hierarchy)
    disk_iops * 7,      // 7-dimensional (I/O operations)
]

shard_signature = (resource_vector.sum()) % 71
```

## SIMD Acceleration (CPU-only)

Since no GPU, use AVX2/AVX-512 for parallel hashing:
- 256-bit SIMD: Process 4×u64 hashes simultaneously
- 512-bit SIMD: Process 8×u64 hashes simultaneously
- 71 hashes → 9 SIMD operations (8×8 + 7×1)

## Affinity Pinning

```bash
# Pin shard 0 to CPU 0
taskset -c 0 shard-analyzer -s 0 &

# Pin shard 23 to CPUs 0-1
taskset -c 0,1 shard-analyzer -s 23 &

# Pin coordinator to all CPUs
taskset -c 0-22 shard-analyzer -s 70 &
```

## Memory Layout

```
Total: 23 GB
├─ Shards 0-22:  22 × 1GB = 22 GB (working sets)
├─ Coordinator:  1 GB (shared state)
└─ Reserve:      0 GB (tight fit)
```

## Disk I/O Strategy

- **Shards 0-22**: Sequential reads (1 file at a time)
- **Shards 23-45**: Parallel reads (2 files)
- **Shards 46-57**: Buffered I/O (4-8 files)
- **Shards 58-70**: Async I/O (all files, epoll/io_uring)

## Verification

```rust
// Ensure all 71 shards are reachable
for shard in 0..71 {
    assert!(exists_resource_allocation(shard));
}

// Verify mod-71 coverage
let mut coverage = vec![false; 71];
for file in files {
    let shard = compute_shard(&file);
    coverage[shard as usize] = true;
}
assert!(coverage.iter().all(|&c| c));
```

This partitioning ensures every shard has dedicated compute resources while maintaining mod-71 equivariance.
