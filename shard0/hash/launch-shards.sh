#!/usr/bin/env bash
# Launch 71 shards with CPU affinity

set -euo pipefail

BINARY="./target/release/ingest"
DATA_DIR="./shard0/data/parquet"

echo "Launching 71 shards with compute partitioning..."

for shard in {0..70}; do
    # Get CPU affinity for this shard
    case $shard in
        [0-9]|1[0-9]|2[0-2])  # Shards 0-22: single core
            CPUS=$shard
            ;;
        2[3-9]|3[0-9]|4[0-5])  # Shards 23-45: dual core
            base=$(( (shard - 23) * 2 ))
            core1=$(( base % 23 ))
            core2=$(( (base + 1) % 23 ))
            CPUS="$core1,$core2"
            ;;
        4[6-9]|5[0-7])  # Shards 46-57: quad core
            base=$(( (shard - 46) * 4 ))
            CPUS=$(seq -s, $base $((base + 3)) | sed 's/[0-9]\+/&%23/g' | bc | tr '\n' ',' | sed 's/,$//')
            ;;
        *)  # Shards 58-70: all cores
            CPUS="0-22"
            ;;
    esac

    echo "Shard $shard -> CPUs $CPUS"
    taskset -c "$CPUS" "$BINARY" --shard "$shard" &
done

wait
echo "All 71 shards completed"
