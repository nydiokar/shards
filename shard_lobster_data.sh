#!/usr/bin/env bash
# shard_lobster_data.sh - Distribute Shard 69 data across all 71 shards

set -euo pipefail

echo "🦞 Sharding Lobster Market Data Across 71 Shards..."
echo "=================================================="

# Source data from Shard 69
SOURCE_SHARD=69
TOTAL_SHARDS=71

# Data to shard
VESSELS=1247
PORTS=247
MARKET_VALUE=2450000000
EQUIPMENT_ITEMS=5000

# Calculate distribution
VESSELS_PER_SHARD=$((VESSELS / TOTAL_SHARDS))
PORTS_PER_SHARD=$((PORTS / TOTAL_SHARDS))
VALUE_PER_SHARD=$((MARKET_VALUE / TOTAL_SHARDS))
EQUIPMENT_PER_SHARD=$((EQUIPMENT_ITEMS / TOTAL_SHARDS))

echo "Distribution per shard:"
echo "  Vessels: $VESSELS_PER_SHARD"
echo "  Ports: $PORTS_PER_SHARD"
echo "  Market Value: \$$VALUE_PER_SHARD"
echo "  Equipment: $EQUIPMENT_PER_SHARD"
echo ""

# Shard the data
for SHARD in {0..70}; do
  SHARD_DIR="shard$SHARD/lobster_data"
  mkdir -p "$SHARD_DIR"
  
  # Calculate shard-specific data (mod 71 distribution)
  START_VESSEL=$((SHARD * VESSELS_PER_SHARD))
  END_VESSEL=$(((SHARD + 1) * VESSELS_PER_SHARD))
  
  # Create shard manifest
  cat > "$SHARD_DIR/manifest.json" <<EOF
{
  "shard": $SHARD,
  "source_shard": $SOURCE_SHARD,
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "data": {
    "vessels": {
      "start_id": $START_VESSEL,
      "end_id": $END_VESSEL,
      "count": $VESSELS_PER_SHARD
    },
    "ports": {
      "count": $PORTS_PER_SHARD
    },
    "market_value": $VALUE_PER_SHARD,
    "equipment_items": $EQUIPMENT_PER_SHARD
  },
  "hash": "$(echo -n "shard${SHARD}_lobster" | sha256sum | cut -d' ' -f1)"
}
EOF

  # Create vessel data
  cat > "$SHARD_DIR/vessels.json" <<EOF
{
  "shard": $SHARD,
  "vessels": [
$(for i in $(seq $START_VESSEL $((END_VESSEL - 1))); do
    LAT=$(echo "scale=6; 40 + ($i % 20)" | bc)
    LON=$(echo "scale=6; -70 + ($i % 30)" | bc)
    echo "    {\"id\": $i, \"lat\": $LAT, \"lon\": $LON, \"type\": \"lobster_boat\"}"
    [ $i -lt $((END_VESSEL - 1)) ] && echo ","
  done)
  ]
}
EOF

  # Create DHT entry for distributed lookup
  cat > "$SHARD_DIR/dht_entry.json" <<EOF
{
  "key": "lobster_shard_$SHARD",
  "value": {
    "shard": $SHARD,
    "vessels": $VESSELS_PER_SHARD,
    "hash": "$(echo -n "shard${SHARD}" | sha256sum | cut -d' ' -f1)"
  }
}
EOF

  echo "[$((SHARD + 1))/$TOTAL_SHARDS] Shard $SHARD: $VESSELS_PER_SHARD vessels"
done

# Create global index
cat > "lobster_global_index.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "source_shard": $SOURCE_SHARD,
  "total_shards": $TOTAL_SHARDS,
  "distribution": {
    "total_vessels": $VESSELS,
    "total_ports": $PORTS,
    "total_market_value": $MARKET_VALUE,
    "total_equipment": $EQUIPMENT_ITEMS,
    "per_shard": {
      "vessels": $VESSELS_PER_SHARD,
      "ports": $PORTS_PER_SHARD,
      "market_value": $VALUE_PER_SHARD,
      "equipment": $EQUIPMENT_PER_SHARD
    }
  },
  "shards": [
$(for s in {0..70}; do
    echo "    {\"shard\": $s, \"hash\": \"$(echo -n "shard${s}" | sha256sum | cut -d' ' -f1)\"}"
    [ $s -lt 70 ] && echo ","
  done)
  ]
}
EOF

echo ""
echo "=================================================="
echo "✨ Lobster data sharded across all 71 shards!"
echo ""
echo "Global Index: lobster_global_index.json"
echo "Shard Data: shard*/lobster_data/"
echo ""
echo "Query any shard for distributed lobster data!"
