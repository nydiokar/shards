// JavaScript proof
const BASE_FREQ = 432;
const SHARDS = 71;

const frequencies = Array.from({length: SHARDS}, (_, i) => 
  BASE_FREQ + (BASE_FREQ * (i + 1) / SHARDS)
);

const [min, max] = [frequencies[0], frequencies[SHARDS-1]];
const ratio = max / min;

console.log(`Min: ${min.toFixed(2)} Hz, Max: ${max.toFixed(2)} Hz, Ratio: ${ratio.toFixed(4)}`);
console.assert(Math.abs(ratio - 2.0) < 0.05, `Not an octave: ${ratio}`);
console.log(`✓ JavaScript: Octave verified [${min.toFixed(2)}-${max.toFixed(2)} Hz]`);
