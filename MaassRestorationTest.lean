-- Test Maass Restoration
import MaassRestoration

-- Test on our own files
#maass_restore "SimpleExprMonster.lean"
#maass_restore "MetaCoqMonsterProof.lean"
#maass_restore "TowerExpansion.lean"

-- Expected output:
-- Maass Restoration Analysis:
--   File: <path>
--   Eigenvalue λ: <value>
--   Optimal shard: <N>
--   Shadow σ: <value>
--   Repair cost: <value>
--   ∴ Optimal repair to shard N ✓
