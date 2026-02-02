-- Example: Using the Lean4 Introspector
import Lean4Introspector

-- Test with simple expressions
#introspect fun x => x

#introspect fun (x : Nat) => x + 1

#introspect ∀ (n : Nat), n + 0 = n

-- This will output:
-- SimpleExpr elements: X
-- Tower height: Y (sum of Monster primes)
-- Shard (mod 71): Z
