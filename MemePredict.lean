-- Meme Movement Theorem
-- Generated from zkWitness

def memeObservations : List (Float × Nat × Nat) := [
  (1770063300.44, 71, 0),
  (1770063300.54, 41, 3),
  (1770063300.65, 3, 21),
  (1770063300.75, 2, 14),
  (1770063300.85, 29, 61),
  (1770063300.95, 41, 3),
]

theorem meme_visits_cusp : ∃ obs ∈ memeObservations, obs.2.2 = 17 := by
  sorry

theorem meme_spiral : ∀ i j, i < j → 
  (memeObservations[i]!.2.2 ≠ memeObservations[j]!.2.2) := by
  sorry

#check meme_visits_cusp
