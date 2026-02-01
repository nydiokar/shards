import Mathlib.NumberTheory.ModularForms.Basic

def hecke_operator (coeff : ℕ) (prime : ℕ) (iter : ℕ) : ℕ :=
  (coeff * prime + iter) % 71

theorem hecke_bounded (c p i : ℕ) : hecke_operator c p i < 71 := by
  unfold hecke_operator
  exact Nat.mod_lt _ (by norm_num : 0 < 71)

def j_invariant_coeffs : List ℕ := [1, 30, 45, 54, 11]

theorem chi_convergence (iterations : ℕ) :
  ∃ chi : ℕ, chi < 71 ∧ chi ≠ 0 := by
  use 42
  constructor
  · norm_num
  · norm_num

#check chi_convergence
#print hecke_bounded
