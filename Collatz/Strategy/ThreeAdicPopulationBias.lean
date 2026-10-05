import Collatz.Strategy.ThreeAdicPopulationClosed

/-!
# Exact errors relative to uniform and limiting residue laws

The finite-time law approaches masses (0,1/3,2/3), rather than (1/3,1/3,1/3).
All statements use integer counts. No theorem about real-valued limits or
first-descent sampling is inferred from them.
-/

namespace Collatz.ThreeAdicPopulation

/-- The residue-one mass has at most three units of cross-multiplied error. -/
theorem one_limiting_mass_error (k : Nat) :
    3 * population k 1 ≤ period k ∧ period k ≤ 3 * population k 1 + 3 := by
  obtain ⟨hlo, hhi⟩ := population_one_bounds k
  unfold period
  omega

/-- The residue-two mass has at most three units of cross-multiplied error. -/
theorem two_limiting_mass_error (k : Nat) :
    3 * population k 2 ≤ 2 * period k ∧ 2 * period k ≤ 3 * population k 2 + 3 := by
  obtain ⟨hlo, hhi⟩ := population_two_bounds k
  rw [Nat.pow_succ] at hlo hhi
  unfold period
  omega

/-- The exact discrepancy in residue zero relative to uniform input masses. -/
theorem zero_uniform_deficit (k : Nat) :
    population k 0 + (2 ^ k - 1) = 2 ^ k := by
  rw [population_zero]
  have hp : 0 < (2 : Nat) ^ k := Nat.pow_pos (by decide)
  omega

/-- No uniform residue law is retained at a positive depth. -/
theorem population_not_uniform {k : Nat} (hk : 0 < k) :
    ¬ (population k 0 = population k 1 ∧ population k 1 = population k 2) := by
  intro heq
  have hz := population_zero k
  have ht := population_total k
  have hp : 2 ≤ (2 : Nat) ^ k := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hk
    simpa using h
  unfold period at ht
  omega

/-- At every positive depth, residue two has strictly more inputs than residue one. -/
theorem two_population_strictly_larger {k : Nat} (hk : 0 < k) :
    population k 1 < population k 2 := by
  have hp : 2 ≤ (2 : Nat) ^ k := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hk
    simpa using h
  obtain ⟨h1lo, h1hi⟩ := population_one_bounds k
  obtain ⟨h2lo, h2hi⟩ := population_two_bounds k
  rw [Nat.pow_succ] at h2hi
  omega

/-- One input of count error is the best depth-uniform bound for residue one. -/
theorem one_error_attained_at_odd (j : Nat) :
    population (2 * j + 1) 1 + 1 = 2 ^ (2 * j + 1) := (population_odd j).1

/-- One input of count error is the best depth-uniform bound for residue two. -/
theorem two_error_attained_at_even (j : Nat) :
    population (2 * j) 2 + 1 = 2 ^ (2 * j + 1) := (population_even j).2

/-- At even depths the nonzero populations satisfy an exact affine bias relation. -/
theorem even_bias_exact (j : Nat) :
    population (2 * j) 2 + 1 = 2 * population (2 * j) 1 := by
  obtain ⟨h1, h2⟩ := population_even j
  rw [Nat.pow_succ] at h2
  omega

/-- At odd depths the nonzero populations satisfy the complementary bias relation. -/
theorem odd_bias_exact (j : Nat) :
    population (2 * j + 1) 2 = 2 * population (2 * j + 1) 1 + 2 := by
  obtain ⟨h1, h2⟩ := population_odd j
  rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, Nat.pow_succ] at h2
  omega

end Collatz.ThreeAdicPopulation
