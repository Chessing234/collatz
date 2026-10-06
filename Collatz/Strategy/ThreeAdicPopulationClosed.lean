import Collatz.Strategy.ThreeAdicPopulation

/-!
# Closed forms for the finite-time residue populations

The residue-zero count is one. The residue-one count is `2^k` for even k and
`2^k-1` for odd k. The residue-two count is `2^(k+1)-1` for even k and
`2^(k+1)` for odd k. Addition-first statements avoid truncated subtraction.
-/

namespace Collatz.ThreeAdicPopulation

/-- Exactly one initial value in the complete input period lands in residue zero. -/
theorem population_zero (k : Nat) : population k 0 = 1 := by
  induction k with
  | zero => exact population_initial 0 (by decide)
  | succ k ih => rw [population_zero_succ, ih]

/-- The two-step update on residue one adds the earlier input period. -/
theorem population_one_two_steps (k : Nat) :
    population (k + 2) 1 = period k + population k 1 := by
  rw [show k + 2 = (k + 1) + 1 by omega, population_one_succ, population_two_succ]

/-- The two-step update on residue two adds the intervening input period. -/
theorem population_two_two_steps (k : Nat) :
    population (k + 2) 2 = period (k + 1) + population k 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, population_two_succ, population_one_succ]

/-- Closed population formulas at every even depth. -/
theorem population_even (j : Nat) :
    population (2 * j) 1 = 2 ^ (2 * j) ∧
    population (2 * j) 2 + 1 = 2 ^ (2 * j + 1) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hi : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [hi, population_one_two_steps, population_two_two_steps]
    have hp1 : 2 ^ (2 * j + 2) = 4 * 2 ^ (2 * j) := by
      rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
      omega
    have hp2 : 2 ^ (2 * j + 2 + 1) = 4 * 2 ^ (2 * j + 1) := by
      rw [show 2 * j + 2 + 1 = ((2 * j + 1) + 1) + 1 by omega,
        Nat.pow_succ, Nat.pow_succ]
      omega
    rw [hp1, hp2]
    unfold period
    constructor <;> omega

/-- Closed population formulas at every odd depth. -/
theorem population_odd (j : Nat) :
    population (2 * j + 1) 1 + 1 = 2 ^ (2 * j + 1) ∧
    population (2 * j + 1) 2 = 2 ^ (2 * j + 2) := by
  obtain ⟨h1, h2⟩ := population_even j
  rw [population_one_succ, population_two_succ]
  constructor
  · exact h2
  · unfold period
    rw [h1, show 2 * j + 2 = (2 * j + 1) + 1 by omega,
      Nat.pow_succ, Nat.pow_succ]
    omega

/-- Each natural depth is either twice a natural number or its successor. -/
theorem depth_even_or_odd (k : Nat) :
    (∃ j : Nat, k = 2 * j) ∨ (∃ j : Nat, k = 2 * j + 1) := by
  have h := Nat.div_add_mod k 2
  by_cases he : k % 2 = 0
  · exact Or.inl ⟨k / 2, by omega⟩
  · exact Or.inr ⟨k / 2, by omega⟩

/-- The residue-one count differs from `2^k` by at most one input. -/
theorem population_one_bounds (k : Nat) :
    population k 1 ≤ 2 ^ k ∧ 2 ^ k ≤ population k 1 + 1 := by
  rcases depth_even_or_odd k with ⟨j, h⟩ | ⟨j, h⟩ <;> subst k
  · have hp := (population_even j).1
    omega
  · have hp := (population_odd j).1
    omega

/-- The residue-two count differs from `2^(k+1)` by at most one input. -/
theorem population_two_bounds (k : Nat) :
    population k 2 ≤ 2 ^ (k + 1) ∧ 2 ^ (k + 1) ≤ population k 2 + 1 := by
  rcases depth_even_or_odd k with ⟨j, h⟩ | ⟨j, h⟩ <;> subst k
  · have hp := (population_even j).2
    omega
  · have hp := (population_odd j).2
    have hi : 2 * j + 1 + 1 = 2 * j + 2 := by omega
    rw [hi]
    omega

/-- Conservation of input multiplicity in the complete-period population. -/
theorem population_total (k : Nat) :
    population k 0 + population k 1 + population k 2 = period k := by
  rw [population_zero]
  rcases depth_even_or_odd k with ⟨j, h⟩ | ⟨j, h⟩ <;> subst k
  · obtain ⟨h1, h2⟩ := population_even j
    unfold period
    rw [Nat.pow_succ] at h2
    omega
  · obtain ⟨h1, h2⟩ := population_odd j
    unfold period
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, Nat.pow_succ] at h2
    omega

/-- The limiting two-to-one bias has a uniformly bounded finite-depth error. -/
theorem population_bias_error (k : Nat) :
    population k 2 ≤ 2 * population k 1 + 2 ∧
    2 * population k 1 ≤ population k 2 + 1 := by
  obtain ⟨h1lo, h1hi⟩ := population_one_bounds k
  obtain ⟨h2lo, h2hi⟩ := population_two_bounds k
  rw [Nat.pow_succ] at h2lo h2hi
  omega

/-- The image population is already nonuniform at depth one. -/
theorem population_depth_one :
    population 1 0 = 1 ∧ population 1 1 = 1 ∧ population 1 2 = 4 := by decide

set_option maxRecDepth 4000 in
/-- A larger checked case that exercises the full orbit-based definition. -/
theorem population_depth_six :
    population 6 0 = 1 ∧ population 6 1 = 64 ∧ population 6 2 = 127 := by decide

end Collatz.ThreeAdicPopulation
