import Collatz.Exploration.RankGrowth

open Collatz Collatz.Exploration.RankGrowth Collatz.Exploration.RankReduction

#print axioms input_le_scaled_orbit
#print axioms input_le_scaled_accelerated
#print axioms successful_time_lower
#print axioms ranking_lower
#print axioms ranking_unbounded
#print axioms no_bounded_rank
#print axioms no_universal_hitting_horizon

-- Exact halving realizes equality in the scale lower bound.
example : orbit 10 1024 = 1 := by decide
example : 1024 = 2^10*orbit 10 1024 := by decide
example : acceleratedOrbit 10 1024 = 1 := by decide
example : 1024 = 2^10*acceleratedOrbit 10 1024 := by decide

-- Reaching 1 in fewer than ten steps is excluded without an orbit census.
example : ∀ k, k < 10 → orbit k 1024 ≠ 1 := by
  intro k hk he
  have hlow := successful_time_lower he
  have hpow : 2^k ≤ 2^9 := Nat.pow_le_pow_right (by decide) (by omega)
  have hval : (2:Nat)^9 = 512 := by decide
  omega
example : ∀ P, Ranking P → 10 ≤ P 1024 := by
  intro P hP
  have hlow := ranking_lower hP (n := 1024) (by decide)
  by_cases h : 10 ≤ P 1024
  · exact h
  · have hpow : 2^(P 1024) ≤ 2^9 := Nat.pow_le_pow_right (by decide) (by omega)
    have hval : (2:Nat)^9 = 512 := by decide
    omega
example : ¬ Ranking (fun n => n%17) := by
  apply no_bounded_rank (B := 16)
  intro n _
  have := Nat.mod_lt n (by decide : 0 < 17)
  omega
