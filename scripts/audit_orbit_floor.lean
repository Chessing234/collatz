import Collatz.Exploration.OrbitFloor

open Collatz Collatz.Exploration.OrbitFloor

#print axioms attained_minimum
#print axioms floor_of_failure
#print axioms no_floor_iff_collatz
#print axioms traps_empty_iff_collatz
#print axioms floor_mod_four

-- Concrete checks exercise the standard-map convention, rather than the
-- accelerated convention used by many of the existing modules.
example : orbit 3 5 = 4 := by decide
example : orbit 3 9 = 7 := by decide
example : orbit 3 13 = 10 := by decide
example : ¬ Floor 1 := by intro h; have := h.1; omega
example : ¬ Floor 2 := by
  intro h
  have := floor_odd h
  omega
example : ¬ Floor 5 := by
  intro h
  have := floor_mod_four h
  omega
example : ∀ q, 0 < q → ¬ Floor (4*q+1) := by
  intro q hq hf
  have hm := hf.2 3
  rw [residue_one_descent q hq] at hm
  omega
