import Collatz.Exploration.FirstDescent

open Collatz Collatz.Exploration.TimeChange Collatz.Exploration.FirstDescent

set_option maxRecDepth 4000

#print axioms first_standard_iff
#print axioms first_not_omitted
#print axioms first_time_bounds
#print axioms standard_unique
#print axioms accelerated_unique
#print axioms first_exists_iff

-- All first-drop claims check every preceding value, not only the endpoint.
example : FirstAccelerated 3 4 := by
  constructor
  · decide
  · intro i hi
    have h : ∀ t : Fin 4, 3 ≤ acceleratedOrbit t.val 3 := by decide
    exact h ⟨i, hi⟩
example : FirstStandard 3 6 := by
  have h : FirstAccelerated 3 4 := by
    constructor
    · decide
    · intro i hi
      have h : ∀ t : Fin 4, 3 ≤ acceleratedOrbit t.val 3 := by decide
      exact h ⟨i, hi⟩
  exact standard_first_of_accelerated h

example : FirstAccelerated 27 59 := by
  constructor
  · decide
  · intro i hi
    have h : ∀ t : Fin 59, 27 ≤ acceleratedOrbit t.val 27 := by decide
    exact h ⟨i, hi⟩

example : clock 27 59 = 96 := by decide
example : acceleratedOrbit 59 27 = 23 := by decide
example : orbit 96 27 = 23 := by decide
example : ¬ FirstStandard 3 7 := by
  intro h
  have hm := h.2 6 (by decide)
  have hv : orbit 6 3 = 2 := by decide
  omega
