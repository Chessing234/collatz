import Collatz.Exploration.AdaptiveResidueObstruction

open Collatz Collatz.Exploration.AdaptiveResidueObstruction

#print axioms prefix_endpoint
#print axioms prefix_non_decreasing_from_start
#print axioms prefix_same_residue
#print axioms potential_prefix
#print axioms no_bounded_adaptive_potential
#print axioms no_bounded_adaptive_affine
#print axioms no_bounded_size_descent

-- Horizon zero still uses a nontrivial witness, avoiding a vacuous edge case.
example : 1 < 2^(0+2)*1-1 := by decide
example : acceleratedOrbit 0 (2^2-1) = 3 := by decide
example : ∀ j, j ≤ 10 →
    (2^12*5-1)%5 = acceleratedOrbit j (2^12*5-1)%5 := by
  intro j hj
  exact prefix_same_residue 10 5 j (by decide) hj
example : ∀ j, j ≤ 10 → 2^12*5-1 ≤ acceleratedOrbit j (2^12*5-1) := by
  intro j hj
  exact prefix_non_decreasing_from_start 10 5 j (by decide) hj
example : acceleratedOrbit 10 (2^12*5-1) = 3^10*2^2*5-1 := by decide
example : ¬ (∀ n, 1 < n → ∃ j, j ≤ 100 ∧ acceleratedOrbit j n < n) :=
  no_bounded_size_descent 100
example : ¬ (∀ n, 1 < n → ∃ j, j ≤ 20 ∧
    3*acceleratedOrbit j n+acceleratedOrbit j n%7 < 3*n+n%7) := by
  apply no_bounded_adaptive_potential 20 7 (by decide) (P := fun n => 3*n+n%7)
  intro x y hr hxy
  dsimp only
  rw [hr]
  omega
