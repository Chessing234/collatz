import CollatzTargetDensity.ResiduePublic

#print CollatzTargetDensity.residueCountBelow
#check CollatzTargetDensity.positive_density_in_progression_iff
#check CollatzTargetDensity.collatz_iff_sparse_bad_in_one_mixed_class
#print axioms CollatzTargetDensity.positive_density_of_count_transport
#print axioms CollatzTargetDensity.positive_density_tail
#print axioms CollatzTargetDensity.sibling_syracuse
#print axioms CollatzTargetDensity.sibling_residue
#print axioms CollatzTargetDensity.ternary_count_transport
#print axioms CollatzTargetDensity.positive_density_odd_in_every_ternary_class
#print axioms CollatzTargetDensity.positive_density_ternary_class_iff
#print axioms CollatzTargetDensity.positive_density_every_mixed_class
#print axioms CollatzTargetDensity.positive_density_mixed_class_iff
#print axioms CollatzTargetDensity.positive_density_in_progression_iff
#print axioms CollatzTargetDensity.counterexamples_positive_density_every_mixed_class
#print axioms CollatzTargetDensity.collatz_iff_sparse_bad_in_one_mixed_class

-- A concrete instance: positive density in each of the 72 classes for target 1.
example (r : ℕ) (hr : r < 72) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (CollatzTargetDensity.residueCountBelow 1 72 r X : ℝ) := by
  exact (CollatzTargetDensity.positive_density_in_progression_iff 1 3 2 r
    (by decide) hr).2 (by decide)

-- The exclusion of targets divisible by 3 persists even in the zero class.
example : ¬∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    c * (X : ℝ) ≤ (CollatzTargetDensity.residueCountBelow 3 72 0 X : ℝ) := by
  intro h
  exact ((CollatzTargetDensity.positive_density_in_progression_iff 3 3 2 0
    (by decide) (by decide)).1 h) (by decide)
