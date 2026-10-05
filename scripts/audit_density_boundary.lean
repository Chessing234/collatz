import Collatz.Exploration.DensityBoundary

open Collatz.Exploration.DensityBoundary

#print axioms density_one_of_bounded_bad
#print axioms badCount_le_of_imp
#print axioms density_one_of_imp
#print axioms badCount_omit
#print axioms omit_density_one
#print axioms density_one_not_universal
#print axioms no_density_to_universal

example : badCount (exceptOne 2) 0 = 0 := by decide
example : badCount (exceptOne 2) 1 = 0 := by decide
example : badCount (exceptOne 2) 2 = 1 := by decide
example : badCount (exceptOne 2) 100 = 1 := by decide
example : badCount (exceptOne 0) 100 = 0 := by decide
example : badCount (exceptOne 1000) 100 = 0 := by decide
example : DensityOne (exceptOne 1000000) := omit_density_one 1000000
example : ¬ (∀ n, 0 < n → exceptOne 1000000 n = true) :=
  omit_not_universal (by decide)

-- Every reciprocal epsilon scale has an explicit bound for the singleton.
example : ∀ d x, d ≤ x → d*badCount (exceptOne 2) x ≤ x := by
  intro d x hx
  rw [badCount_omit]
  split <;> simp_all
