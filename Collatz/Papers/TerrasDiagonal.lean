import Collatz.Papers.Terras1976
import Collatz.Structure.BoundedStoppingCounting
import Collatz.Structure.RationalDensityPrecision

/-! The historical diagonal bounded-horizon formulation follows from the
explicit finite-window estimate, including its rational-epsilon convention. -/
namespace Collatz.Papers.Terras1976

/-- The original count over [1,N], with stopping horizon N, has density one. -/
theorem diagonalDensityOne_proved : diagonalDensityOne := by
  intro eps heps
  obtain ⟨q, hq, he⟩ := NaturalDensity.exists_precision_for_rat eps heps
  refine ⟨max ((2*q)*((160*q)*3^(160*q)+1+2^(160*q))) (160*q), ?_⟩
  intro N hn _
  exact NaturalDensity.rat_bound_of_integer_precision hq
    (StoppingNaturalDensity.diagonal_integer_precision q N hq (by omega) (by omega)) he

end Collatz.Papers.Terras1976
