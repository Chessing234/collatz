import Collatz.Research.CoefficientDescent.Horizon
import Collatz.Research.DescentIntervals.Universal

/-! The two distinct obligations in a coefficient-based universal descent proof. -/
namespace Collatz.Research.CoefficientDescent

open FirstLightDescent

/-- Existence of a first coefficient crossing, without any bound on its time. -/
def CoefficientCoverage : Prop := ∀ n, 1 < n → ∃ k, FirstLight n k

/-- The unrestricted coefficient stopping-time descent assertion. -/
def CrossingDescent : Prop :=
  ∀ n k, 1 < n → FirstLight n k → acceleratedOrbit k n < n

/-- Crossing existence and correctness together imply universal descent and Collatz. -/
theorem collatz_of_coverage_and_crossing (hc : CoefficientCoverage) (hd : CrossingDescent) :
    CollatzConjecture := by
  apply DescentIntervals.collatz_of_coverage
  intro n hn
  obtain ⟨k, hk⟩ := hc n hn
  exact (DescentIntervals.coverage_at_iff n).mpr ⟨k, hd n k hn hk⟩

/-- Collatz would supply crossing existence, since actual descent forces coefficient contraction. -/
theorem coefficientCoverage_of_collatz (hc : CollatzConjecture) : CoefficientCoverage := by
  intro n hn
  obtain ⟨k, hk⟩ := DescentIntervals.coverage_of_collatz hc n hn
  have hs := (DescentIntervals.canonical_exact_iff n k).mpr hk
  obtain ⟨j, _, hj⟩ := exists_firstLight_of_drop hs.2.1
  exact ⟨j, hj⟩

/-- Extending the checked horizon to every finite horizon would prove crossing correctness. -/
theorem crossingDescent_of_all_horizons
    (h : ∀ K n k, 1 < n → k ≤ K → FirstLight n k → acceleratedOrbit k n < n) :
    CrossingDescent := by
  intro n k hn hf
  exact h k n k hn (Nat.le_refl k) hf

/-- Under the crossing-descent law, the remaining crossing-coverage obligation is exact. -/
theorem collatz_iff_coefficientCoverage (hd : CrossingDescent) :
    CollatzConjecture ↔ CoefficientCoverage :=
  ⟨coefficientCoverage_of_collatz, fun hc => collatz_of_coverage_and_crossing hc hd⟩

/-- A never-descending positive input greater than one has no crossing through 256. -/
theorem no_crossing_of_no_drop {n : Nat} (hn : 1 < n)
    (hnd : ∀ k, k ≤ 256 → n ≤ acceleratedOrbit k n) :
    ∀ k, k ≤ 256 → ¬ FirstLight n k := by
  intro k hk hf
  have hd := descent_at_firstLight_le_256 hn hk hf
  have := hnd k hk
  omega

end Collatz.Research.CoefficientDescent
