import Collatz.Research.PassageAtlas.Horizon
import Collatz.Research.CoefficientDescent.Universal
import Collatz.Structure.Minimal

/-! The investigation is directed at universal descent. This file isolates
precisely the remaining quantifier after the certified window, and supplies
an unbounded arithmetic sufficient condition. None of the open conditions
is introduced as an axiom or asserted to hold. -/
namespace Collatz.Research.PassageAtlas
open FirstLightDescent

/-- The residual target permits input-dependent, arbitrarily late witnesses. -/
def ResidualCoverage : Prop := ∀ n : Nat, 1 < n →
  (∀ k : Nat, k ≤ 2592 → ¬ FirstLight n k) →
  ∃ k : Nat, 2592 < k ∧ acceleratedOrbit k n < n

/-- The unresolved residual coverage is exactly equivalent to Collatz. -/
theorem residualCoverage_iff_collatz : ResidualCoverage ↔ CollatzConjecture := by
  constructor
  · intro hr
    apply DescentIntervals.collatz_of_coverage
    intro n hn
    by_cases he : ∃ k, k ≤ 2592 ∧ FirstLight n k
    · obtain ⟨k, hk, hf⟩ := he
      exact (DescentIntervals.coverage_at_iff n).mpr
        ⟨k, descent_at_firstLight_le_2592 hn hk hf⟩
    · have hno : ∀ k, k ≤ 2592 → ¬ FirstLight n k := by
        intro k hk hf
        exact he ⟨k, hk, hf⟩
      obtain ⟨k, _, hd⟩ := hr n hn hno
      exact (DescentIntervals.coverage_at_iff n).mpr ⟨k, hd⟩
  · intro hc n hn hno
    obtain ⟨k, hk⟩ := DescentIntervals.coverage_of_collatz hc n hn
    have hs := (DescentIntervals.canonical_exact_iff n k).mpr hk
    refine ⟨k, ?_, hs.2.1⟩
    by_cases hle : k ≤ 2592
    · exact False.elim (hno k hle ((stopping_iff_firstLight_le_2592 hn hle).mp hs))
    · omega

/-- A sufficient residual target expressed using just odd counts and integer gaps. -/
def ResidualGapCoverage : Prop := ∀ n : Nat, 1 < n →
  (∀ k : Nat, k ≤ 2592 → ¬ FirstLight n k) →
  ∃ k : Nat, FirstLight n k ∧
    oddCount n k * 3 ^ oddCount n k < 3 * (2 ^ k - 3 ^ oddCount n k) * n

/-- The explicit gap estimate forces descent without a fixed crossing-time bound. -/
theorem residualCoverage_of_gap (h : ResidualGapCoverage) : ResidualCoverage := by
  intro n hn hno
  obtain ⟨k, hf, hgap⟩ := h n hn hno
  have hlate : 2592 < k := by
    by_cases hk : k ≤ 2592
    · exact False.elim (hno k hk hf)
    · omega
  refine ⟨k, hlate, ?_⟩
  by_cases hd : acceleratedOrbit k n < n
  · exact hd
  · have hb := failure_bound hf (by omega)
    omega

/-- A proof of the residual arithmetic condition would solve the original conjecture. -/
theorem collatz_of_residual_gap (h : ResidualGapCoverage) : CollatzConjecture :=
  residualCoverage_iff_collatz.mp (residualCoverage_of_gap h)

/-- If Collatz fails, a concrete never-descending input survives the certified window. -/
theorem residual_failure_witness (h : ¬ CollatzConjecture) :
    ∃ n : Nat, 1 < n ∧
      (∀ k : Nat, k ≤ 2592 → ¬ FirstLight n k) ∧
      (∀ k : Nat, n ≤ acceleratedOrbit k n) := by
  obtain ⟨n, hm⟩ := Minimal.exists_minimalCounterexample h
  have hn := Minimal.gt_one_of_minimal hm
  refine ⟨n, hn, ?_, ?_⟩
  · intro k hk hf
    exact Minimal.not_accOrbit_lt_of_minimal hm k
      (descent_at_firstLight_le_2592 hn hk hf)
  · intro k
    have := Minimal.not_accOrbit_lt_of_minimal hm k
    omega

/-- No finite window alone can supply all the required witnesses, even if enlarged. -/
theorem finite_crossing_window_incomplete (K : Nat) (hK : FirstLightConsequences.ExactThrough K) :
    ∃ n : Nat, 1 < n ∧ ∀ k : Nat, k ≤ K → ¬ FirstLight n k := by
  obtain ⟨n, hn, hmiss⟩ := DescentIntervals.finite_depth_incomplete K
  refine ⟨n, hn, ?_⟩
  intro k hk hf
  have hs := (CoefficientDescent.stopping_iff_firstLight_of_horizon hK hn hk).mpr hf
  exact hmiss k hk ((DescentIntervals.canonical_exact_iff n k).mp hs)

/-- Certified progress must be combined with an unbounded argument, not a fixed deadline. -/
theorem crossing_window_2592_incomplete :
    ∃ n : Nat, 1 < n ∧ ∀ k : Nat, k ≤ 2592 → ¬ FirstLight n k :=
  finite_crossing_window_incomplete 2592 exactThrough_2592

end Collatz.Research.PassageAtlas
