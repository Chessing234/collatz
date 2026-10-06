import Collatz.Strategy.FirstLight1024Interface
import Collatz.Research.CoefficientDescent.Transfer

/-!
# Reusing an exceptional range up to its next arithmetic obstruction

The threshold 99730 already covers the finite witnesses checked for horizon
1024. A larger coefficient horizon needs no new input witnesses while its
uniform gap bound remains below this threshold. This file checks that fact
through 1538, and checks the failure of the same gap bound at 1539.
-/
namespace Collatz.Research.StoppingAtlas

open FirstLightDescent FirstLightConsequences

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2048 in
/-- Exact arithmetic validates the inherited exceptional-input threshold through 1538. -/
theorem gap_1538 : FirstLightGapCheck.check 1538 99730 = true := by decide

/-- Every first coefficient crossing through 1538 is a descent, for unbounded n>1. -/
theorem descent_at_firstLight_le_1538 {n k : Nat} (hn : 1 < n) (hk : k ≤ 1538)
    (hf : FirstLight n k) : acceleratedOrbit k n < n := by
  apply FirstLightCertificates.descent_of_certificates 1538 99730
    (FirstLightGapCheck.check_sound _ _ gap_1538) _ hn hk hf
  intro m hm
  obtain ⟨j, hj, hd⟩ := FirstLight1024.small_starts_99730 m hm
  exact ⟨⟨j.val, by have := j.isLt; omega⟩, hj, hd⟩

/-- Interface to the general stopping-time and periodicity developments. -/
theorem exactThrough_1538 : ExactThrough 1538 :=
  fun _ _ hn hk hf => descent_at_firstLight_le_1538 hn hk hf

/-- Both exact first-event predicates agree through the certified horizon. -/
theorem stopping_iff_firstLight_le_1538 {n k : Nat} (hn : 1 < n) (hk : k ≤ 1538) :
    stoppingTime n k ↔ FirstLight n k :=
  CoefficientDescent.stopping_iff_firstLight_of_horizon
    (fun _ _ h hK hF => descent_at_firstLight_le_1538 h hK hF) hn hk

set_option exponentiation.threshold 2048 in
/-- At the next critical pair the old arithmetic threshold fails; this is not an orbit counterexample. -/
theorem next_gap_fails : ¬ ((971 : Nat) * 3 ^ 971 <
    3 * (2 ^ 1539 - 3 ^ 971) * 99730) := by decide

set_option exponentiation.threshold 2048 in
/-- The next gap would require a threshold of at least 330588 in this bound. -/
theorem next_gap_threshold :
    ((971 : Nat) * 3 ^ 971) / (3 * (2 ^ 1539 - 3 ^ 971)) + 1 = 330588 := by decide

/-- A discrepancy beyond the inherited horizon must now occur after 1538. -/
theorem discrepancy_after_1538 {n k : Nat} (hn : 1 < n) (hf : FirstLight n k)
    (hfail : n ≤ acceleratedOrbit k n) : 1538 < k := by
  by_cases hk : k ≤ 1538
  · have := descent_at_firstLight_le_1538 hn hk hf
    omega
  · omega

end Collatz.Research.StoppingAtlas
