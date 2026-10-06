import Collatz.Research.PassageAtlas.SmallInputs
import Collatz.Research.StoppingAtlas.Bridge

/-! A conditional first-crossing theorem for unbounded starting integers.
The finite horizon remains a hypothesis; existence of a crossing is open. -/
namespace Collatz.Research.PassageAtlas
open FirstLightDescent FirstLightConsequences

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 4096 in
/-- Enlarging the exceptional-input range certifies the next stable gap plateau. -/
theorem gap_2592 : FirstLightGapCheck.check 2592 330588 = true := by decide

/-- Every first crossing through 2592 yields actual descent for every n>1. -/
theorem descent_at_firstLight_le_2592 {n k : Nat} (hn : 1 < n) (hk : k ≤ 2592)
    (hf : FirstLight n k) : acceleratedOrbit k n < n := by
  apply FirstLightCertificates.descent_of_certificates 2592 330588
    (FirstLightGapCheck.check_sound _ _ gap_2592) _ hn hk hf
  intro m hm
  obtain ⟨j, hj, hd⟩ := small_starts_330588 m hm
  exact ⟨⟨j.val, by have := j.isLt; omega⟩, hj, hd⟩

theorem exactThrough_2592 : ExactThrough 2592 :=
  fun _ _ hn hk hf => descent_at_firstLight_le_2592 hn hk hf

/-- Equality of coefficient stopping and actual first descent in the certified range. -/
theorem stopping_iff_firstLight_le_2592 {n k : Nat} (hn : 1 < n) (hk : k ≤ 2592) :
    stoppingTime n k ↔ FirstLight n k :=
  CoefficientDescent.stopping_iff_firstLight_of_horizon exactThrough_2592 hn hk

/-- A bounded nonempty exact-time interval would require a longer crossing. -/
theorem empty_or_tail_2592 (k r : Nat) (hk : k ≤ 2592) :
    (∀ m, ¬ (DescentIntervals.exactInterval k r).Contains m) ∨
    ((DescentIntervals.exactInterval k r).upper = none ∧
      ∀ m, stoppingTime (2 ^ k * m + r) k ↔ (DescentIntervals.exactInterval k r).lower ≤ m) :=
  StoppingAtlas.empty_or_tail exactThrough_2592 k r hk

/-- Any failure of first-crossing descent lies beyond the newly certified horizon. -/
theorem discrepancy_after_2592 {n k : Nat} (hn : 1 < n) (hf : FirstLight n k)
    (hfail : n ≤ acceleratedOrbit k n) : 2592 < k := by
  by_cases hk : k ≤ 2592
  · have := descent_at_firstLight_le_2592 hn hk hf
    omega
  · omega

set_option exponentiation.threshold 4096 in
/-- The same bound fails at the next record gap. This is not an orbit counterexample. -/
theorem next_gap_fails : ¬ ((1636 : Nat) * 3 ^ 1636 <
    3 * (2 ^ 2593 - 3 ^ 1636) * 330588) := by decide

set_option exponentiation.threshold 4096 in
/-- An enlarged range of at least 583015 would be needed by this particular bound. -/
theorem next_gap_threshold :
    ((1636 : Nat) * 3 ^ 1636) / (3 * (2 ^ 2593 - 3 ^ 1636)) + 1 = 583015 := by decide

end Collatz.Research.PassageAtlas
