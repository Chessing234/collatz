import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0638

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2616. -/
theorem bounds_13_2616 : exactInterval 13 2616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2616 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2616) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2616 : oddCount 2616 13 = 8 ∧ acceleratedOrbit 13 2616 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2616 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2616) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2616.1, data_13_2616.2]

/-- Complete interval computation for depth 13, residue 2617. -/
theorem bounds_13_2617 : exactInterval 13 2617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2617 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2617) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2617 : oddCount 2617 13 = 8 ∧ acceleratedOrbit 13 2617 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2617 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2617) = 3 ^ 8 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2617.1, data_13_2617.2]

/-- Complete interval computation for depth 13, residue 2618. -/
theorem bounds_13_2618 : exactInterval 13 2618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2618 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2618) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2618 : oddCount 2618 13 = 8 ∧ acceleratedOrbit 13 2618 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2618 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2618) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2618.1, data_13_2618.2]

/-- Complete interval computation for depth 13, residue 2619. -/
theorem bounds_13_2619 : exactInterval 13 2619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2619 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2619) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2619 : oddCount 2619 13 = 7 ∧ acceleratedOrbit 13 2619 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2619 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2619) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2619.1, data_13_2619.2]

/-- Complete interval computation for depth 13, residue 2620. -/
theorem bounds_13_2620 : exactInterval 13 2620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2620 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2620) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2620 : oddCount 2620 13 = 8 ∧ acceleratedOrbit 13 2620 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2620 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2620) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2620.1, data_13_2620.2]

/-- Complete interval computation for depth 13, residue 2621. -/
theorem bounds_13_2621 : exactInterval 13 2621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2621 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2621) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2621 : oddCount 2621 13 = 8 ∧ acceleratedOrbit 13 2621 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2621 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2621) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2621.1, data_13_2621.2]

/-- Complete interval computation for depth 13, residue 2622. -/
theorem bounds_13_2622 : exactInterval 13 2622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2622 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2622) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2622 : oddCount 2622 13 = 7 ∧ acceleratedOrbit 13 2622 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2622 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2622) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2622.1, data_13_2622.2]

/-- Complete interval computation for depth 13, residue 2623. -/
theorem bounds_13_2623 : exactInterval 13 2623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2623 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2623) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2623 : oddCount 2623 13 = 7 ∧ acceleratedOrbit 13 2623 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2623 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2623) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2623.1, data_13_2623.2]

/-- Complete interval computation for depth 13, residue 2624. -/
theorem bounds_13_2624 : exactInterval 13 2624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2624 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2624) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2624 : oddCount 2624 13 = 6 ∧ acceleratedOrbit 13 2624 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2624 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2624) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2624.1, data_13_2624.2]

/-- Complete interval computation for depth 13, residue 2625. -/
theorem bounds_13_2625 : exactInterval 13 2625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2625 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2625) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2625 : oddCount 2625 13 = 4 ∧ acceleratedOrbit 13 2625 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2625 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2625) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2625.1, data_13_2625.2]

/-- Complete interval computation for depth 13, residue 2626. -/
theorem bounds_13_2626 : exactInterval 13 2626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2626 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2626) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2626 : oddCount 2626 13 = 4 ∧ acceleratedOrbit 13 2626 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2626 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2626) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2626.1, data_13_2626.2]

/-- Complete interval computation for depth 13, residue 2627. -/
theorem bounds_13_2627 : exactInterval 13 2627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2627 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2627) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2627 : oddCount 2627 13 = 4 ∧ acceleratedOrbit 13 2627 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2627 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2627) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2627.1, data_13_2627.2]

/-- Complete interval computation for depth 13, residue 2628. -/
theorem bounds_13_2628 : exactInterval 13 2628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2628 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2628) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2628 : oddCount 2628 13 = 6 ∧ acceleratedOrbit 13 2628 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2628 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2628) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2628.1, data_13_2628.2]

/-- Complete interval computation for depth 13, residue 2629. -/
theorem bounds_13_2629 : exactInterval 13 2629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2629 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2629) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2629 : oddCount 2629 13 = 6 ∧ acceleratedOrbit 13 2629 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2629 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2629) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2629.1, data_13_2629.2]

/-- Complete interval computation for depth 13, residue 2630. -/
theorem bounds_13_2630 : exactInterval 13 2630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2630 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2630) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2630 : oddCount 2630 13 = 6 ∧ acceleratedOrbit 13 2630 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2630 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2630) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2630.1, data_13_2630.2]

end Collatz.Research.StoppingAtlas.Batch0638
