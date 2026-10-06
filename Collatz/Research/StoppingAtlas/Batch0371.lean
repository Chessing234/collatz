import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0371

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2611. -/
theorem bounds_12_2611 : exactInterval 12 2611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2611 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2611) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2611 : oddCount 2611 12 = 7 ∧ acceleratedOrbit 12 2611 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2611 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2611) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2611.1, data_12_2611.2]

/-- Complete interval computation for depth 12, residue 2612. -/
theorem bounds_12_2612 : exactInterval 12 2612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2612 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2612) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2612 : oddCount 2612 12 = 4 ∧ acceleratedOrbit 12 2612 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2612 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2612) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2612.1, data_12_2612.2]

/-- Complete interval computation for depth 12, residue 2613. -/
theorem bounds_12_2613 : exactInterval 12 2613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2613 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2613) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2613 : oddCount 2613 12 = 4 ∧ acceleratedOrbit 12 2613 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2613 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2613) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2613.1, data_12_2613.2]

/-- Complete interval computation for depth 12, residue 2614. -/
theorem bounds_12_2614 : exactInterval 12 2614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2614 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2614) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2614 : oddCount 2614 12 = 9 ∧ acceleratedOrbit 12 2614 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2614 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2614) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2614.1, data_12_2614.2]

/-- Complete interval computation for depth 12, residue 2615. -/
theorem bounds_12_2615 : exactInterval 12 2615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2615 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2615) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2615 : oddCount 2615 12 = 9 ∧ acceleratedOrbit 12 2615 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2615 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2615) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2615.1, data_12_2615.2]

/-- Complete interval computation for depth 12, residue 2616. -/
theorem bounds_12_2616 : exactInterval 12 2616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2616 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2616) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2616 : oddCount 2616 12 = 7 ∧ acceleratedOrbit 12 2616 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2616 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2616) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2616.1, data_12_2616.2]

/-- Complete interval computation for depth 12, residue 2617. -/
theorem bounds_12_2617 : exactInterval 12 2617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2617 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2617) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2617 : oddCount 2617 12 = 7 ∧ acceleratedOrbit 12 2617 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2617 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2617) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2617.1, data_12_2617.2]

/-- Complete interval computation for depth 12, residue 2618. -/
theorem bounds_12_2618 : exactInterval 12 2618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2618 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2618) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2618 : oddCount 2618 12 = 7 ∧ acceleratedOrbit 12 2618 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2618 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2618) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2618.1, data_12_2618.2]

/-- Complete interval computation for depth 12, residue 2619. -/
theorem bounds_12_2619 : exactInterval 12 2619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2619 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2619) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2619 : oddCount 2619 12 = 6 ∧ acceleratedOrbit 12 2619 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2619 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2619) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2619.1, data_12_2619.2]

/-- Complete interval computation for depth 12, residue 2620. -/
theorem bounds_12_2620 : exactInterval 12 2620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2620 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2620) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2620 : oddCount 2620 12 = 7 ∧ acceleratedOrbit 12 2620 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2620 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2620) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2620.1, data_12_2620.2]

/-- Complete interval computation for depth 12, residue 2621. -/
theorem bounds_12_2621 : exactInterval 12 2621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2621 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2621) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2621 : oddCount 2621 12 = 7 ∧ acceleratedOrbit 12 2621 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2621 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2621) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2621.1, data_12_2621.2]

/-- Complete interval computation for depth 12, residue 2622. -/
theorem bounds_12_2622 : exactInterval 12 2622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2622 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2622) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2622 : oddCount 2622 12 = 6 ∧ acceleratedOrbit 12 2622 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2622 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2622) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2622.1, data_12_2622.2]

/-- Complete interval computation for depth 12, residue 2623. -/
theorem bounds_12_2623 : exactInterval 12 2623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2623 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2623) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2623 : oddCount 2623 12 = 6 ∧ acceleratedOrbit 12 2623 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2623 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2623) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2623.1, data_12_2623.2]

/-- Complete interval computation for depth 12, residue 2624. -/
theorem bounds_12_2624 : exactInterval 12 2624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2624 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2624) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2624 : oddCount 2624 12 = 5 ∧ acceleratedOrbit 12 2624 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2624 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2624) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2624.1, data_12_2624.2]

/-- Complete interval computation for depth 12, residue 2625. -/
theorem bounds_12_2625 : exactInterval 12 2625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2625 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2625) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2625 : oddCount 2625 12 = 4 ∧ acceleratedOrbit 12 2625 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2625 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2625) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2625.1, data_12_2625.2]

end Collatz.Research.StoppingAtlas.Batch0371
