import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0369

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2580. -/
theorem bounds_12_2580 : exactInterval 12 2580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2580 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2580) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2580 : oddCount 2580 12 = 5 ∧ acceleratedOrbit 12 2580 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2580 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2580) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2580.1, data_12_2580.2]

/-- Complete interval computation for depth 12, residue 2581. -/
theorem bounds_12_2581 : exactInterval 12 2581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2581 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2581) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2581 : oddCount 2581 12 = 5 ∧ acceleratedOrbit 12 2581 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2581 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2581) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2581.1, data_12_2581.2]

/-- Complete interval computation for depth 12, residue 2582. -/
theorem bounds_12_2582 : exactInterval 12 2582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2582 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2582) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2582 : oddCount 2582 12 = 6 ∧ acceleratedOrbit 12 2582 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2582 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2582) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2582.1, data_12_2582.2]

/-- Complete interval computation for depth 12, residue 2583. -/
theorem bounds_12_2583 : exactInterval 12 2583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2583 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2583) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2583 : oddCount 2583 12 = 6 ∧ acceleratedOrbit 12 2583 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2583 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2583) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2583.1, data_12_2583.2]

/-- Complete interval computation for depth 12, residue 2584. -/
theorem bounds_12_2584 : exactInterval 12 2584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2584 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2584) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2584 : oddCount 2584 12 = 5 ∧ acceleratedOrbit 12 2584 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2584 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2584) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2584.1, data_12_2584.2]

/-- Complete interval computation for depth 12, residue 2585. -/
theorem bounds_12_2585 : exactInterval 12 2585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2585 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2585) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2585 : oddCount 2585 12 = 6 ∧ acceleratedOrbit 12 2585 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2585 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2585) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2585.1, data_12_2585.2]

/-- Complete interval computation for depth 12, residue 2586. -/
theorem bounds_12_2586 : exactInterval 12 2586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2586 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2586) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2586 : oddCount 2586 12 = 5 ∧ acceleratedOrbit 12 2586 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2586 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2586) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2586.1, data_12_2586.2]

/-- Complete interval computation for depth 12, residue 2587. -/
theorem bounds_12_2587 : exactInterval 12 2587 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2587 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2587) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2587 : oddCount 2587 12 = 7 ∧ acceleratedOrbit 12 2587 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2587 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2587) = 3 ^ 7 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2587.1, data_12_2587.2]

/-- Complete interval computation for depth 12, residue 2588. -/
theorem bounds_12_2588 : exactInterval 12 2588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2588 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2588) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2588 : oddCount 2588 12 = 5 ∧ acceleratedOrbit 12 2588 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2588 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2588) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2588.1, data_12_2588.2]

/-- Complete interval computation for depth 12, residue 2589. -/
theorem bounds_12_2589 : exactInterval 12 2589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2589 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2589) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2589 : oddCount 2589 12 = 5 ∧ acceleratedOrbit 12 2589 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2589 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2589) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2589.1, data_12_2589.2]

/-- Complete interval computation for depth 12, residue 2590. -/
theorem bounds_12_2590 : exactInterval 12 2590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2590 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2590) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2590 : oddCount 2590 12 = 5 ∧ acceleratedOrbit 12 2590 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2590 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2590) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2590.1, data_12_2590.2]

/-- Complete interval computation for depth 12, residue 2591. -/
theorem bounds_12_2591 : exactInterval 12 2591 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2591 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2591) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2591 : oddCount 2591 12 = 7 ∧ acceleratedOrbit 12 2591 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2591 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2591) = 3 ^ 7 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2591.1, data_12_2591.2]

/-- Complete interval computation for depth 12, residue 2592. -/
theorem bounds_12_2592 : exactInterval 12 2592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2592 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2592) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2592 : oddCount 2592 12 = 4 ∧ acceleratedOrbit 12 2592 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2592 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2592) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2592.1, data_12_2592.2]

/-- Complete interval computation for depth 12, residue 2593. -/
theorem bounds_12_2593 : exactInterval 12 2593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2593 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2593) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2593 : oddCount 2593 12 = 5 ∧ acceleratedOrbit 12 2593 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2593 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2593) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2593.1, data_12_2593.2]

/-- Complete interval computation for depth 12, residue 2594. -/
theorem bounds_12_2594 : exactInterval 12 2594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2594 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2594) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2594 : oddCount 2594 12 = 5 ∧ acceleratedOrbit 12 2594 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2594 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2594) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2594.1, data_12_2594.2]

end Collatz.Research.StoppingAtlas.Batch0369
