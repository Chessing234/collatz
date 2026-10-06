import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0636

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2585. -/
theorem bounds_13_2585 : exactInterval 13 2585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2585 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2585) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2585 : oddCount 2585 13 = 7 ∧ acceleratedOrbit 13 2585 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2585 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2585) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2585.1, data_13_2585.2]

/-- Complete interval computation for depth 13, residue 2586. -/
theorem bounds_13_2586 : exactInterval 13 2586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2586 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2586) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2586 : oddCount 2586 13 = 6 ∧ acceleratedOrbit 13 2586 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2586 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2586) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2586.1, data_13_2586.2]

/-- Complete interval computation for depth 13, residue 2587. -/
theorem bounds_13_2587 : exactInterval 13 2587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2587 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2587) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2587 : oddCount 2587 13 = 7 ∧ acceleratedOrbit 13 2587 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2587 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2587) = 3 ^ 7 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2587.1, data_13_2587.2]

/-- Complete interval computation for depth 13, residue 2588. -/
theorem bounds_13_2588 : exactInterval 13 2588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2588 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2588) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2588 : oddCount 2588 13 = 5 ∧ acceleratedOrbit 13 2588 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2588 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2588) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2588.1, data_13_2588.2]

/-- Complete interval computation for depth 13, residue 2589. -/
theorem bounds_13_2589 : exactInterval 13 2589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2589 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2589) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2589 : oddCount 2589 13 = 5 ∧ acceleratedOrbit 13 2589 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2589 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2589) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2589.1, data_13_2589.2]

/-- Complete interval computation for depth 13, residue 2590. -/
theorem bounds_13_2590 : exactInterval 13 2590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2590 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2590) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2590 : oddCount 2590 13 = 5 ∧ acceleratedOrbit 13 2590 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2590 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2590) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2590.1, data_13_2590.2]

/-- Complete interval computation for depth 13, residue 2591. -/
theorem bounds_13_2591 : exactInterval 13 2591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2591 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2591) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2591 : oddCount 2591 13 = 7 ∧ acceleratedOrbit 13 2591 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2591 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2591) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2591.1, data_13_2591.2]

/-- Complete interval computation for depth 13, residue 2592. -/
theorem bounds_13_2592 : exactInterval 13 2592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2592 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2592) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2592 : oddCount 2592 13 = 5 ∧ acceleratedOrbit 13 2592 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2592 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2592) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2592.1, data_13_2592.2]

/-- Complete interval computation for depth 13, residue 2593. -/
theorem bounds_13_2593 : exactInterval 13 2593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2593 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2593) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2593 : oddCount 2593 13 = 5 ∧ acceleratedOrbit 13 2593 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2593 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2593) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2593.1, data_13_2593.2]

/-- Complete interval computation for depth 13, residue 2594. -/
theorem bounds_13_2594 : exactInterval 13 2594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2594 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2594) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2594 : oddCount 2594 13 = 6 ∧ acceleratedOrbit 13 2594 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2594 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2594) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2594.1, data_13_2594.2]

/-- Complete interval computation for depth 13, residue 2595. -/
theorem bounds_13_2595 : exactInterval 13 2595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2595 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2595) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2595 : oddCount 2595 13 = 6 ∧ acceleratedOrbit 13 2595 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2595 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2595) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2595.1, data_13_2595.2]

/-- Complete interval computation for depth 13, residue 2596. -/
theorem bounds_13_2596 : exactInterval 13 2596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2596 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2596) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2596 : oddCount 2596 13 = 7 ∧ acceleratedOrbit 13 2596 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2596 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2596) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2596.1, data_13_2596.2]

/-- Complete interval computation for depth 13, residue 2597. -/
theorem bounds_13_2597 : exactInterval 13 2597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2597 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2597) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2597 : oddCount 2597 13 = 7 ∧ acceleratedOrbit 13 2597 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2597 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2597) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2597.1, data_13_2597.2]

/-- Complete interval computation for depth 13, residue 2598. -/
theorem bounds_13_2598 : exactInterval 13 2598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2598 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2598) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2598 : oddCount 2598 13 = 7 ∧ acceleratedOrbit 13 2598 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2598 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2598) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2598.1, data_13_2598.2]

/-- Complete interval computation for depth 13, residue 2599. -/
theorem bounds_13_2599 : exactInterval 13 2599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2599 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2599) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2599 : oddCount 2599 13 = 7 ∧ acceleratedOrbit 13 2599 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2599 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2599) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2599.1, data_13_2599.2]

end Collatz.Research.StoppingAtlas.Batch0636
