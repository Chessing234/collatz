import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0633

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2539. -/
theorem bounds_13_2539 : exactInterval 13 2539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2539 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2539) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2539 : oddCount 2539 13 = 8 ∧ acceleratedOrbit 13 2539 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2539 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2539) = 3 ^ 8 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2539.1, data_13_2539.2]

/-- Complete interval computation for depth 13, residue 2540. -/
theorem bounds_13_2540 : exactInterval 13 2540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2540 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2540) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2540 : oddCount 2540 13 = 6 ∧ acceleratedOrbit 13 2540 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2540 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2540) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2540.1, data_13_2540.2]

/-- Complete interval computation for depth 13, residue 2541. -/
theorem bounds_13_2541 : exactInterval 13 2541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2541 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2541) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2541 : oddCount 2541 13 = 6 ∧ acceleratedOrbit 13 2541 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2541 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2541) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2541.1, data_13_2541.2]

/-- Complete interval computation for depth 13, residue 2542. -/
theorem bounds_13_2542 : exactInterval 13 2542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2542 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2542) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2542 : oddCount 2542 13 = 6 ∧ acceleratedOrbit 13 2542 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2542 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2542) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2542.1, data_13_2542.2]

/-- Complete interval computation for depth 13, residue 2543. -/
theorem bounds_13_2543 : exactInterval 13 2543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2543 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2543) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2543 : oddCount 2543 13 = 9 ∧ acceleratedOrbit 13 2543 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2543 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2543) = 3 ^ 9 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2543.1, data_13_2543.2]

/-- Complete interval computation for depth 13, residue 2544. -/
theorem bounds_13_2544 : exactInterval 13 2544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2544 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2544) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2544 : oddCount 2544 13 = 8 ∧ acceleratedOrbit 13 2544 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2544 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2544) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2544.1, data_13_2544.2]

/-- Complete interval computation for depth 13, residue 2545. -/
theorem bounds_13_2545 : exactInterval 13 2545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2545 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2545) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2545 : oddCount 2545 13 = 5 ∧ acceleratedOrbit 13 2545 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2545 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2545) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2545.1, data_13_2545.2]

/-- Complete interval computation for depth 13, residue 2546. -/
theorem bounds_13_2546 : exactInterval 13 2546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2546 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2546) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2546 : oddCount 2546 13 = 6 ∧ acceleratedOrbit 13 2546 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2546 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2546) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2546.1, data_13_2546.2]

/-- Complete interval computation for depth 13, residue 2547. -/
theorem bounds_13_2547 : exactInterval 13 2547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2547 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2547) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2547 : oddCount 2547 13 = 6 ∧ acceleratedOrbit 13 2547 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2547 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2547) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2547.1, data_13_2547.2]

/-- Complete interval computation for depth 13, residue 2548. -/
theorem bounds_13_2548 : exactInterval 13 2548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2548 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2548) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2548 : oddCount 2548 13 = 8 ∧ acceleratedOrbit 13 2548 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2548 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2548) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2548.1, data_13_2548.2]

/-- Complete interval computation for depth 13, residue 2549. -/
theorem bounds_13_2549 : exactInterval 13 2549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2549 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2549) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2549 : oddCount 2549 13 = 8 ∧ acceleratedOrbit 13 2549 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2549 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2549) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2549.1, data_13_2549.2]

/-- Complete interval computation for depth 13, residue 2550. -/
theorem bounds_13_2550 : exactInterval 13 2550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2550 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2550) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2550 : oddCount 2550 13 = 8 ∧ acceleratedOrbit 13 2550 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2550 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2550) = 3 ^ 8 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2550.1, data_13_2550.2]

/-- Complete interval computation for depth 13, residue 2551. -/
theorem bounds_13_2551 : exactInterval 13 2551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2551 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2551) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2551 : oddCount 2551 13 = 8 ∧ acceleratedOrbit 13 2551 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2551 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2551) = 3 ^ 8 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2551.1, data_13_2551.2]

/-- Complete interval computation for depth 13, residue 2552. -/
theorem bounds_13_2552 : exactInterval 13 2552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2552 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2552) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2552 : oddCount 2552 13 = 8 ∧ acceleratedOrbit 13 2552 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2552 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2552) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2552.1, data_13_2552.2]

/-- Complete interval computation for depth 13, residue 2553. -/
theorem bounds_13_2553 : exactInterval 13 2553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2553 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2553) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2553 : oddCount 2553 13 = 8 ∧ acceleratedOrbit 13 2553 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2553 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2553) = 3 ^ 8 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2553.1, data_13_2553.2]

end Collatz.Research.StoppingAtlas.Batch0633
