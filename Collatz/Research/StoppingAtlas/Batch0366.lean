import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0366

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2534. -/
theorem bounds_12_2534 : exactInterval 12 2534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2534 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2534) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2534 : oddCount 2534 12 = 6 ∧ acceleratedOrbit 12 2534 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2534 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2534) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2534.1, data_12_2534.2]

/-- Complete interval computation for depth 12, residue 2535. -/
theorem bounds_12_2535 : exactInterval 12 2535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2535 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2535) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2535 : oddCount 2535 12 = 8 ∧ acceleratedOrbit 12 2535 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2535 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2535) = 3 ^ 8 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2535.1, data_12_2535.2]

/-- Complete interval computation for depth 12, residue 2536. -/
theorem bounds_12_2536 : exactInterval 12 2536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2536 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2536) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2536 : oddCount 2536 12 = 5 ∧ acceleratedOrbit 12 2536 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2536 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2536) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2536.1, data_12_2536.2]

/-- Complete interval computation for depth 12, residue 2537. -/
theorem bounds_12_2537 : exactInterval 12 2537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2537 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2537) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2537 : oddCount 2537 12 = 8 ∧ acceleratedOrbit 12 2537 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2537 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2537) = 3 ^ 8 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2537.1, data_12_2537.2]

/-- Complete interval computation for depth 12, residue 2538. -/
theorem bounds_12_2538 : exactInterval 12 2538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2538 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2538) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2538 : oddCount 2538 12 = 5 ∧ acceleratedOrbit 12 2538 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2538 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2538) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2538.1, data_12_2538.2]

/-- Complete interval computation for depth 12, residue 2539. -/
theorem bounds_12_2539 : exactInterval 12 2539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2539 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2539) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2539 : oddCount 2539 12 = 8 ∧ acceleratedOrbit 12 2539 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2539 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2539) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2539.1, data_12_2539.2]

/-- Complete interval computation for depth 12, residue 2540. -/
theorem bounds_12_2540 : exactInterval 12 2540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2540 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2540) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2540 : oddCount 2540 12 = 5 ∧ acceleratedOrbit 12 2540 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2540 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2540) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2540.1, data_12_2540.2]

/-- Complete interval computation for depth 12, residue 2541. -/
theorem bounds_12_2541 : exactInterval 12 2541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2541 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2541) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2541 : oddCount 2541 12 = 5 ∧ acceleratedOrbit 12 2541 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2541 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2541) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2541.1, data_12_2541.2]

/-- Complete interval computation for depth 12, residue 2542. -/
theorem bounds_12_2542 : exactInterval 12 2542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2542 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2542) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2542 : oddCount 2542 12 = 5 ∧ acceleratedOrbit 12 2542 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2542 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2542) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2542.1, data_12_2542.2]

/-- Complete interval computation for depth 12, residue 2543. -/
theorem bounds_12_2543 : exactInterval 12 2543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2543 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2543) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2543 : oddCount 2543 12 = 9 ∧ acceleratedOrbit 12 2543 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2543 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2543) = 3 ^ 9 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2543.1, data_12_2543.2]

/-- Complete interval computation for depth 12, residue 2544. -/
theorem bounds_12_2544 : exactInterval 12 2544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2544 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2544) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2544 : oddCount 2544 12 = 7 ∧ acceleratedOrbit 12 2544 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2544 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2544) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2544.1, data_12_2544.2]

/-- Complete interval computation for depth 12, residue 2545. -/
theorem bounds_12_2545 : exactInterval 12 2545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2545 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2545) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2545 : oddCount 2545 12 = 5 ∧ acceleratedOrbit 12 2545 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2545 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2545) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2545.1, data_12_2545.2]

/-- Complete interval computation for depth 12, residue 2546. -/
theorem bounds_12_2546 : exactInterval 12 2546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2546 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2546) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2546 : oddCount 2546 12 = 6 ∧ acceleratedOrbit 12 2546 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2546 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2546) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2546.1, data_12_2546.2]

/-- Complete interval computation for depth 12, residue 2547. -/
theorem bounds_12_2547 : exactInterval 12 2547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2547 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2547) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2547 : oddCount 2547 12 = 6 ∧ acceleratedOrbit 12 2547 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2547 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2547) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2547.1, data_12_2547.2]

/-- Complete interval computation for depth 12, residue 2548. -/
theorem bounds_12_2548 : exactInterval 12 2548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2548 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2548) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2548 : oddCount 2548 12 = 7 ∧ acceleratedOrbit 12 2548 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2548 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2548) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2548.1, data_12_2548.2]

end Collatz.Research.StoppingAtlas.Batch0366
