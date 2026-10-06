import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0363

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2488. -/
theorem bounds_12_2488 : exactInterval 12 2488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2488 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2488) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2488 : oddCount 2488 12 = 6 ∧ acceleratedOrbit 12 2488 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2488 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2488) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2488.1, data_12_2488.2]

/-- Complete interval computation for depth 12, residue 2489. -/
theorem bounds_12_2489 : exactInterval 12 2489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2489 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2489) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2489 : oddCount 2489 12 = 5 ∧ acceleratedOrbit 12 2489 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2489 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2489) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2489.1, data_12_2489.2]

/-- Complete interval computation for depth 12, residue 2490. -/
theorem bounds_12_2490 : exactInterval 12 2490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2490 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2490) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2490 : oddCount 2490 12 = 6 ∧ acceleratedOrbit 12 2490 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2490 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2490) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2490.1, data_12_2490.2]

/-- Complete interval computation for depth 12, residue 2491. -/
theorem bounds_12_2491 : exactInterval 12 2491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2491 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2491) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2491 : oddCount 2491 12 = 8 ∧ acceleratedOrbit 12 2491 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2491 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2491) = 3 ^ 8 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2491.1, data_12_2491.2]

/-- Complete interval computation for depth 12, residue 2492. -/
theorem bounds_12_2492 : exactInterval 12 2492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2492 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2492) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2492 : oddCount 2492 12 = 7 ∧ acceleratedOrbit 12 2492 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2492 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2492) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2492.1, data_12_2492.2]

/-- Complete interval computation for depth 12, residue 2493. -/
theorem bounds_12_2493 : exactInterval 12 2493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2493 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2493) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2493 : oddCount 2493 12 = 7 ∧ acceleratedOrbit 12 2493 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2493 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2493) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2493.1, data_12_2493.2]

/-- Complete interval computation for depth 12, residue 2494. -/
theorem bounds_12_2494 : exactInterval 12 2494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2494 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2494) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2494 : oddCount 2494 12 = 7 ∧ acceleratedOrbit 12 2494 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2494 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2494) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2494.1, data_12_2494.2]

/-- Complete interval computation for depth 12, residue 2495. -/
theorem bounds_12_2495 : exactInterval 12 2495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2495 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2495) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2495 : oddCount 2495 12 = 10 ∧ acceleratedOrbit 12 2495 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2495 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2495) = 3 ^ 10 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2495.1, data_12_2495.2]

/-- Complete interval computation for depth 12, residue 2496. -/
theorem bounds_12_2496 : exactInterval 12 2496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2496 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2496) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2496 : oddCount 2496 12 = 5 ∧ acceleratedOrbit 12 2496 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2496 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2496) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2496.1, data_12_2496.2]

/-- Complete interval computation for depth 12, residue 2497. -/
theorem bounds_12_2497 : exactInterval 12 2497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2497 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2497) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2497 : oddCount 2497 12 = 7 ∧ acceleratedOrbit 12 2497 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2497 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2497) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2497.1, data_12_2497.2]

/-- Complete interval computation for depth 12, residue 2498. -/
theorem bounds_12_2498 : exactInterval 12 2498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2498 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2498) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2498 : oddCount 2498 12 = 8 ∧ acceleratedOrbit 12 2498 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2498 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2498) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2498.1, data_12_2498.2]

/-- Complete interval computation for depth 12, residue 2499. -/
theorem bounds_12_2499 : exactInterval 12 2499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2499 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2499) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2499 : oddCount 2499 12 = 8 ∧ acceleratedOrbit 12 2499 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2499 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2499) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2499.1, data_12_2499.2]

/-- Complete interval computation for depth 12, residue 2500. -/
theorem bounds_12_2500 : exactInterval 12 2500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2500 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2500) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2500 : oddCount 2500 12 = 3 ∧ acceleratedOrbit 12 2500 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2500 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2500) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2500.1, data_12_2500.2]

/-- Complete interval computation for depth 12, residue 2501. -/
theorem bounds_12_2501 : exactInterval 12 2501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2501 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2501) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2501 : oddCount 2501 12 = 3 ∧ acceleratedOrbit 12 2501 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2501 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2501) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2501.1, data_12_2501.2]

/-- Complete interval computation for depth 12, residue 2502. -/
theorem bounds_12_2502 : exactInterval 12 2502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2502 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2502) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2502 : oddCount 2502 12 = 3 ∧ acceleratedOrbit 12 2502 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2502 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2502) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2502.1, data_12_2502.2]

end Collatz.Research.StoppingAtlas.Batch0363
