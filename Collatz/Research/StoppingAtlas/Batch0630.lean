import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0630

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2493. -/
theorem bounds_13_2493 : exactInterval 13 2493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2493 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2493) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2493 : oddCount 2493 13 = 8 ∧ acceleratedOrbit 13 2493 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2493 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2493) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2493.1, data_13_2493.2]

/-- Complete interval computation for depth 13, residue 2494. -/
theorem bounds_13_2494 : exactInterval 13 2494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2494 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2494) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2494 : oddCount 2494 13 = 8 ∧ acceleratedOrbit 13 2494 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2494 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2494) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2494.1, data_13_2494.2]

/-- Complete interval computation for depth 13, residue 2495. -/
theorem bounds_13_2495 : exactInterval 13 2495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2495 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2495) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2495 : oddCount 2495 13 = 10 ∧ acceleratedOrbit 13 2495 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2495 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2495) = 3 ^ 10 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2495.1, data_13_2495.2]

/-- Complete interval computation for depth 13, residue 2496. -/
theorem bounds_13_2496 : exactInterval 13 2496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2496 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2496) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2496 : oddCount 2496 13 = 5 ∧ acceleratedOrbit 13 2496 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2496 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2496) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2496.1, data_13_2496.2]

/-- Complete interval computation for depth 13, residue 2497. -/
theorem bounds_13_2497 : exactInterval 13 2497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2497 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2497) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2497 : oddCount 2497 13 = 7 ∧ acceleratedOrbit 13 2497 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2497 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2497) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2497.1, data_13_2497.2]

/-- Complete interval computation for depth 13, residue 2498. -/
theorem bounds_13_2498 : exactInterval 13 2498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2498 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2498) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2498 : oddCount 2498 13 = 9 ∧ acceleratedOrbit 13 2498 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2498 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2498) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2498.1, data_13_2498.2]

/-- Complete interval computation for depth 13, residue 2499. -/
theorem bounds_13_2499 : exactInterval 13 2499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2499 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2499) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2499 : oddCount 2499 13 = 9 ∧ acceleratedOrbit 13 2499 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2499 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2499) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2499.1, data_13_2499.2]

/-- Complete interval computation for depth 13, residue 2500. -/
theorem bounds_13_2500 : exactInterval 13 2500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2500 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2500) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2500 : oddCount 2500 13 = 4 ∧ acceleratedOrbit 13 2500 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2500 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2500) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2500.1, data_13_2500.2]

/-- Complete interval computation for depth 13, residue 2501. -/
theorem bounds_13_2501 : exactInterval 13 2501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2501 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2501) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2501 : oddCount 2501 13 = 4 ∧ acceleratedOrbit 13 2501 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2501 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2501) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2501.1, data_13_2501.2]

/-- Complete interval computation for depth 13, residue 2502. -/
theorem bounds_13_2502 : exactInterval 13 2502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2502 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2502) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2502 : oddCount 2502 13 = 4 ∧ acceleratedOrbit 13 2502 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2502 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2502) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2502.1, data_13_2502.2]

/-- Complete interval computation for depth 13, residue 2503. -/
theorem bounds_13_2503 : exactInterval 13 2503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2503 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2503) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2503 : oddCount 2503 13 = 9 ∧ acceleratedOrbit 13 2503 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2503 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2503) = 3 ^ 9 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2503.1, data_13_2503.2]

/-- Complete interval computation for depth 13, residue 2504. -/
theorem bounds_13_2504 : exactInterval 13 2504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2504 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2504) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2504 : oddCount 2504 13 = 7 ∧ acceleratedOrbit 13 2504 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2504 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2504) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2504.1, data_13_2504.2]

/-- Complete interval computation for depth 13, residue 2505. -/
theorem bounds_13_2505 : exactInterval 13 2505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2505 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2505) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2505 : oddCount 2505 13 = 7 ∧ acceleratedOrbit 13 2505 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2505 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2505) = 3 ^ 7 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2505.1, data_13_2505.2]

/-- Complete interval computation for depth 13, residue 2506. -/
theorem bounds_13_2506 : exactInterval 13 2506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2506 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2506) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2506 : oddCount 2506 13 = 7 ∧ acceleratedOrbit 13 2506 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2506 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2506) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2506.1, data_13_2506.2]

/-- Complete interval computation for depth 13, residue 2507. -/
theorem bounds_13_2507 : exactInterval 13 2507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2507 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2507) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2507 : oddCount 2507 13 = 6 ∧ acceleratedOrbit 13 2507 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2507 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2507) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2507.1, data_13_2507.2]

end Collatz.Research.StoppingAtlas.Batch0630
