import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0632

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2524. -/
theorem bounds_13_2524 : exactInterval 13 2524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2524 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2524) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2524 : oddCount 2524 13 = 4 ∧ acceleratedOrbit 13 2524 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2524 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2524) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2524.1, data_13_2524.2]

/-- Complete interval computation for depth 13, residue 2525. -/
theorem bounds_13_2525 : exactInterval 13 2525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2525 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2525) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2525 : oddCount 2525 13 = 4 ∧ acceleratedOrbit 13 2525 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2525 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2525) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2525.1, data_13_2525.2]

/-- Complete interval computation for depth 13, residue 2526. -/
theorem bounds_13_2526 : exactInterval 13 2526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2526 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2526) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2526 : oddCount 2526 13 = 11 ∧ acceleratedOrbit 13 2526 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2526 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2526) = 3 ^ 11 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2526.1, data_13_2526.2]

/-- Complete interval computation for depth 13, residue 2527. -/
theorem bounds_13_2527 : exactInterval 13 2527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2527 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2527) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2527 : oddCount 2527 13 = 11 ∧ acceleratedOrbit 13 2527 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2527 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2527) = 3 ^ 11 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2527.1, data_13_2527.2]

/-- Complete interval computation for depth 13, residue 2528. -/
theorem bounds_13_2528 : exactInterval 13 2528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2528 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2528) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2528 : oddCount 2528 13 = 5 ∧ acceleratedOrbit 13 2528 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2528 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2528) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2528.1, data_13_2528.2]

/-- Complete interval computation for depth 13, residue 2529. -/
theorem bounds_13_2529 : exactInterval 13 2529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2529 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2529) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2529 : oddCount 2529 13 = 7 ∧ acceleratedOrbit 13 2529 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2529 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2529) = 3 ^ 7 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2529.1, data_13_2529.2]

/-- Complete interval computation for depth 13, residue 2530. -/
theorem bounds_13_2530 : exactInterval 13 2530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2530 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2530) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2530 : oddCount 2530 13 = 5 ∧ acceleratedOrbit 13 2530 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2530 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2530) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2530.1, data_13_2530.2]

/-- Complete interval computation for depth 13, residue 2531. -/
theorem bounds_13_2531 : exactInterval 13 2531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2531 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2531) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2531 : oddCount 2531 13 = 5 ∧ acceleratedOrbit 13 2531 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2531 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2531) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2531.1, data_13_2531.2]

/-- Complete interval computation for depth 13, residue 2532. -/
theorem bounds_13_2532 : exactInterval 13 2532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2532 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2532) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2532 : oddCount 2532 13 = 6 ∧ acceleratedOrbit 13 2532 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2532 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2532) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2532.1, data_13_2532.2]

/-- Complete interval computation for depth 13, residue 2533. -/
theorem bounds_13_2533 : exactInterval 13 2533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2533 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2533) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2533 : oddCount 2533 13 = 6 ∧ acceleratedOrbit 13 2533 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2533 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2533) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2533.1, data_13_2533.2]

/-- Complete interval computation for depth 13, residue 2534. -/
theorem bounds_13_2534 : exactInterval 13 2534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2534 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2534) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2534 : oddCount 2534 13 = 6 ∧ acceleratedOrbit 13 2534 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2534 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2534) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2534.1, data_13_2534.2]

/-- Complete interval computation for depth 13, residue 2535. -/
theorem bounds_13_2535 : exactInterval 13 2535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2535 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2535) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2535 : oddCount 2535 13 = 9 ∧ acceleratedOrbit 13 2535 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2535 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2535) = 3 ^ 9 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2535.1, data_13_2535.2]

/-- Complete interval computation for depth 13, residue 2536. -/
theorem bounds_13_2536 : exactInterval 13 2536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2536 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2536) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2536 : oddCount 2536 13 = 5 ∧ acceleratedOrbit 13 2536 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2536 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2536) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2536.1, data_13_2536.2]

/-- Complete interval computation for depth 13, residue 2537. -/
theorem bounds_13_2537 : exactInterval 13 2537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2537 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2537) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2537 : oddCount 2537 13 = 9 ∧ acceleratedOrbit 13 2537 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2537 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2537) = 3 ^ 9 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2537.1, data_13_2537.2]

/-- Complete interval computation for depth 13, residue 2538. -/
theorem bounds_13_2538 : exactInterval 13 2538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2538 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2538) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2538 : oddCount 2538 13 = 5 ∧ acceleratedOrbit 13 2538 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2538 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2538) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2538.1, data_13_2538.2]

end Collatz.Research.StoppingAtlas.Batch0632
