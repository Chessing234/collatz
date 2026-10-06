import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0365

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2519. -/
theorem bounds_12_2519 : exactInterval 12 2519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2519 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2519) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2519 : oddCount 2519 12 = 8 ∧ acceleratedOrbit 12 2519 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2519 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2519) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2519.1, data_12_2519.2]

/-- Complete interval computation for depth 12, residue 2520. -/
theorem bounds_12_2520 : exactInterval 12 2520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2520 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2520) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2520 : oddCount 2520 12 = 4 ∧ acceleratedOrbit 12 2520 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2520 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2520) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2520.1, data_12_2520.2]

/-- Complete interval computation for depth 12, residue 2521. -/
theorem bounds_12_2521 : exactInterval 12 2521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2521 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2521) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2521 : oddCount 2521 12 = 4 ∧ acceleratedOrbit 12 2521 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2521 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2521) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2521.1, data_12_2521.2]

/-- Complete interval computation for depth 12, residue 2522. -/
theorem bounds_12_2522 : exactInterval 12 2522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2522 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2522) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2522 : oddCount 2522 12 = 4 ∧ acceleratedOrbit 12 2522 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2522 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2522) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2522.1, data_12_2522.2]

/-- Complete interval computation for depth 12, residue 2523. -/
theorem bounds_12_2523 : exactInterval 12 2523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2523 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2523) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2523 : oddCount 2523 12 = 7 ∧ acceleratedOrbit 12 2523 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2523 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2523) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2523.1, data_12_2523.2]

/-- Complete interval computation for depth 12, residue 2524. -/
theorem bounds_12_2524 : exactInterval 12 2524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2524 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2524) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2524 : oddCount 2524 12 = 4 ∧ acceleratedOrbit 12 2524 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2524 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2524) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2524.1, data_12_2524.2]

/-- Complete interval computation for depth 12, residue 2525. -/
theorem bounds_12_2525 : exactInterval 12 2525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2525 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2525) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2525 : oddCount 2525 12 = 4 ∧ acceleratedOrbit 12 2525 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2525 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2525) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2525.1, data_12_2525.2]

/-- Complete interval computation for depth 12, residue 2526. -/
theorem bounds_12_2526 : exactInterval 12 2526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2526 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2526) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2526 : oddCount 2526 12 = 10 ∧ acceleratedOrbit 12 2526 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2526 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2526) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2526.1, data_12_2526.2]

/-- Complete interval computation for depth 12, residue 2527. -/
theorem bounds_12_2527 : exactInterval 12 2527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2527 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2527) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2527 : oddCount 2527 12 = 10 ∧ acceleratedOrbit 12 2527 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2527 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2527) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2527.1, data_12_2527.2]

/-- Complete interval computation for depth 12, residue 2528. -/
theorem bounds_12_2528 : exactInterval 12 2528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2528 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2528) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2528 : oddCount 2528 12 = 5 ∧ acceleratedOrbit 12 2528 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2528 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2528) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2528.1, data_12_2528.2]

/-- Complete interval computation for depth 12, residue 2529. -/
theorem bounds_12_2529 : exactInterval 12 2529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2529 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2529) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2529 : oddCount 2529 12 = 7 ∧ acceleratedOrbit 12 2529 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2529 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2529) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2529.1, data_12_2529.2]

/-- Complete interval computation for depth 12, residue 2530. -/
theorem bounds_12_2530 : exactInterval 12 2530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2530 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2530) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2530 : oddCount 2530 12 = 5 ∧ acceleratedOrbit 12 2530 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2530 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2530) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2530.1, data_12_2530.2]

/-- Complete interval computation for depth 12, residue 2531. -/
theorem bounds_12_2531 : exactInterval 12 2531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2531 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2531) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2531 : oddCount 2531 12 = 5 ∧ acceleratedOrbit 12 2531 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2531 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2531) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2531.1, data_12_2531.2]

/-- Complete interval computation for depth 12, residue 2532. -/
theorem bounds_12_2532 : exactInterval 12 2532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2532 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2532) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2532 : oddCount 2532 12 = 6 ∧ acceleratedOrbit 12 2532 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2532 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2532) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2532.1, data_12_2532.2]

/-- Complete interval computation for depth 12, residue 2533. -/
theorem bounds_12_2533 : exactInterval 12 2533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2533 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2533) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2533 : oddCount 2533 12 = 6 ∧ acceleratedOrbit 12 2533 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2533 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2533) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2533.1, data_12_2533.2]

end Collatz.Research.StoppingAtlas.Batch0365
