import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0259

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8454. -/
theorem bounds_15_8454 : exactInterval 15 8454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8454 : oddCount 8454 15 = 8 ∧ acceleratedOrbit 15 8454 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8454) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8454.1, data_15_8454.2]

/-- Complete interval computation for depth 15, residue 8455. -/
theorem bounds_15_8455 : exactInterval 15 8455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8455 : oddCount 8455 15 = 10 ∧ acceleratedOrbit 15 8455 = 15241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8455) = 3 ^ 10 * m + 15241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8455.1, data_15_8455.2]

/-- Complete interval computation for depth 15, residue 8456. -/
theorem bounds_15_8456 : exactInterval 15 8456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8456 : oddCount 8456 15 = 8 ∧ acceleratedOrbit 15 8456 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8456) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8456.1, data_15_8456.2]

/-- Complete interval computation for depth 15, residue 8457. -/
theorem bounds_15_8457 : exactInterval 15 8457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8457 : oddCount 8457 15 = 8 ∧ acceleratedOrbit 15 8457 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8457) = 3 ^ 8 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8457.1, data_15_8457.2]

/-- Complete interval computation for depth 15, residue 8458. -/
theorem bounds_15_8458 : exactInterval 15 8458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8458 : oddCount 8458 15 = 8 ∧ acceleratedOrbit 15 8458 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8458) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8458.1, data_15_8458.2]

/-- Complete interval computation for depth 15, residue 8459. -/
theorem bounds_15_8459 : exactInterval 15 8459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8459 : oddCount 8459 15 = 7 ∧ acceleratedOrbit 15 8459 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8459) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8459.1, data_15_8459.2]

/-- Complete interval computation for depth 15, residue 8460. -/
theorem bounds_15_8460 : exactInterval 15 8460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8460 : oddCount 8460 15 = 8 ∧ acceleratedOrbit 15 8460 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8460) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8460.1, data_15_8460.2]

/-- Complete interval computation for depth 15, residue 8461. -/
theorem bounds_15_8461 : exactInterval 15 8461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8461 : oddCount 8461 15 = 8 ∧ acceleratedOrbit 15 8461 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8461) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8461.1, data_15_8461.2]

/-- Complete interval computation for depth 15, residue 8462. -/
theorem bounds_15_8462 : exactInterval 15 8462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8462 : oddCount 8462 15 = 8 ∧ acceleratedOrbit 15 8462 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8462) = 3 ^ 8 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8462.1, data_15_8462.2]

/-- Complete interval computation for depth 15, residue 8463. -/
theorem bounds_15_8463 : exactInterval 15 8463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8463 : oddCount 8463 15 = 8 ∧ acceleratedOrbit 15 8463 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8463) = 3 ^ 8 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8463.1, data_15_8463.2]

/-- Complete interval computation for depth 15, residue 8464. -/
theorem bounds_15_8464 : exactInterval 15 8464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8464 : oddCount 8464 15 = 3 ∧ acceleratedOrbit 15 8464 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8464) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8464.1, data_15_8464.2]

/-- Complete interval computation for depth 15, residue 8465. -/
theorem bounds_15_8465 : exactInterval 15 8465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8465 : oddCount 8465 15 = 8 ∧ acceleratedOrbit 15 8465 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8465) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8465.1, data_15_8465.2]

/-- Complete interval computation for depth 15, residue 8466. -/
theorem bounds_15_8466 : exactInterval 15 8466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8466 : oddCount 8466 15 = 11 ∧ acceleratedOrbit 15 8466 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8466) = 3 ^ 11 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8466.1, data_15_8466.2]

/-- Complete interval computation for depth 15, residue 8467. -/
theorem bounds_15_8467 : exactInterval 15 8467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8467 : oddCount 8467 15 = 11 ∧ acceleratedOrbit 15 8467 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8467) = 3 ^ 11 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8467.1, data_15_8467.2]

/-- Complete interval computation for depth 15, residue 8468. -/
theorem bounds_15_8468 : exactInterval 15 8468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8468 : oddCount 8468 15 = 3 ∧ acceleratedOrbit 15 8468 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8468) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8468.1, data_15_8468.2]

/-- Complete interval computation for depth 15, residue 8469. -/
theorem bounds_15_8469 : exactInterval 15 8469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8469 : oddCount 8469 15 = 3 ∧ acceleratedOrbit 15 8469 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8469) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8469.1, data_15_8469.2]

/-- Complete interval computation for depth 15, residue 8470. -/
theorem bounds_15_8470 : exactInterval 15 8470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8470 : oddCount 8470 15 = 9 ∧ acceleratedOrbit 15 8470 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8470) = 3 ^ 9 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8470.1, data_15_8470.2]

/-- Complete interval computation for depth 15, residue 8471. -/
theorem bounds_15_8471 : exactInterval 15 8471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8471 : oddCount 8471 15 = 9 ∧ acceleratedOrbit 15 8471 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8471) = 3 ^ 9 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8471.1, data_15_8471.2]

/-- Complete interval computation for depth 15, residue 8472. -/
theorem bounds_15_8472 : exactInterval 15 8472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8472 : oddCount 8472 15 = 3 ∧ acceleratedOrbit 15 8472 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8472) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8472.1, data_15_8472.2]

/-- Complete interval computation for depth 15, residue 8473. -/
theorem bounds_15_8473 : exactInterval 15 8473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8473 : oddCount 8473 15 = 9 ∧ acceleratedOrbit 15 8473 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8473) = 3 ^ 9 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8473.1, data_15_8473.2]

/-- Complete interval computation for depth 15, residue 8474. -/
theorem bounds_15_8474 : exactInterval 15 8474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8474 : oddCount 8474 15 = 3 ∧ acceleratedOrbit 15 8474 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8474) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8474.1, data_15_8474.2]

/-- Complete interval computation for depth 15, residue 8475. -/
theorem bounds_15_8475 : exactInterval 15 8475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8475 : oddCount 8475 15 = 10 ∧ acceleratedOrbit 15 8475 = 15275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8475) = 3 ^ 10 * m + 15275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8475.1, data_15_8475.2]

/-- Complete interval computation for depth 15, residue 8476. -/
theorem bounds_15_8476 : exactInterval 15 8476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8476 : oddCount 8476 15 = 9 ∧ acceleratedOrbit 15 8476 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8476) = 3 ^ 9 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8476.1, data_15_8476.2]

/-- Complete interval computation for depth 15, residue 8477. -/
theorem bounds_15_8477 : exactInterval 15 8477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8477 : oddCount 8477 15 = 9 ∧ acceleratedOrbit 15 8477 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8477) = 3 ^ 9 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8477.1, data_15_8477.2]

/-- Complete interval computation for depth 15, residue 8478. -/
theorem bounds_15_8478 : exactInterval 15 8478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8478 : oddCount 8478 15 = 9 ∧ acceleratedOrbit 15 8478 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8478) = 3 ^ 9 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8478.1, data_15_8478.2]

/-- Complete interval computation for depth 15, residue 8479. -/
theorem bounds_15_8479 : exactInterval 15 8479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8479 : oddCount 8479 15 = 7 ∧ acceleratedOrbit 15 8479 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8479) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8479.1, data_15_8479.2]

/-- Complete interval computation for depth 15, residue 8480. -/
theorem bounds_15_8480 : exactInterval 15 8480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8480 : oddCount 8480 15 = 6 ∧ acceleratedOrbit 15 8480 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8480) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8480.1, data_15_8480.2]

/-- Complete interval computation for depth 15, residue 8481. -/
theorem bounds_15_8481 : exactInterval 15 8481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8481 : oddCount 8481 15 = 9 ∧ acceleratedOrbit 15 8481 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8481) = 3 ^ 9 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8481.1, data_15_8481.2]

/-- Complete interval computation for depth 15, residue 8482. -/
theorem bounds_15_8482 : exactInterval 15 8482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8482 : oddCount 8482 15 = 10 ∧ acceleratedOrbit 15 8482 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8482) = 3 ^ 10 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8482.1, data_15_8482.2]

/-- Complete interval computation for depth 15, residue 8483. -/
theorem bounds_15_8483 : exactInterval 15 8483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8483 : oddCount 8483 15 = 10 ∧ acceleratedOrbit 15 8483 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8483) = 3 ^ 10 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8483.1, data_15_8483.2]

/-- Complete interval computation for depth 15, residue 8484. -/
theorem bounds_15_8484 : exactInterval 15 8484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8484 : oddCount 8484 15 = 10 ∧ acceleratedOrbit 15 8484 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8484) = 3 ^ 10 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8484.1, data_15_8484.2]

/-- Complete interval computation for depth 15, residue 8485. -/
theorem bounds_15_8485 : exactInterval 15 8485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8485 : oddCount 8485 15 = 10 ∧ acceleratedOrbit 15 8485 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8485) = 3 ^ 10 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8485.1, data_15_8485.2]

end Collatz.Research.PassageAtlas.Batch0259
