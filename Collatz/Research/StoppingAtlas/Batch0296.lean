import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0296

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1459. -/
theorem bounds_12_1459 : exactInterval 12 1459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1459 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1459) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1459 : oddCount 1459 12 = 4 ∧ acceleratedOrbit 12 1459 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1459 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1459) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1459.1, data_12_1459.2]

/-- Complete interval computation for depth 12, residue 1460. -/
theorem bounds_12_1460 : exactInterval 12 1460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1460 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1460) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1460 : oddCount 1460 12 = 6 ∧ acceleratedOrbit 12 1460 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1460 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1460) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1460.1, data_12_1460.2]

/-- Complete interval computation for depth 12, residue 1461. -/
theorem bounds_12_1461 : exactInterval 12 1461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1461 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1461) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1461 : oddCount 1461 12 = 6 ∧ acceleratedOrbit 12 1461 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1461 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1461) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1461.1, data_12_1461.2]

/-- Complete interval computation for depth 12, residue 1462. -/
theorem bounds_12_1462 : exactInterval 12 1462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1462 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1462) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1462 : oddCount 1462 12 = 8 ∧ acceleratedOrbit 12 1462 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1462 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1462) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1462.1, data_12_1462.2]

/-- Complete interval computation for depth 12, residue 1463. -/
theorem bounds_12_1463 : exactInterval 12 1463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1463 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1463) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1463 : oddCount 1463 12 = 8 ∧ acceleratedOrbit 12 1463 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1463 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1463) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1463.1, data_12_1463.2]

/-- Complete interval computation for depth 12, residue 1464. -/
theorem bounds_12_1464 : exactInterval 12 1464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1464 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1464) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1464 : oddCount 1464 12 = 6 ∧ acceleratedOrbit 12 1464 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1464 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1464) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1464.1, data_12_1464.2]

/-- Complete interval computation for depth 12, residue 1465. -/
theorem bounds_12_1465 : exactInterval 12 1465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1465 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1465) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1465 : oddCount 1465 12 = 4 ∧ acceleratedOrbit 12 1465 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1465 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1465) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1465.1, data_12_1465.2]

/-- Complete interval computation for depth 12, residue 1466. -/
theorem bounds_12_1466 : exactInterval 12 1466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1466 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1466) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1466 : oddCount 1466 12 = 6 ∧ acceleratedOrbit 12 1466 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1466 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1466) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1466.1, data_12_1466.2]

/-- Complete interval computation for depth 12, residue 1467. -/
theorem bounds_12_1467 : exactInterval 12 1467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1467 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1467) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1467 : oddCount 1467 12 = 7 ∧ acceleratedOrbit 12 1467 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1467 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1467) = 3 ^ 7 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1467.1, data_12_1467.2]

/-- Complete interval computation for depth 12, residue 1468. -/
theorem bounds_12_1468 : exactInterval 12 1468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1468 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1468) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1468 : oddCount 1468 12 = 6 ∧ acceleratedOrbit 12 1468 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1468 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1468) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1468.1, data_12_1468.2]

/-- Complete interval computation for depth 12, residue 1469. -/
theorem bounds_12_1469 : exactInterval 12 1469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1469 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1469) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1469 : oddCount 1469 12 = 6 ∧ acceleratedOrbit 12 1469 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1469 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1469) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1469.1, data_12_1469.2]

/-- Complete interval computation for depth 12, residue 1470. -/
theorem bounds_12_1470 : exactInterval 12 1470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1470 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1470) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1470 : oddCount 1470 12 = 6 ∧ acceleratedOrbit 12 1470 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1470 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1470) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1470.1, data_12_1470.2]

/-- Complete interval computation for depth 12, residue 1471. -/
theorem bounds_12_1471 : exactInterval 12 1471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1471 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1471) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1471 : oddCount 1471 12 = 11 ∧ acceleratedOrbit 12 1471 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1471 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1471) = 3 ^ 11 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1471.1, data_12_1471.2]

/-- Complete interval computation for depth 12, residue 1472. -/
theorem bounds_12_1472 : exactInterval 12 1472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1472 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1472) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1472 : oddCount 1472 12 = 3 ∧ acceleratedOrbit 12 1472 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1472 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1472) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1472.1, data_12_1472.2]

/-- Complete interval computation for depth 12, residue 1473. -/
theorem bounds_12_1473 : exactInterval 12 1473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1473 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1473) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1473 : oddCount 1473 12 = 6 ∧ acceleratedOrbit 12 1473 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1473 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1473) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1473.1, data_12_1473.2]

end Collatz.Research.StoppingAtlas.Batch0296
