import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0563

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1464. -/
theorem bounds_13_1464 : exactInterval 13 1464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1464 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1464) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1464 : oddCount 1464 13 = 7 ∧ acceleratedOrbit 13 1464 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1464 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1464) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1464.1, data_13_1464.2]

/-- Complete interval computation for depth 13, residue 1465. -/
theorem bounds_13_1465 : exactInterval 13 1465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1465 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1465) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1465 : oddCount 1465 13 = 5 ∧ acceleratedOrbit 13 1465 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1465 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1465) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1465.1, data_13_1465.2]

/-- Complete interval computation for depth 13, residue 1466. -/
theorem bounds_13_1466 : exactInterval 13 1466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1466 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1466) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1466 : oddCount 1466 13 = 7 ∧ acceleratedOrbit 13 1466 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1466 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1466) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1466.1, data_13_1466.2]

/-- Complete interval computation for depth 13, residue 1467. -/
theorem bounds_13_1467 : exactInterval 13 1467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1467 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1467) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1467 : oddCount 1467 13 = 8 ∧ acceleratedOrbit 13 1467 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1467 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1467) = 3 ^ 8 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1467.1, data_13_1467.2]

/-- Complete interval computation for depth 13, residue 1468. -/
theorem bounds_13_1468 : exactInterval 13 1468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1468 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1468) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1468 : oddCount 1468 13 = 6 ∧ acceleratedOrbit 13 1468 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1468 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1468) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1468.1, data_13_1468.2]

/-- Complete interval computation for depth 13, residue 1469. -/
theorem bounds_13_1469 : exactInterval 13 1469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1469 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1469) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1469 : oddCount 1469 13 = 6 ∧ acceleratedOrbit 13 1469 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1469 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1469) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1469.1, data_13_1469.2]

/-- Complete interval computation for depth 13, residue 1470. -/
theorem bounds_13_1470 : exactInterval 13 1470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1470 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1470) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1470 : oddCount 1470 13 = 6 ∧ acceleratedOrbit 13 1470 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1470 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1470) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1470.1, data_13_1470.2]

/-- Complete interval computation for depth 13, residue 1471. -/
theorem bounds_13_1471 : exactInterval 13 1471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1471 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1471) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1471 : oddCount 1471 13 = 12 ∧ acceleratedOrbit 13 1471 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1471 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1471) = 3 ^ 12 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1471.1, data_13_1471.2]

/-- Complete interval computation for depth 13, residue 1472. -/
theorem bounds_13_1472 : exactInterval 13 1472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1472 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1472) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1472 : oddCount 1472 13 = 3 ∧ acceleratedOrbit 13 1472 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1472 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1472) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1472.1, data_13_1472.2]

/-- Complete interval computation for depth 13, residue 1473. -/
theorem bounds_13_1473 : exactInterval 13 1473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1473 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1473) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1473 : oddCount 1473 13 = 7 ∧ acceleratedOrbit 13 1473 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1473 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1473) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1473.1, data_13_1473.2]

/-- Complete interval computation for depth 13, residue 1474. -/
theorem bounds_13_1474 : exactInterval 13 1474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1474 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1474) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1474 : oddCount 1474 13 = 9 ∧ acceleratedOrbit 13 1474 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1474 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1474) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1474.1, data_13_1474.2]

/-- Complete interval computation for depth 13, residue 1475. -/
theorem bounds_13_1475 : exactInterval 13 1475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1475 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1475) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1475 : oddCount 1475 13 = 9 ∧ acceleratedOrbit 13 1475 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1475 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1475) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1475.1, data_13_1475.2]

/-- Complete interval computation for depth 13, residue 1476. -/
theorem bounds_13_1476 : exactInterval 13 1476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1476 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1476) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1476 : oddCount 1476 13 = 3 ∧ acceleratedOrbit 13 1476 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1476 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1476) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1476.1, data_13_1476.2]

/-- Complete interval computation for depth 13, residue 1477. -/
theorem bounds_13_1477 : exactInterval 13 1477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1477 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1477) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1477 : oddCount 1477 13 = 3 ∧ acceleratedOrbit 13 1477 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1477 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1477) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1477.1, data_13_1477.2]

/-- Complete interval computation for depth 13, residue 1478. -/
theorem bounds_13_1478 : exactInterval 13 1478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1478 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1478) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1478 : oddCount 1478 13 = 3 ∧ acceleratedOrbit 13 1478 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1478 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1478) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1478.1, data_13_1478.2]

end Collatz.Research.StoppingAtlas.Batch0563
