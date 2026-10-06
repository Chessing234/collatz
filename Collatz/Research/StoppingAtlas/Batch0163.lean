import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0163

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1464. -/
theorem bounds_11_1464 : exactInterval 11 1464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1464 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1464) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1464 : oddCount 1464 11 = 5 ∧ acceleratedOrbit 11 1464 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1464 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1464) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1464.1, data_11_1464.2]

/-- Complete interval computation for depth 11, residue 1465. -/
theorem bounds_11_1465 : exactInterval 11 1465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1465 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1465) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1465 : oddCount 1465 11 = 4 ∧ acceleratedOrbit 11 1465 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1465 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1465) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1465.1, data_11_1465.2]

/-- Complete interval computation for depth 11, residue 1466. -/
theorem bounds_11_1466 : exactInterval 11 1466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1466 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1466) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1466 : oddCount 1466 11 = 5 ∧ acceleratedOrbit 11 1466 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1466 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1466) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1466.1, data_11_1466.2]

/-- Complete interval computation for depth 11, residue 1467. -/
theorem bounds_11_1467 : exactInterval 11 1467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1467 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1467) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1467 : oddCount 1467 11 = 6 ∧ acceleratedOrbit 11 1467 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1467 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1467) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1467.1, data_11_1467.2]

/-- Complete interval computation for depth 11, residue 1468. -/
theorem bounds_11_1468 : exactInterval 11 1468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1468 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1468) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1468 : oddCount 1468 11 = 6 ∧ acceleratedOrbit 11 1468 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1468 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1468) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1468.1, data_11_1468.2]

/-- Complete interval computation for depth 11, residue 1469. -/
theorem bounds_11_1469 : exactInterval 11 1469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1469 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1469) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1469 : oddCount 1469 11 = 6 ∧ acceleratedOrbit 11 1469 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1469 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1469) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1469.1, data_11_1469.2]

/-- Complete interval computation for depth 11, residue 1470. -/
theorem bounds_11_1470 : exactInterval 11 1470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1470 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1470) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1470 : oddCount 1470 11 = 6 ∧ acceleratedOrbit 11 1470 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1470 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1470) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1470.1, data_11_1470.2]

/-- Complete interval computation for depth 11, residue 1471. -/
theorem bounds_11_1471 : exactInterval 11 1471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1471 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1471) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1471 : oddCount 1471 11 = 10 ∧ acceleratedOrbit 11 1471 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1471 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1471) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1471.1, data_11_1471.2]

/-- Complete interval computation for depth 11, residue 1472. -/
theorem bounds_11_1472 : exactInterval 11 1472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1472 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1472) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1472 : oddCount 1472 11 = 3 ∧ acceleratedOrbit 11 1472 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1472 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1472) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1472.1, data_11_1472.2]

/-- Complete interval computation for depth 11, residue 1473. -/
theorem bounds_11_1473 : exactInterval 11 1473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1473 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1473) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1473 : oddCount 1473 11 = 6 ∧ acceleratedOrbit 11 1473 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1473 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1473) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1473.1, data_11_1473.2]

/-- Complete interval computation for depth 11, residue 1474. -/
theorem bounds_11_1474 : exactInterval 11 1474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1474 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1474) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1474 : oddCount 1474 11 = 7 ∧ acceleratedOrbit 11 1474 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1474 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1474) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1474.1, data_11_1474.2]

/-- Complete interval computation for depth 11, residue 1475. -/
theorem bounds_11_1475 : exactInterval 11 1475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1475 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1475) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1475 : oddCount 1475 11 = 7 ∧ acceleratedOrbit 11 1475 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1475 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1475) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1475.1, data_11_1475.2]

/-- Complete interval computation for depth 11, residue 1476. -/
theorem bounds_11_1476 : exactInterval 11 1476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1476 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1476) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1476 : oddCount 1476 11 = 3 ∧ acceleratedOrbit 11 1476 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1476 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1476) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1476.1, data_11_1476.2]

/-- Complete interval computation for depth 11, residue 1477. -/
theorem bounds_11_1477 : exactInterval 11 1477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1477 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1477) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1477 : oddCount 1477 11 = 3 ∧ acceleratedOrbit 11 1477 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1477 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1477) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1477.1, data_11_1477.2]

/-- Complete interval computation for depth 11, residue 1478. -/
theorem bounds_11_1478 : exactInterval 11 1478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1478 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1478) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1478 : oddCount 1478 11 = 3 ∧ acceleratedOrbit 11 1478 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1478 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1478) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1478.1, data_11_1478.2]

end Collatz.Research.StoppingAtlas.Batch0163
