import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0297

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1474. -/
theorem bounds_12_1474 : exactInterval 12 1474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1474 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1474) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1474 : oddCount 1474 12 = 8 ∧ acceleratedOrbit 12 1474 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1474 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1474) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1474.1, data_12_1474.2]

/-- Complete interval computation for depth 12, residue 1475. -/
theorem bounds_12_1475 : exactInterval 12 1475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1475 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1475) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1475 : oddCount 1475 12 = 8 ∧ acceleratedOrbit 12 1475 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1475 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1475) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1475.1, data_12_1475.2]

/-- Complete interval computation for depth 12, residue 1476. -/
theorem bounds_12_1476 : exactInterval 12 1476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1476 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1476) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1476 : oddCount 1476 12 = 3 ∧ acceleratedOrbit 12 1476 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1476 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1476) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1476.1, data_12_1476.2]

/-- Complete interval computation for depth 12, residue 1477. -/
theorem bounds_12_1477 : exactInterval 12 1477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1477 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1477) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1477 : oddCount 1477 12 = 3 ∧ acceleratedOrbit 12 1477 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1477 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1477) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1477.1, data_12_1477.2]

/-- Complete interval computation for depth 12, residue 1478. -/
theorem bounds_12_1478 : exactInterval 12 1478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1478 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1478) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1478 : oddCount 1478 12 = 3 ∧ acceleratedOrbit 12 1478 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1478 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1478) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1478.1, data_12_1478.2]

/-- Complete interval computation for depth 12, residue 1479. -/
theorem bounds_12_1479 : exactInterval 12 1479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1479 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1479) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1479 : oddCount 1479 12 = 7 ∧ acceleratedOrbit 12 1479 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1479 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1479) = 3 ^ 7 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1479.1, data_12_1479.2]

/-- Complete interval computation for depth 12, residue 1480. -/
theorem bounds_12_1480 : exactInterval 12 1480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1480 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1480) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1480 : oddCount 1480 12 = 5 ∧ acceleratedOrbit 12 1480 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1480 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1480) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1480.1, data_12_1480.2]

/-- Complete interval computation for depth 12, residue 1481. -/
theorem bounds_12_1481 : exactInterval 12 1481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1481 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1481) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1481 : oddCount 1481 12 = 5 ∧ acceleratedOrbit 12 1481 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1481 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1481) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1481.1, data_12_1481.2]

/-- Complete interval computation for depth 12, residue 1482. -/
theorem bounds_12_1482 : exactInterval 12 1482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1482 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1482) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1482 : oddCount 1482 12 = 5 ∧ acceleratedOrbit 12 1482 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1482 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1482) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1482.1, data_12_1482.2]

/-- Complete interval computation for depth 12, residue 1483. -/
theorem bounds_12_1483 : exactInterval 12 1483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1483 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1483) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1483 : oddCount 1483 12 = 6 ∧ acceleratedOrbit 12 1483 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1483 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1483) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1483.1, data_12_1483.2]

/-- Complete interval computation for depth 12, residue 1484. -/
theorem bounds_12_1484 : exactInterval 12 1484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1484 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1484) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1484 : oddCount 1484 12 = 5 ∧ acceleratedOrbit 12 1484 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1484 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1484) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1484.1, data_12_1484.2]

/-- Complete interval computation for depth 12, residue 1485. -/
theorem bounds_12_1485 : exactInterval 12 1485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1485 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1485) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1485 : oddCount 1485 12 = 5 ∧ acceleratedOrbit 12 1485 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1485 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1485) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1485.1, data_12_1485.2]

/-- Complete interval computation for depth 12, residue 1486. -/
theorem bounds_12_1486 : exactInterval 12 1486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1486 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1486) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1486 : oddCount 1486 12 = 9 ∧ acceleratedOrbit 12 1486 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1486 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1486) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1486.1, data_12_1486.2]

/-- Complete interval computation for depth 12, residue 1487. -/
theorem bounds_12_1487 : exactInterval 12 1487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1487 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1487) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1487 : oddCount 1487 12 = 9 ∧ acceleratedOrbit 12 1487 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1487 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1487) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1487.1, data_12_1487.2]

/-- Complete interval computation for depth 12, residue 1488. -/
theorem bounds_12_1488 : exactInterval 12 1488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1488 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1488) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1488 : oddCount 1488 12 = 3 ∧ acceleratedOrbit 12 1488 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1488 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1488) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1488.1, data_12_1488.2]

end Collatz.Research.StoppingAtlas.Batch0297
