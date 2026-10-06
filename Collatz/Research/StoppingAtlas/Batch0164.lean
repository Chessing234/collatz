import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0164

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1479. -/
theorem bounds_11_1479 : exactInterval 11 1479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1479 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1479) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1479 : oddCount 1479 11 = 6 ∧ acceleratedOrbit 11 1479 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1479 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1479) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1479.1, data_11_1479.2]

/-- Complete interval computation for depth 11, residue 1480. -/
theorem bounds_11_1480 : exactInterval 11 1480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1480 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1480) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1480 : oddCount 1480 11 = 4 ∧ acceleratedOrbit 11 1480 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1480 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1480) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1480.1, data_11_1480.2]

/-- Complete interval computation for depth 11, residue 1481. -/
theorem bounds_11_1481 : exactInterval 11 1481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1481 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1481) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1481 : oddCount 1481 11 = 5 ∧ acceleratedOrbit 11 1481 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1481 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1481) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1481.1, data_11_1481.2]

/-- Complete interval computation for depth 11, residue 1482. -/
theorem bounds_11_1482 : exactInterval 11 1482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1482 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1482) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1482 : oddCount 1482 11 = 4 ∧ acceleratedOrbit 11 1482 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1482 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1482) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1482.1, data_11_1482.2]

/-- Complete interval computation for depth 11, residue 1483. -/
theorem bounds_11_1483 : exactInterval 11 1483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1483 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1483) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1483 : oddCount 1483 11 = 6 ∧ acceleratedOrbit 11 1483 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1483 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1483) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1483.1, data_11_1483.2]

/-- Complete interval computation for depth 11, residue 1484. -/
theorem bounds_11_1484 : exactInterval 11 1484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1484 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1484) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1484 : oddCount 1484 11 = 4 ∧ acceleratedOrbit 11 1484 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1484 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1484) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1484.1, data_11_1484.2]

/-- Complete interval computation for depth 11, residue 1485. -/
theorem bounds_11_1485 : exactInterval 11 1485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1485 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1485) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1485 : oddCount 1485 11 = 4 ∧ acceleratedOrbit 11 1485 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1485 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1485) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1485.1, data_11_1485.2]

/-- Complete interval computation for depth 11, residue 1486. -/
theorem bounds_11_1486 : exactInterval 11 1486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1486 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1486) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1486 : oddCount 1486 11 = 8 ∧ acceleratedOrbit 11 1486 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1486 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1486) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1486.1, data_11_1486.2]

/-- Complete interval computation for depth 11, residue 1487. -/
theorem bounds_11_1487 : exactInterval 11 1487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1487 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1487) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1487 : oddCount 1487 11 = 8 ∧ acceleratedOrbit 11 1487 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1487 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1487) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1487.1, data_11_1487.2]

/-- Complete interval computation for depth 11, residue 1488. -/
theorem bounds_11_1488 : exactInterval 11 1488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1488 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1488) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1488 : oddCount 1488 11 = 3 ∧ acceleratedOrbit 11 1488 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1488 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1488) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1488.1, data_11_1488.2]

/-- Complete interval computation for depth 11, residue 1489. -/
theorem bounds_11_1489 : exactInterval 11 1489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1489 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1489) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1489 : oddCount 1489 11 = 4 ∧ acceleratedOrbit 11 1489 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1489 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1489) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1489.1, data_11_1489.2]

/-- Complete interval computation for depth 11, residue 1490. -/
theorem bounds_11_1490 : exactInterval 11 1490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1490 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1490) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1490 : oddCount 1490 11 = 7 ∧ acceleratedOrbit 11 1490 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1490 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1490) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1490.1, data_11_1490.2]

/-- Complete interval computation for depth 11, residue 1491. -/
theorem bounds_11_1491 : exactInterval 11 1491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1491 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1491) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1491 : oddCount 1491 11 = 7 ∧ acceleratedOrbit 11 1491 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1491 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1491) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1491.1, data_11_1491.2]

/-- Complete interval computation for depth 11, residue 1492. -/
theorem bounds_11_1492 : exactInterval 11 1492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1492 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1492) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1492 : oddCount 1492 11 = 3 ∧ acceleratedOrbit 11 1492 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1492 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1492) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1492.1, data_11_1492.2]

/-- Complete interval computation for depth 11, residue 1493. -/
theorem bounds_11_1493 : exactInterval 11 1493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1493 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1493) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1493 : oddCount 1493 11 = 3 ∧ acceleratedOrbit 11 1493 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1493 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1493) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1493.1, data_11_1493.2]

/-- Complete interval computation for depth 11, residue 1494. -/
theorem bounds_11_1494 : exactInterval 11 1494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1494 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1494) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1494 : oddCount 1494 11 = 6 ∧ acceleratedOrbit 11 1494 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1494 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1494) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1494.1, data_11_1494.2]

end Collatz.Research.StoppingAtlas.Batch0164
