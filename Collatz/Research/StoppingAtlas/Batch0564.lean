import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0564

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1479. -/
theorem bounds_13_1479 : exactInterval 13 1479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1479 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1479) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1479 : oddCount 1479 13 = 8 ∧ acceleratedOrbit 13 1479 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1479 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1479) = 3 ^ 8 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1479.1, data_13_1479.2]

/-- Complete interval computation for depth 13, residue 1480. -/
theorem bounds_13_1480 : exactInterval 13 1480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1480 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1480) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1480 : oddCount 1480 13 = 6 ∧ acceleratedOrbit 13 1480 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1480 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1480) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1480.1, data_13_1480.2]

/-- Complete interval computation for depth 13, residue 1481. -/
theorem bounds_13_1481 : exactInterval 13 1481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1481 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1481) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1481 : oddCount 1481 13 = 5 ∧ acceleratedOrbit 13 1481 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1481 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1481) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1481.1, data_13_1481.2]

/-- Complete interval computation for depth 13, residue 1482. -/
theorem bounds_13_1482 : exactInterval 13 1482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1482 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1482) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1482 : oddCount 1482 13 = 6 ∧ acceleratedOrbit 13 1482 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1482 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1482) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1482.1, data_13_1482.2]

/-- Complete interval computation for depth 13, residue 1483. -/
theorem bounds_13_1483 : exactInterval 13 1483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1483 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1483) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1483 : oddCount 1483 13 = 7 ∧ acceleratedOrbit 13 1483 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1483 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1483) = 3 ^ 7 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1483.1, data_13_1483.2]

/-- Complete interval computation for depth 13, residue 1484. -/
theorem bounds_13_1484 : exactInterval 13 1484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1484 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1484) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1484 : oddCount 1484 13 = 6 ∧ acceleratedOrbit 13 1484 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1484 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1484) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1484.1, data_13_1484.2]

/-- Complete interval computation for depth 13, residue 1485. -/
theorem bounds_13_1485 : exactInterval 13 1485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1485 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1485) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1485 : oddCount 1485 13 = 6 ∧ acceleratedOrbit 13 1485 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1485 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1485) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1485.1, data_13_1485.2]

/-- Complete interval computation for depth 13, residue 1486. -/
theorem bounds_13_1486 : exactInterval 13 1486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1486 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1486) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1486 : oddCount 1486 13 = 9 ∧ acceleratedOrbit 13 1486 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1486 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1486) = 3 ^ 9 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1486.1, data_13_1486.2]

/-- Complete interval computation for depth 13, residue 1487. -/
theorem bounds_13_1487 : exactInterval 13 1487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1487 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1487) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1487 : oddCount 1487 13 = 9 ∧ acceleratedOrbit 13 1487 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1487 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1487) = 3 ^ 9 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1487.1, data_13_1487.2]

/-- Complete interval computation for depth 13, residue 1488. -/
theorem bounds_13_1488 : exactInterval 13 1488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1488 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1488) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1488 : oddCount 1488 13 = 3 ∧ acceleratedOrbit 13 1488 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1488 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1488) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1488.1, data_13_1488.2]

/-- Complete interval computation for depth 13, residue 1489. -/
theorem bounds_13_1489 : exactInterval 13 1489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1489 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1489) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1489 : oddCount 1489 13 = 6 ∧ acceleratedOrbit 13 1489 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1489 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1489) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1489.1, data_13_1489.2]

/-- Complete interval computation for depth 13, residue 1490. -/
theorem bounds_13_1490 : exactInterval 13 1490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1490 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1490) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1490 : oddCount 1490 13 = 9 ∧ acceleratedOrbit 13 1490 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1490 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1490) = 3 ^ 9 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1490.1, data_13_1490.2]

/-- Complete interval computation for depth 13, residue 1491. -/
theorem bounds_13_1491 : exactInterval 13 1491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1491 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1491) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1491 : oddCount 1491 13 = 9 ∧ acceleratedOrbit 13 1491 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1491 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1491) = 3 ^ 9 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1491.1, data_13_1491.2]

/-- Complete interval computation for depth 13, residue 1492. -/
theorem bounds_13_1492 : exactInterval 13 1492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1492 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1492) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1492 : oddCount 1492 13 = 3 ∧ acceleratedOrbit 13 1492 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1492 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1492) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1492.1, data_13_1492.2]

/-- Complete interval computation for depth 13, residue 1493. -/
theorem bounds_13_1493 : exactInterval 13 1493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1493 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1493) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1493 : oddCount 1493 13 = 3 ∧ acceleratedOrbit 13 1493 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1493 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1493) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1493.1, data_13_1493.2]

/-- Complete interval computation for depth 13, residue 1494. -/
theorem bounds_13_1494 : exactInterval 13 1494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1494 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1494) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1494 : oddCount 1494 13 = 7 ∧ acceleratedOrbit 13 1494 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1494 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1494) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1494.1, data_13_1494.2]

end Collatz.Research.StoppingAtlas.Batch0564
