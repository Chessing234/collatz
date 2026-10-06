import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0046

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1474. -/
theorem bounds_15_1474 : exactInterval 15 1474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1474 : oddCount 1474 15 = 10 ∧ acceleratedOrbit 15 1474 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1474) = 3 ^ 10 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1474.1, data_15_1474.2]

/-- Complete interval computation for depth 15, residue 1475. -/
theorem bounds_15_1475 : exactInterval 15 1475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1475 : oddCount 1475 15 = 10 ∧ acceleratedOrbit 15 1475 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1475) = 3 ^ 10 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1475.1, data_15_1475.2]

/-- Complete interval computation for depth 15, residue 1476. -/
theorem bounds_15_1476 : exactInterval 15 1476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1476 : oddCount 1476 15 = 4 ∧ acceleratedOrbit 15 1476 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1476) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1476.1, data_15_1476.2]

/-- Complete interval computation for depth 15, residue 1477. -/
theorem bounds_15_1477 : exactInterval 15 1477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1477 : oddCount 1477 15 = 4 ∧ acceleratedOrbit 15 1477 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1477) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1477.1, data_15_1477.2]

/-- Complete interval computation for depth 15, residue 1478. -/
theorem bounds_15_1478 : exactInterval 15 1478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1478 : oddCount 1478 15 = 4 ∧ acceleratedOrbit 15 1478 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1478) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1478.1, data_15_1478.2]

/-- Complete interval computation for depth 15, residue 1479. -/
theorem bounds_15_1479 : exactInterval 15 1479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1479 : oddCount 1479 15 = 10 ∧ acceleratedOrbit 15 1479 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1479) = 3 ^ 10 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1479.1, data_15_1479.2]

/-- Complete interval computation for depth 15, residue 1480. -/
theorem bounds_15_1480 : exactInterval 15 1480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1480 : oddCount 1480 15 = 7 ∧ acceleratedOrbit 15 1480 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1480) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1480.1, data_15_1480.2]

/-- Complete interval computation for depth 15, residue 1481. -/
theorem bounds_15_1481 : exactInterval 15 1481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1481 : oddCount 1481 15 = 5 ∧ acceleratedOrbit 15 1481 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1481) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1481.1, data_15_1481.2]

/-- Complete interval computation for depth 15, residue 1482. -/
theorem bounds_15_1482 : exactInterval 15 1482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1482 : oddCount 1482 15 = 7 ∧ acceleratedOrbit 15 1482 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1482) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1482.1, data_15_1482.2]

/-- Complete interval computation for depth 15, residue 1483. -/
theorem bounds_15_1483 : exactInterval 15 1483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1483 : oddCount 1483 15 = 8 ∧ acceleratedOrbit 15 1483 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1483) = 3 ^ 8 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1483.1, data_15_1483.2]

/-- Complete interval computation for depth 15, residue 1484. -/
theorem bounds_15_1484 : exactInterval 15 1484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1484 : oddCount 1484 15 = 7 ∧ acceleratedOrbit 15 1484 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1484) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1484.1, data_15_1484.2]

/-- Complete interval computation for depth 15, residue 1485. -/
theorem bounds_15_1485 : exactInterval 15 1485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1485 : oddCount 1485 15 = 7 ∧ acceleratedOrbit 15 1485 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1485) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1485.1, data_15_1485.2]

/-- Complete interval computation for depth 15, residue 1486. -/
theorem bounds_15_1486 : exactInterval 15 1486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1486 : oddCount 1486 15 = 10 ∧ acceleratedOrbit 15 1486 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1486) = 3 ^ 10 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1486.1, data_15_1486.2]

/-- Complete interval computation for depth 15, residue 1487. -/
theorem bounds_15_1487 : exactInterval 15 1487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1487 : oddCount 1487 15 = 10 ∧ acceleratedOrbit 15 1487 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1487) = 3 ^ 10 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1487.1, data_15_1487.2]

/-- Complete interval computation for depth 15, residue 1488. -/
theorem bounds_15_1488 : exactInterval 15 1488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1488 : oddCount 1488 15 = 4 ∧ acceleratedOrbit 15 1488 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1488) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1488.1, data_15_1488.2]

/-- Complete interval computation for depth 15, residue 1489. -/
theorem bounds_15_1489 : exactInterval 15 1489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1489 : oddCount 1489 15 = 7 ∧ acceleratedOrbit 15 1489 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1489) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1489.1, data_15_1489.2]

/-- Complete interval computation for depth 15, residue 1490. -/
theorem bounds_15_1490 : exactInterval 15 1490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1490 : oddCount 1490 15 = 10 ∧ acceleratedOrbit 15 1490 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1490) = 3 ^ 10 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1490.1, data_15_1490.2]

/-- Complete interval computation for depth 15, residue 1491. -/
theorem bounds_15_1491 : exactInterval 15 1491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1491 : oddCount 1491 15 = 10 ∧ acceleratedOrbit 15 1491 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1491) = 3 ^ 10 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1491.1, data_15_1491.2]

/-- Complete interval computation for depth 15, residue 1492. -/
theorem bounds_15_1492 : exactInterval 15 1492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1492 : oddCount 1492 15 = 4 ∧ acceleratedOrbit 15 1492 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1492) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1492.1, data_15_1492.2]

/-- Complete interval computation for depth 15, residue 1493. -/
theorem bounds_15_1493 : exactInterval 15 1493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1493 : oddCount 1493 15 = 4 ∧ acceleratedOrbit 15 1493 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1493) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1493.1, data_15_1493.2]

/-- Complete interval computation for depth 15, residue 1494. -/
theorem bounds_15_1494 : exactInterval 15 1494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1494 : oddCount 1494 15 = 7 ∧ acceleratedOrbit 15 1494 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1494) = 3 ^ 7 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1494.1, data_15_1494.2]

/-- Complete interval computation for depth 15, residue 1495. -/
theorem bounds_15_1495 : exactInterval 15 1495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1495 : oddCount 1495 15 = 7 ∧ acceleratedOrbit 15 1495 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1495) = 3 ^ 7 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1495.1, data_15_1495.2]

/-- Complete interval computation for depth 15, residue 1496. -/
theorem bounds_15_1496 : exactInterval 15 1496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1496 : oddCount 1496 15 = 7 ∧ acceleratedOrbit 15 1496 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1496) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1496.1, data_15_1496.2]

/-- Complete interval computation for depth 15, residue 1497. -/
theorem bounds_15_1497 : exactInterval 15 1497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1497 : oddCount 1497 15 = 7 ∧ acceleratedOrbit 15 1497 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1497) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1497.1, data_15_1497.2]

/-- Complete interval computation for depth 15, residue 1498. -/
theorem bounds_15_1498 : exactInterval 15 1498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1498 : oddCount 1498 15 = 7 ∧ acceleratedOrbit 15 1498 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1498) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1498.1, data_15_1498.2]

/-- Complete interval computation for depth 15, residue 1499. -/
theorem bounds_15_1499 : exactInterval 15 1499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1499 : oddCount 1499 15 = 7 ∧ acceleratedOrbit 15 1499 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1499) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1499.1, data_15_1499.2]

/-- Complete interval computation for depth 15, residue 1500. -/
theorem bounds_15_1500 : exactInterval 15 1500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1500 : oddCount 1500 15 = 7 ∧ acceleratedOrbit 15 1500 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1500) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1500.1, data_15_1500.2]

/-- Complete interval computation for depth 15, residue 1501. -/
theorem bounds_15_1501 : exactInterval 15 1501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1501 : oddCount 1501 15 = 7 ∧ acceleratedOrbit 15 1501 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1501) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1501.1, data_15_1501.2]

/-- Complete interval computation for depth 15, residue 1502. -/
theorem bounds_15_1502 : exactInterval 15 1502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1502 : oddCount 1502 15 = 10 ∧ acceleratedOrbit 15 1502 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1502) = 3 ^ 10 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1502.1, data_15_1502.2]

/-- Complete interval computation for depth 15, residue 1503. -/
theorem bounds_15_1503 : exactInterval 15 1503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1503 : oddCount 1503 15 = 10 ∧ acceleratedOrbit 15 1503 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1503) = 3 ^ 10 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1503.1, data_15_1503.2]

/-- Complete interval computation for depth 15, residue 1504. -/
theorem bounds_15_1504 : exactInterval 15 1504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1504 : oddCount 1504 15 = 7 ∧ acceleratedOrbit 15 1504 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1504) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1504.1, data_15_1504.2]

/-- Complete interval computation for depth 15, residue 1505. -/
theorem bounds_15_1505 : exactInterval 15 1505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1505 : oddCount 1505 15 = 8 ∧ acceleratedOrbit 15 1505 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1505) = 3 ^ 8 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1505.1, data_15_1505.2]

/-- Complete interval computation for depth 15, residue 1506. -/
theorem bounds_15_1506 : exactInterval 15 1506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1506 : oddCount 1506 15 = 4 ∧ acceleratedOrbit 15 1506 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1506) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1506.1, data_15_1506.2]

end Collatz.Research.PassageAtlas.Batch0046
