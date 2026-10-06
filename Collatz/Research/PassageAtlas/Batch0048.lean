import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0048

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1540. -/
theorem bounds_15_1540 : exactInterval 15 1540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1540 : oddCount 1540 15 = 6 ∧ acceleratedOrbit 15 1540 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1540) = 3 ^ 6 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1540.1, data_15_1540.2]

/-- Complete interval computation for depth 15, residue 1541. -/
theorem bounds_15_1541 : exactInterval 15 1541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1541 : oddCount 1541 15 = 6 ∧ acceleratedOrbit 15 1541 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1541) = 3 ^ 6 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1541.1, data_15_1541.2]

/-- Complete interval computation for depth 15, residue 1542. -/
theorem bounds_15_1542 : exactInterval 15 1542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1542 : oddCount 1542 15 = 6 ∧ acceleratedOrbit 15 1542 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1542) = 3 ^ 6 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1542.1, data_15_1542.2]

/-- Complete interval computation for depth 15, residue 1543. -/
theorem bounds_15_1543 : exactInterval 15 1543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1543 : oddCount 1543 15 = 8 ∧ acceleratedOrbit 15 1543 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1543) = 3 ^ 8 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1543.1, data_15_1543.2]

/-- Complete interval computation for depth 15, residue 1544. -/
theorem bounds_15_1544 : exactInterval 15 1544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1544 : oddCount 1544 15 = 7 ∧ acceleratedOrbit 15 1544 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1544) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1544.1, data_15_1544.2]

/-- Complete interval computation for depth 15, residue 1545. -/
theorem bounds_15_1545 : exactInterval 15 1545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1545 : oddCount 1545 15 = 9 ∧ acceleratedOrbit 15 1545 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1545) = 3 ^ 9 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1545.1, data_15_1545.2]

/-- Complete interval computation for depth 15, residue 1546. -/
theorem bounds_15_1546 : exactInterval 15 1546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1546 : oddCount 1546 15 = 7 ∧ acceleratedOrbit 15 1546 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1546) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1546.1, data_15_1546.2]

/-- Complete interval computation for depth 15, residue 1547. -/
theorem bounds_15_1547 : exactInterval 15 1547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1547 : oddCount 1547 15 = 6 ∧ acceleratedOrbit 15 1547 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1547) = 3 ^ 6 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1547.1, data_15_1547.2]

/-- Complete interval computation for depth 15, residue 1548. -/
theorem bounds_15_1548 : exactInterval 15 1548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1548 : oddCount 1548 15 = 7 ∧ acceleratedOrbit 15 1548 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1548) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1548.1, data_15_1548.2]

/-- Complete interval computation for depth 15, residue 1549. -/
theorem bounds_15_1549 : exactInterval 15 1549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1549 : oddCount 1549 15 = 7 ∧ acceleratedOrbit 15 1549 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1549) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1549.1, data_15_1549.2]

/-- Complete interval computation for depth 15, residue 1550. -/
theorem bounds_15_1550 : exactInterval 15 1550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1550 : oddCount 1550 15 = 9 ∧ acceleratedOrbit 15 1550 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1550) = 3 ^ 9 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1550.1, data_15_1550.2]

/-- Complete interval computation for depth 15, residue 1551. -/
theorem bounds_15_1551 : exactInterval 15 1551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1551 : oddCount 1551 15 = 9 ∧ acceleratedOrbit 15 1551 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1551) = 3 ^ 9 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1551.1, data_15_1551.2]

/-- Complete interval computation for depth 15, residue 1552. -/
theorem bounds_15_1552 : exactInterval 15 1552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1552 : oddCount 1552 15 = 7 ∧ acceleratedOrbit 15 1552 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1552) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1552.1, data_15_1552.2]

/-- Complete interval computation for depth 15, residue 1553. -/
theorem bounds_15_1553 : exactInterval 15 1553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1553 : oddCount 1553 15 = 7 ∧ acceleratedOrbit 15 1553 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1553) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1553.1, data_15_1553.2]

/-- Complete interval computation for depth 15, residue 1554. -/
theorem bounds_15_1554 : exactInterval 15 1554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1554 : oddCount 1554 15 = 7 ∧ acceleratedOrbit 15 1554 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1554) = 3 ^ 7 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1554.1, data_15_1554.2]

/-- Complete interval computation for depth 15, residue 1555. -/
theorem bounds_15_1555 : exactInterval 15 1555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1555 : oddCount 1555 15 = 7 ∧ acceleratedOrbit 15 1555 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1555) = 3 ^ 7 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1555.1, data_15_1555.2]

/-- Complete interval computation for depth 15, residue 1556. -/
theorem bounds_15_1556 : exactInterval 15 1556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1556 : oddCount 1556 15 = 7 ∧ acceleratedOrbit 15 1556 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1556) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1556.1, data_15_1556.2]

/-- Complete interval computation for depth 15, residue 1557. -/
theorem bounds_15_1557 : exactInterval 15 1557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1557 : oddCount 1557 15 = 7 ∧ acceleratedOrbit 15 1557 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1557) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1557.1, data_15_1557.2]

/-- Complete interval computation for depth 15, residue 1558. -/
theorem bounds_15_1558 : exactInterval 15 1558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1558 : oddCount 1558 15 = 8 ∧ acceleratedOrbit 15 1558 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1558) = 3 ^ 8 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1558.1, data_15_1558.2]

/-- Complete interval computation for depth 15, residue 1559. -/
theorem bounds_15_1559 : exactInterval 15 1559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1559 : oddCount 1559 15 = 8 ∧ acceleratedOrbit 15 1559 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1559) = 3 ^ 8 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1559.1, data_15_1559.2]

/-- Complete interval computation for depth 15, residue 1560. -/
theorem bounds_15_1560 : exactInterval 15 1560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1560 : oddCount 1560 15 = 7 ∧ acceleratedOrbit 15 1560 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1560) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1560.1, data_15_1560.2]

/-- Complete interval computation for depth 15, residue 1561. -/
theorem bounds_15_1561 : exactInterval 15 1561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1561 : oddCount 1561 15 = 8 ∧ acceleratedOrbit 15 1561 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1561) = 3 ^ 8 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1561.1, data_15_1561.2]

/-- Complete interval computation for depth 15, residue 1562. -/
theorem bounds_15_1562 : exactInterval 15 1562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1562 : oddCount 1562 15 = 7 ∧ acceleratedOrbit 15 1562 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1562) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1562.1, data_15_1562.2]

/-- Complete interval computation for depth 15, residue 1563. -/
theorem bounds_15_1563 : exactInterval 15 1563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1563 : oddCount 1563 15 = 9 ∧ acceleratedOrbit 15 1563 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1563) = 3 ^ 9 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1563.1, data_15_1563.2]

/-- Complete interval computation for depth 15, residue 1564. -/
theorem bounds_15_1564 : exactInterval 15 1564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1564 : oddCount 1564 15 = 7 ∧ acceleratedOrbit 15 1564 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1564) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1564.1, data_15_1564.2]

/-- Complete interval computation for depth 15, residue 1565. -/
theorem bounds_15_1565 : exactInterval 15 1565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1565 : oddCount 1565 15 = 7 ∧ acceleratedOrbit 15 1565 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1565) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1565.1, data_15_1565.2]

/-- Complete interval computation for depth 15, residue 1566. -/
theorem bounds_15_1566 : exactInterval 15 1566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1566 : oddCount 1566 15 = 7 ∧ acceleratedOrbit 15 1566 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1566) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1566.1, data_15_1566.2]

/-- Complete interval computation for depth 15, residue 1567. -/
theorem bounds_15_1567 : exactInterval 15 1567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1567 : oddCount 1567 15 = 8 ∧ acceleratedOrbit 15 1567 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1567) = 3 ^ 8 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1567.1, data_15_1567.2]

/-- Complete interval computation for depth 15, residue 1568. -/
theorem bounds_15_1568 : exactInterval 15 1568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1568 : oddCount 1568 15 = 5 ∧ acceleratedOrbit 15 1568 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1568) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1568.1, data_15_1568.2]

/-- Complete interval computation for depth 15, residue 1569. -/
theorem bounds_15_1569 : exactInterval 15 1569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1569 : oddCount 1569 15 = 6 ∧ acceleratedOrbit 15 1569 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1569) = 3 ^ 6 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1569.1, data_15_1569.2]

/-- Complete interval computation for depth 15, residue 1570. -/
theorem bounds_15_1570 : exactInterval 15 1570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1570 : oddCount 1570 15 = 7 ∧ acceleratedOrbit 15 1570 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1570) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1570.1, data_15_1570.2]

/-- Complete interval computation for depth 15, residue 1571. -/
theorem bounds_15_1571 : exactInterval 15 1571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1571 : oddCount 1571 15 = 7 ∧ acceleratedOrbit 15 1571 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1571) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1571.1, data_15_1571.2]

end Collatz.Research.PassageAtlas.Batch0048
