import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0568

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1541. -/
theorem bounds_13_1541 : exactInterval 13 1541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1541 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1541) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1541 : oddCount 1541 13 = 5 ∧ acceleratedOrbit 13 1541 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1541 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1541) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1541.1, data_13_1541.2]

/-- Complete interval computation for depth 13, residue 1542. -/
theorem bounds_13_1542 : exactInterval 13 1542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1542 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1542) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1542 : oddCount 1542 13 = 5 ∧ acceleratedOrbit 13 1542 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1542 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1542) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1542.1, data_13_1542.2]

/-- Complete interval computation for depth 13, residue 1543. -/
theorem bounds_13_1543 : exactInterval 13 1543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1543 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1543) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1543 : oddCount 1543 13 = 7 ∧ acceleratedOrbit 13 1543 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1543 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1543) = 3 ^ 7 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1543.1, data_13_1543.2]

/-- Complete interval computation for depth 13, residue 1544. -/
theorem bounds_13_1544 : exactInterval 13 1544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1544 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1544) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1544 : oddCount 1544 13 = 5 ∧ acceleratedOrbit 13 1544 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1544 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1544) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1544.1, data_13_1544.2]

/-- Complete interval computation for depth 13, residue 1545. -/
theorem bounds_13_1545 : exactInterval 13 1545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1545 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1545) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1545 : oddCount 1545 13 = 8 ∧ acceleratedOrbit 13 1545 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1545 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1545) = 3 ^ 8 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1545.1, data_13_1545.2]

/-- Complete interval computation for depth 13, residue 1546. -/
theorem bounds_13_1546 : exactInterval 13 1546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1546 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1546) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1546 : oddCount 1546 13 = 5 ∧ acceleratedOrbit 13 1546 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1546 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1546) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1546.1, data_13_1546.2]

/-- Complete interval computation for depth 13, residue 1547. -/
theorem bounds_13_1547 : exactInterval 13 1547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1547 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1547) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1547 : oddCount 1547 13 = 5 ∧ acceleratedOrbit 13 1547 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1547 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1547) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1547.1, data_13_1547.2]

/-- Complete interval computation for depth 13, residue 1548. -/
theorem bounds_13_1548 : exactInterval 13 1548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1548 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1548) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1548 : oddCount 1548 13 = 5 ∧ acceleratedOrbit 13 1548 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1548 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1548) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1548.1, data_13_1548.2]

/-- Complete interval computation for depth 13, residue 1549. -/
theorem bounds_13_1549 : exactInterval 13 1549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1549 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1549) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1549 : oddCount 1549 13 = 5 ∧ acceleratedOrbit 13 1549 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1549 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1549) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1549.1, data_13_1549.2]

/-- Complete interval computation for depth 13, residue 1550. -/
theorem bounds_13_1550 : exactInterval 13 1550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1550 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1550) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1550 : oddCount 1550 13 = 7 ∧ acceleratedOrbit 13 1550 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1550 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1550) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1550.1, data_13_1550.2]

/-- Complete interval computation for depth 13, residue 1551. -/
theorem bounds_13_1551 : exactInterval 13 1551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1551 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1551) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1551 : oddCount 1551 13 = 7 ∧ acceleratedOrbit 13 1551 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1551 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1551) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1551.1, data_13_1551.2]

/-- Complete interval computation for depth 13, residue 1552. -/
theorem bounds_13_1552 : exactInterval 13 1552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1552 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1552) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1552 : oddCount 1552 13 = 5 ∧ acceleratedOrbit 13 1552 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1552 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1552) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1552.1, data_13_1552.2]

/-- Complete interval computation for depth 13, residue 1553. -/
theorem bounds_13_1553 : exactInterval 13 1553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1553 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1553) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1553 : oddCount 1553 13 = 5 ∧ acceleratedOrbit 13 1553 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1553 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1553) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1553.1, data_13_1553.2]

/-- Complete interval computation for depth 13, residue 1554. -/
theorem bounds_13_1554 : exactInterval 13 1554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1554 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1554) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1554 : oddCount 1554 13 = 7 ∧ acceleratedOrbit 13 1554 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1554 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1554) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1554.1, data_13_1554.2]

/-- Complete interval computation for depth 13, residue 1555. -/
theorem bounds_13_1555 : exactInterval 13 1555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1555 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1555) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1555 : oddCount 1555 13 = 7 ∧ acceleratedOrbit 13 1555 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1555 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1555) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1555.1, data_13_1555.2]

end Collatz.Research.StoppingAtlas.Batch0568
