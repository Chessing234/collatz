import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0168

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1541. -/
theorem bounds_11_1541 : exactInterval 11 1541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1541 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1541) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1541 : oddCount 1541 11 = 5 ∧ acceleratedOrbit 11 1541 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1541 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1541) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1541.1, data_11_1541.2]

/-- Complete interval computation for depth 11, residue 1542. -/
theorem bounds_11_1542 : exactInterval 11 1542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1542 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1542) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1542 : oddCount 1542 11 = 5 ∧ acceleratedOrbit 11 1542 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1542 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1542) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1542.1, data_11_1542.2]

/-- Complete interval computation for depth 11, residue 1543. -/
theorem bounds_11_1543 : exactInterval 11 1543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1543 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1543) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1543 : oddCount 1543 11 = 6 ∧ acceleratedOrbit 11 1543 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1543 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1543) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1543.1, data_11_1543.2]

/-- Complete interval computation for depth 11, residue 1544. -/
theorem bounds_11_1544 : exactInterval 11 1544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1544 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1544) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1544 : oddCount 1544 11 = 4 ∧ acceleratedOrbit 11 1544 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1544 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1544) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1544.1, data_11_1544.2]

/-- Complete interval computation for depth 11, residue 1545. -/
theorem bounds_11_1545 : exactInterval 11 1545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1545 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1545) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1545 : oddCount 1545 11 = 6 ∧ acceleratedOrbit 11 1545 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1545 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1545) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1545.1, data_11_1545.2]

/-- Complete interval computation for depth 11, residue 1546. -/
theorem bounds_11_1546 : exactInterval 11 1546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1546 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1546) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1546 : oddCount 1546 11 = 4 ∧ acceleratedOrbit 11 1546 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1546 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1546) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1546.1, data_11_1546.2]

/-- Complete interval computation for depth 11, residue 1547. -/
theorem bounds_11_1547 : exactInterval 11 1547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1547 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1547) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1547 : oddCount 1547 11 = 5 ∧ acceleratedOrbit 11 1547 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1547 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1547) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1547.1, data_11_1547.2]

/-- Complete interval computation for depth 11, residue 1548. -/
theorem bounds_11_1548 : exactInterval 11 1548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1548 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1548) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1548 : oddCount 1548 11 = 4 ∧ acceleratedOrbit 11 1548 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1548 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1548) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1548.1, data_11_1548.2]

/-- Complete interval computation for depth 11, residue 1549. -/
theorem bounds_11_1549 : exactInterval 11 1549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1549 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1549) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1549 : oddCount 1549 11 = 4 ∧ acceleratedOrbit 11 1549 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1549 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1549) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1549.1, data_11_1549.2]

/-- Complete interval computation for depth 11, residue 1550. -/
theorem bounds_11_1550 : exactInterval 11 1550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1550 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1550) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1550 : oddCount 1550 11 = 6 ∧ acceleratedOrbit 11 1550 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1550 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1550) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1550.1, data_11_1550.2]

/-- Complete interval computation for depth 11, residue 1551. -/
theorem bounds_11_1551 : exactInterval 11 1551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1551 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1551) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1551 : oddCount 1551 11 = 6 ∧ acceleratedOrbit 11 1551 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1551 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1551) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1551.1, data_11_1551.2]

/-- Complete interval computation for depth 11, residue 1552. -/
theorem bounds_11_1552 : exactInterval 11 1552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1552 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1552) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1552 : oddCount 1552 11 = 5 ∧ acceleratedOrbit 11 1552 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1552 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1552) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1552.1, data_11_1552.2]

/-- Complete interval computation for depth 11, residue 1553. -/
theorem bounds_11_1553 : exactInterval 11 1553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1553 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1553) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1553 : oddCount 1553 11 = 4 ∧ acceleratedOrbit 11 1553 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1553 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1553) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1553.1, data_11_1553.2]

/-- Complete interval computation for depth 11, residue 1554. -/
theorem bounds_11_1554 : exactInterval 11 1554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1554 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1554) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1554 : oddCount 1554 11 = 7 ∧ acceleratedOrbit 11 1554 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1554 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1554) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1554.1, data_11_1554.2]

/-- Complete interval computation for depth 11, residue 1555. -/
theorem bounds_11_1555 : exactInterval 11 1555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1555 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1555) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1555 : oddCount 1555 11 = 7 ∧ acceleratedOrbit 11 1555 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1555 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1555) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1555.1, data_11_1555.2]

end Collatz.Research.StoppingAtlas.Batch0168
