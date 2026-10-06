import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0301

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1536. -/
theorem bounds_12_1536 : exactInterval 12 1536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1536 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1536) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1536 : oddCount 1536 12 = 2 ∧ acceleratedOrbit 12 1536 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1536 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1536) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1536.1, data_12_1536.2]

/-- Complete interval computation for depth 12, residue 1537. -/
theorem bounds_12_1537 : exactInterval 12 1537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1537 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1537) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1537 : oddCount 1537 12 = 7 ∧ acceleratedOrbit 12 1537 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1537 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1537) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1537.1, data_12_1537.2]

/-- Complete interval computation for depth 12, residue 1538. -/
theorem bounds_12_1538 : exactInterval 12 1538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1538 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1538) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1538 : oddCount 1538 12 = 5 ∧ acceleratedOrbit 12 1538 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1538 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1538) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1538.1, data_12_1538.2]

/-- Complete interval computation for depth 12, residue 1539. -/
theorem bounds_12_1539 : exactInterval 12 1539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1539 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1539) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1539 : oddCount 1539 12 = 5 ∧ acceleratedOrbit 12 1539 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1539 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1539) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1539.1, data_12_1539.2]

/-- Complete interval computation for depth 12, residue 1540. -/
theorem bounds_12_1540 : exactInterval 12 1540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1540 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1540) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1540 : oddCount 1540 12 = 5 ∧ acceleratedOrbit 12 1540 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1540 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1540) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1540.1, data_12_1540.2]

/-- Complete interval computation for depth 12, residue 1541. -/
theorem bounds_12_1541 : exactInterval 12 1541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1541 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1541) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1541 : oddCount 1541 12 = 5 ∧ acceleratedOrbit 12 1541 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1541 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1541) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1541.1, data_12_1541.2]

/-- Complete interval computation for depth 12, residue 1542. -/
theorem bounds_12_1542 : exactInterval 12 1542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1542 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1542) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1542 : oddCount 1542 12 = 5 ∧ acceleratedOrbit 12 1542 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1542 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1542) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1542.1, data_12_1542.2]

/-- Complete interval computation for depth 12, residue 1543. -/
theorem bounds_12_1543 : exactInterval 12 1543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1543 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1543) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1543 : oddCount 1543 12 = 6 ∧ acceleratedOrbit 12 1543 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1543 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1543) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1543.1, data_12_1543.2]

/-- Complete interval computation for depth 12, residue 1544. -/
theorem bounds_12_1544 : exactInterval 12 1544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1544 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1544) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1544 : oddCount 1544 12 = 4 ∧ acceleratedOrbit 12 1544 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1544 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1544) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1544.1, data_12_1544.2]

/-- Complete interval computation for depth 12, residue 1545. -/
theorem bounds_12_1545 : exactInterval 12 1545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1545 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1545) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1545 : oddCount 1545 12 = 7 ∧ acceleratedOrbit 12 1545 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1545 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1545) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1545.1, data_12_1545.2]

/-- Complete interval computation for depth 12, residue 1546. -/
theorem bounds_12_1546 : exactInterval 12 1546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1546 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1546) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1546 : oddCount 1546 12 = 4 ∧ acceleratedOrbit 12 1546 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1546 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1546) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1546.1, data_12_1546.2]

/-- Complete interval computation for depth 12, residue 1547. -/
theorem bounds_12_1547 : exactInterval 12 1547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1547 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1547) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1547 : oddCount 1547 12 = 5 ∧ acceleratedOrbit 12 1547 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1547 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1547) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1547.1, data_12_1547.2]

/-- Complete interval computation for depth 12, residue 1548. -/
theorem bounds_12_1548 : exactInterval 12 1548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1548 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1548) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1548 : oddCount 1548 12 = 4 ∧ acceleratedOrbit 12 1548 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1548 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1548) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1548.1, data_12_1548.2]

/-- Complete interval computation for depth 12, residue 1549. -/
theorem bounds_12_1549 : exactInterval 12 1549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1549 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1549) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1549 : oddCount 1549 12 = 4 ∧ acceleratedOrbit 12 1549 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1549 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1549) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1549.1, data_12_1549.2]

/-- Complete interval computation for depth 12, residue 1550. -/
theorem bounds_12_1550 : exactInterval 12 1550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1550 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1550) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1550 : oddCount 1550 12 = 7 ∧ acceleratedOrbit 12 1550 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1550 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1550) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1550.1, data_12_1550.2]

end Collatz.Research.StoppingAtlas.Batch0301
