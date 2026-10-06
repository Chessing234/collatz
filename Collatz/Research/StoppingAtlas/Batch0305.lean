import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0305

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1597. -/
theorem bounds_12_1597 : exactInterval 12 1597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1597 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1597) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1597 : oddCount 1597 12 = 5 ∧ acceleratedOrbit 12 1597 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1597 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1597) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1597.1, data_12_1597.2]

/-- Complete interval computation for depth 12, residue 1598. -/
theorem bounds_12_1598 : exactInterval 12 1598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1598 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1598) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1598 : oddCount 1598 12 = 8 ∧ acceleratedOrbit 12 1598 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1598 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1598) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1598.1, data_12_1598.2]

/-- Complete interval computation for depth 12, residue 1599. -/
theorem bounds_12_1599 : exactInterval 12 1599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1599 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1599) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1599 : oddCount 1599 12 = 8 ∧ acceleratedOrbit 12 1599 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1599 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1599) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1599.1, data_12_1599.2]

/-- Complete interval computation for depth 12, residue 1600. -/
theorem bounds_12_1600 : exactInterval 12 1600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1600 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1600) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1600 : oddCount 1600 12 = 3 ∧ acceleratedOrbit 12 1600 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1600 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1600) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1600.1, data_12_1600.2]

/-- Complete interval computation for depth 12, residue 1601. -/
theorem bounds_12_1601 : exactInterval 12 1601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1601 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1601) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1601 : oddCount 1601 12 = 6 ∧ acceleratedOrbit 12 1601 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1601 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1601) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1601.1, data_12_1601.2]

/-- Complete interval computation for depth 12, residue 1602. -/
theorem bounds_12_1602 : exactInterval 12 1602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1602 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1602) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1602 : oddCount 1602 12 = 6 ∧ acceleratedOrbit 12 1602 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1602 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1602) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1602.1, data_12_1602.2]

/-- Complete interval computation for depth 12, residue 1603. -/
theorem bounds_12_1603 : exactInterval 12 1603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1603 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1603) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1603 : oddCount 1603 12 = 6 ∧ acceleratedOrbit 12 1603 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1603 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1603) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1603.1, data_12_1603.2]

/-- Complete interval computation for depth 12, residue 1604. -/
theorem bounds_12_1604 : exactInterval 12 1604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1604 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1604) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1604 : oddCount 1604 12 = 4 ∧ acceleratedOrbit 12 1604 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1604 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1604) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1604.1, data_12_1604.2]

/-- Complete interval computation for depth 12, residue 1605. -/
theorem bounds_12_1605 : exactInterval 12 1605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1605 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1605) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1605 : oddCount 1605 12 = 4 ∧ acceleratedOrbit 12 1605 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1605 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1605) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1605.1, data_12_1605.2]

/-- Complete interval computation for depth 12, residue 1606. -/
theorem bounds_12_1606 : exactInterval 12 1606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1606 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1606) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1606 : oddCount 1606 12 = 4 ∧ acceleratedOrbit 12 1606 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1606 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1606) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1606.1, data_12_1606.2]

/-- Complete interval computation for depth 12, residue 1607. -/
theorem bounds_12_1607 : exactInterval 12 1607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1607 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1607) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1607 : oddCount 1607 12 = 7 ∧ acceleratedOrbit 12 1607 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1607 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1607) = 3 ^ 7 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1607.1, data_12_1607.2]

/-- Complete interval computation for depth 12, residue 1608. -/
theorem bounds_12_1608 : exactInterval 12 1608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1608 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1608) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1608 : oddCount 1608 12 = 4 ∧ acceleratedOrbit 12 1608 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1608 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1608) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1608.1, data_12_1608.2]

/-- Complete interval computation for depth 12, residue 1609. -/
theorem bounds_12_1609 : exactInterval 12 1609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1609 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1609) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1609 : oddCount 1609 12 = 8 ∧ acceleratedOrbit 12 1609 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1609 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1609) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1609.1, data_12_1609.2]

/-- Complete interval computation for depth 12, residue 1610. -/
theorem bounds_12_1610 : exactInterval 12 1610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1610 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1610) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1610 : oddCount 1610 12 = 4 ∧ acceleratedOrbit 12 1610 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1610 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1610) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1610.1, data_12_1610.2]

/-- Complete interval computation for depth 12, residue 1611. -/
theorem bounds_12_1611 : exactInterval 12 1611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1611 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1611) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1611 : oddCount 1611 12 = 4 ∧ acceleratedOrbit 12 1611 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1611 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1611) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1611.1, data_12_1611.2]

end Collatz.Research.StoppingAtlas.Batch0305
