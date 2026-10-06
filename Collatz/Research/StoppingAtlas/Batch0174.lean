import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0174

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1633. -/
theorem bounds_11_1633 : exactInterval 11 1633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1633 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1633) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1633 : oddCount 1633 11 = 5 ∧ acceleratedOrbit 11 1633 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1633 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1633) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1633.1, data_11_1633.2]

/-- Complete interval computation for depth 11, residue 1634. -/
theorem bounds_11_1634 : exactInterval 11 1634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1634 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1634) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1634 : oddCount 1634 11 = 4 ∧ acceleratedOrbit 11 1634 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1634 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1634) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1634.1, data_11_1634.2]

/-- Complete interval computation for depth 11, residue 1635. -/
theorem bounds_11_1635 : exactInterval 11 1635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1635 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1635) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1635 : oddCount 1635 11 = 4 ∧ acceleratedOrbit 11 1635 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1635 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1635) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1635.1, data_11_1635.2]

/-- Complete interval computation for depth 11, residue 1636. -/
theorem bounds_11_1636 : exactInterval 11 1636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1636 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1636) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1636 : oddCount 1636 11 = 4 ∧ acceleratedOrbit 11 1636 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1636 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1636) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1636.1, data_11_1636.2]

/-- Complete interval computation for depth 11, residue 1637. -/
theorem bounds_11_1637 : exactInterval 11 1637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1637 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1637) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1637 : oddCount 1637 11 = 4 ∧ acceleratedOrbit 11 1637 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1637 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1637) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1637.1, data_11_1637.2]

/-- Complete interval computation for depth 11, residue 1638. -/
theorem bounds_11_1638 : exactInterval 11 1638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1638 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1638) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1638 : oddCount 1638 11 = 4 ∧ acceleratedOrbit 11 1638 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1638 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1638) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1638.1, data_11_1638.2]

/-- Complete interval computation for depth 11, residue 1639. -/
theorem bounds_11_1639 : exactInterval 11 1639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1639 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1639) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1639 : oddCount 1639 11 = 8 ∧ acceleratedOrbit 11 1639 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1639 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1639) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1639.1, data_11_1639.2]

/-- Complete interval computation for depth 11, residue 1640. -/
theorem bounds_11_1640 : exactInterval 11 1640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1640 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1640) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1640 : oddCount 1640 11 = 3 ∧ acceleratedOrbit 11 1640 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1640 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1640) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1640.1, data_11_1640.2]

/-- Complete interval computation for depth 11, residue 1641. -/
theorem bounds_11_1641 : exactInterval 11 1641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1641 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1641) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1641 : oddCount 1641 11 = 8 ∧ acceleratedOrbit 11 1641 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1641 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1641) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1641.1, data_11_1641.2]

/-- Complete interval computation for depth 11, residue 1642. -/
theorem bounds_11_1642 : exactInterval 11 1642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1642 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1642) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1642 : oddCount 1642 11 = 3 ∧ acceleratedOrbit 11 1642 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1642 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1642) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1642.1, data_11_1642.2]

/-- Complete interval computation for depth 11, residue 1643. -/
theorem bounds_11_1643 : exactInterval 11 1643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1643 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1643) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1643 : oddCount 1643 11 = 7 ∧ acceleratedOrbit 11 1643 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1643 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1643) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1643.1, data_11_1643.2]

/-- Complete interval computation for depth 11, residue 1644. -/
theorem bounds_11_1644 : exactInterval 11 1644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1644 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1644) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1644 : oddCount 1644 11 = 6 ∧ acceleratedOrbit 11 1644 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1644 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1644) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1644.1, data_11_1644.2]

/-- Complete interval computation for depth 11, residue 1645. -/
theorem bounds_11_1645 : exactInterval 11 1645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1645 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1645) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1645 : oddCount 1645 11 = 6 ∧ acceleratedOrbit 11 1645 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1645 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1645) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1645.1, data_11_1645.2]

/-- Complete interval computation for depth 11, residue 1646. -/
theorem bounds_11_1646 : exactInterval 11 1646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1646 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1646) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1646 : oddCount 1646 11 = 6 ∧ acceleratedOrbit 11 1646 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1646 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1646) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1646.1, data_11_1646.2]

/-- Complete interval computation for depth 11, residue 1647. -/
theorem bounds_11_1647 : exactInterval 11 1647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1647 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1647) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1647 : oddCount 1647 11 = 7 ∧ acceleratedOrbit 11 1647 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1647 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1647) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1647.1, data_11_1647.2]

end Collatz.Research.StoppingAtlas.Batch0174
