import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0574

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1633. -/
theorem bounds_13_1633 : exactInterval 13 1633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1633 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1633) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1633 : oddCount 1633 13 = 6 ∧ acceleratedOrbit 13 1633 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1633 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1633) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1633.1, data_13_1633.2]

/-- Complete interval computation for depth 13, residue 1634. -/
theorem bounds_13_1634 : exactInterval 13 1634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1634 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1634) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1634 : oddCount 1634 13 = 5 ∧ acceleratedOrbit 13 1634 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1634 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1634) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1634.1, data_13_1634.2]

/-- Complete interval computation for depth 13, residue 1635. -/
theorem bounds_13_1635 : exactInterval 13 1635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1635 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1635) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1635 : oddCount 1635 13 = 5 ∧ acceleratedOrbit 13 1635 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1635 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1635) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1635.1, data_13_1635.2]

/-- Complete interval computation for depth 13, residue 1636. -/
theorem bounds_13_1636 : exactInterval 13 1636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1636 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1636) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1636 : oddCount 1636 13 = 5 ∧ acceleratedOrbit 13 1636 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1636 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1636) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1636.1, data_13_1636.2]

/-- Complete interval computation for depth 13, residue 1637. -/
theorem bounds_13_1637 : exactInterval 13 1637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1637 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1637) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1637 : oddCount 1637 13 = 5 ∧ acceleratedOrbit 13 1637 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1637 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1637) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1637.1, data_13_1637.2]

/-- Complete interval computation for depth 13, residue 1638. -/
theorem bounds_13_1638 : exactInterval 13 1638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1638 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1638) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1638 : oddCount 1638 13 = 5 ∧ acceleratedOrbit 13 1638 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1638 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1638) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1638.1, data_13_1638.2]

/-- Complete interval computation for depth 13, residue 1639. -/
theorem bounds_13_1639 : exactInterval 13 1639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1639 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1639) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1639 : oddCount 1639 13 = 10 ∧ acceleratedOrbit 13 1639 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1639 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1639) = 3 ^ 10 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1639.1, data_13_1639.2]

/-- Complete interval computation for depth 13, residue 1640. -/
theorem bounds_13_1640 : exactInterval 13 1640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1640 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1640) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1640 : oddCount 1640 13 = 4 ∧ acceleratedOrbit 13 1640 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1640 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1640) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1640.1, data_13_1640.2]

/-- Complete interval computation for depth 13, residue 1641. -/
theorem bounds_13_1641 : exactInterval 13 1641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1641 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1641) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1641 : oddCount 1641 13 = 8 ∧ acceleratedOrbit 13 1641 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1641 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1641) = 3 ^ 8 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1641.1, data_13_1641.2]

/-- Complete interval computation for depth 13, residue 1642. -/
theorem bounds_13_1642 : exactInterval 13 1642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1642 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1642) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1642 : oddCount 1642 13 = 4 ∧ acceleratedOrbit 13 1642 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1642 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1642) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1642.1, data_13_1642.2]

/-- Complete interval computation for depth 13, residue 1643. -/
theorem bounds_13_1643 : exactInterval 13 1643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1643 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1643) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1643 : oddCount 1643 13 = 8 ∧ acceleratedOrbit 13 1643 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1643 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1643) = 3 ^ 8 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1643.1, data_13_1643.2]

/-- Complete interval computation for depth 13, residue 1644. -/
theorem bounds_13_1644 : exactInterval 13 1644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1644 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1644) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1644 : oddCount 1644 13 = 8 ∧ acceleratedOrbit 13 1644 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1644 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1644) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1644.1, data_13_1644.2]

/-- Complete interval computation for depth 13, residue 1645. -/
theorem bounds_13_1645 : exactInterval 13 1645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1645 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1645) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1645 : oddCount 1645 13 = 8 ∧ acceleratedOrbit 13 1645 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1645 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1645) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1645.1, data_13_1645.2]

/-- Complete interval computation for depth 13, residue 1646. -/
theorem bounds_13_1646 : exactInterval 13 1646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1646 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1646) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1646 : oddCount 1646 13 = 8 ∧ acceleratedOrbit 13 1646 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1646 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1646) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1646.1, data_13_1646.2]

/-- Complete interval computation for depth 13, residue 1647. -/
theorem bounds_13_1647 : exactInterval 13 1647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1647 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1647) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1647 : oddCount 1647 13 = 7 ∧ acceleratedOrbit 13 1647 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1647 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1647) = 3 ^ 7 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1647.1, data_13_1647.2]

end Collatz.Research.StoppingAtlas.Batch0574
