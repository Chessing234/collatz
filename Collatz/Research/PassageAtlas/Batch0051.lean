import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0051

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1638. -/
theorem bounds_15_1638 : exactInterval 15 1638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1638 : oddCount 1638 15 = 6 ∧ acceleratedOrbit 15 1638 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1638) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1638.1, data_15_1638.2]

/-- Complete interval computation for depth 15, residue 1639. -/
theorem bounds_15_1639 : exactInterval 15 1639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1639 : oddCount 1639 15 = 11 ∧ acceleratedOrbit 15 1639 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1639) = 3 ^ 11 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1639.1, data_15_1639.2]

/-- Complete interval computation for depth 15, residue 1640. -/
theorem bounds_15_1640 : exactInterval 15 1640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1640 : oddCount 1640 15 = 5 ∧ acceleratedOrbit 15 1640 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1640) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1640.1, data_15_1640.2]

/-- Complete interval computation for depth 15, residue 1641. -/
theorem bounds_15_1641 : exactInterval 15 1641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1641 : oddCount 1641 15 = 8 ∧ acceleratedOrbit 15 1641 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1641) = 3 ^ 8 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1641.1, data_15_1641.2]

/-- Complete interval computation for depth 15, residue 1642. -/
theorem bounds_15_1642 : exactInterval 15 1642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1642 : oddCount 1642 15 = 5 ∧ acceleratedOrbit 15 1642 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1642) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1642.1, data_15_1642.2]

/-- Complete interval computation for depth 15, residue 1643. -/
theorem bounds_15_1643 : exactInterval 15 1643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1643 : oddCount 1643 15 = 9 ∧ acceleratedOrbit 15 1643 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1643) = 3 ^ 9 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1643.1, data_15_1643.2]

/-- Complete interval computation for depth 15, residue 1644. -/
theorem bounds_15_1644 : exactInterval 15 1644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1644 : oddCount 1644 15 = 9 ∧ acceleratedOrbit 15 1644 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1644) = 3 ^ 9 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1644.1, data_15_1644.2]

/-- Complete interval computation for depth 15, residue 1645. -/
theorem bounds_15_1645 : exactInterval 15 1645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1645 : oddCount 1645 15 = 9 ∧ acceleratedOrbit 15 1645 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1645) = 3 ^ 9 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1645.1, data_15_1645.2]

/-- Complete interval computation for depth 15, residue 1646. -/
theorem bounds_15_1646 : exactInterval 15 1646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1646 : oddCount 1646 15 = 9 ∧ acceleratedOrbit 15 1646 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1646) = 3 ^ 9 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1646.1, data_15_1646.2]

/-- Complete interval computation for depth 15, residue 1647. -/
theorem bounds_15_1647 : exactInterval 15 1647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1647 : oddCount 1647 15 = 7 ∧ acceleratedOrbit 15 1647 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1647) = 3 ^ 7 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1647.1, data_15_1647.2]

/-- Complete interval computation for depth 15, residue 1648. -/
theorem bounds_15_1648 : exactInterval 15 1648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1648 : oddCount 1648 15 = 8 ∧ acceleratedOrbit 15 1648 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1648) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1648.1, data_15_1648.2]

/-- Complete interval computation for depth 15, residue 1649. -/
theorem bounds_15_1649 : exactInterval 15 1649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1649 : oddCount 1649 15 = 5 ∧ acceleratedOrbit 15 1649 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1649) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1649.1, data_15_1649.2]

/-- Complete interval computation for depth 15, residue 1650. -/
theorem bounds_15_1650 : exactInterval 15 1650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1650 : oddCount 1650 15 = 8 ∧ acceleratedOrbit 15 1650 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1650) = 3 ^ 8 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1650.1, data_15_1650.2]

/-- Complete interval computation for depth 15, residue 1651. -/
theorem bounds_15_1651 : exactInterval 15 1651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1651 : oddCount 1651 15 = 8 ∧ acceleratedOrbit 15 1651 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1651) = 3 ^ 8 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1651.1, data_15_1651.2]

/-- Complete interval computation for depth 15, residue 1652. -/
theorem bounds_15_1652 : exactInterval 15 1652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1652 : oddCount 1652 15 = 8 ∧ acceleratedOrbit 15 1652 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1652) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1652.1, data_15_1652.2]

/-- Complete interval computation for depth 15, residue 1653. -/
theorem bounds_15_1653 : exactInterval 15 1653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1653 : oddCount 1653 15 = 8 ∧ acceleratedOrbit 15 1653 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1653) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1653.1, data_15_1653.2]

/-- Complete interval computation for depth 15, residue 1654. -/
theorem bounds_15_1654 : exactInterval 15 1654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1654 : oddCount 1654 15 = 6 ∧ acceleratedOrbit 15 1654 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1654) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1654.1, data_15_1654.2]

/-- Complete interval computation for depth 15, residue 1655. -/
theorem bounds_15_1655 : exactInterval 15 1655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1655 : oddCount 1655 15 = 6 ∧ acceleratedOrbit 15 1655 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1655) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1655.1, data_15_1655.2]

/-- Complete interval computation for depth 15, residue 1656. -/
theorem bounds_15_1656 : exactInterval 15 1656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1656 : oddCount 1656 15 = 8 ∧ acceleratedOrbit 15 1656 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1656) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1656.1, data_15_1656.2]

/-- Complete interval computation for depth 15, residue 1657. -/
theorem bounds_15_1657 : exactInterval 15 1657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1657 : oddCount 1657 15 = 9 ∧ acceleratedOrbit 15 1657 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1657) = 3 ^ 9 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1657.1, data_15_1657.2]

/-- Complete interval computation for depth 15, residue 1658. -/
theorem bounds_15_1658 : exactInterval 15 1658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1658 : oddCount 1658 15 = 8 ∧ acceleratedOrbit 15 1658 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1658) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1658.1, data_15_1658.2]

/-- Complete interval computation for depth 15, residue 1659. -/
theorem bounds_15_1659 : exactInterval 15 1659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1659 : oddCount 1659 15 = 6 ∧ acceleratedOrbit 15 1659 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1659) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1659.1, data_15_1659.2]

/-- Complete interval computation for depth 15, residue 1660. -/
theorem bounds_15_1660 : exactInterval 15 1660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1660 : oddCount 1660 15 = 9 ∧ acceleratedOrbit 15 1660 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1660) = 3 ^ 9 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1660.1, data_15_1660.2]

/-- Complete interval computation for depth 15, residue 1661. -/
theorem bounds_15_1661 : exactInterval 15 1661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1661 : oddCount 1661 15 = 9 ∧ acceleratedOrbit 15 1661 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1661) = 3 ^ 9 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1661.1, data_15_1661.2]

/-- Complete interval computation for depth 15, residue 1662. -/
theorem bounds_15_1662 : exactInterval 15 1662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1662 : oddCount 1662 15 = 9 ∧ acceleratedOrbit 15 1662 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1662) = 3 ^ 9 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1662.1, data_15_1662.2]

/-- Complete interval computation for depth 15, residue 1663. -/
theorem bounds_15_1663 : exactInterval 15 1663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1663 : oddCount 1663 15 = 11 ∧ acceleratedOrbit 15 1663 = 8996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1663) = 3 ^ 11 * m + 8996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1663.1, data_15_1663.2]

/-- Complete interval computation for depth 15, residue 1664. -/
theorem bounds_15_1664 : exactInterval 15 1664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1664 : oddCount 1664 15 = 3 ∧ acceleratedOrbit 15 1664 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1664) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1664.1, data_15_1664.2]

/-- Complete interval computation for depth 15, residue 1665. -/
theorem bounds_15_1665 : exactInterval 15 1665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1665 : oddCount 1665 15 = 10 ∧ acceleratedOrbit 15 1665 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1665) = 3 ^ 10 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1665.1, data_15_1665.2]

/-- Complete interval computation for depth 15, residue 1666. -/
theorem bounds_15_1666 : exactInterval 15 1666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1666 : oddCount 1666 15 = 5 ∧ acceleratedOrbit 15 1666 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1666) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1666.1, data_15_1666.2]

/-- Complete interval computation for depth 15, residue 1667. -/
theorem bounds_15_1667 : exactInterval 15 1667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1667 : oddCount 1667 15 = 5 ∧ acceleratedOrbit 15 1667 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1667) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1667.1, data_15_1667.2]

/-- Complete interval computation for depth 15, residue 1668. -/
theorem bounds_15_1668 : exactInterval 15 1668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1668 : oddCount 1668 15 = 8 ∧ acceleratedOrbit 15 1668 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1668) = 3 ^ 8 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1668.1, data_15_1668.2]

/-- Complete interval computation for depth 15, residue 1669. -/
theorem bounds_15_1669 : exactInterval 15 1669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1669 : oddCount 1669 15 = 8 ∧ acceleratedOrbit 15 1669 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1669) = 3 ^ 8 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1669.1, data_15_1669.2]

/-- Complete interval computation for depth 15, residue 1670. -/
theorem bounds_15_1670 : exactInterval 15 1670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1670 : oddCount 1670 15 = 8 ∧ acceleratedOrbit 15 1670 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1670) = 3 ^ 8 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1670.1, data_15_1670.2]

end Collatz.Research.PassageAtlas.Batch0051
