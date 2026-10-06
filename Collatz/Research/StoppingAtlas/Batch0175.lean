import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0175

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1648. -/
theorem bounds_11_1648 : exactInterval 11 1648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1648 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1648) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1648 : oddCount 1648 11 = 6 ∧ acceleratedOrbit 11 1648 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1648 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1648) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1648.1, data_11_1648.2]

/-- Complete interval computation for depth 11, residue 1649. -/
theorem bounds_11_1649 : exactInterval 11 1649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1649 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1649) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1649 : oddCount 1649 11 = 3 ∧ acceleratedOrbit 11 1649 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1649 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1649) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1649.1, data_11_1649.2]

/-- Complete interval computation for depth 11, residue 1650. -/
theorem bounds_11_1650 : exactInterval 11 1650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1650 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1650) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1650 : oddCount 1650 11 = 6 ∧ acceleratedOrbit 11 1650 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1650 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1650) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1650.1, data_11_1650.2]

/-- Complete interval computation for depth 11, residue 1651. -/
theorem bounds_11_1651 : exactInterval 11 1651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1651 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1651) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1651 : oddCount 1651 11 = 6 ∧ acceleratedOrbit 11 1651 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1651 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1651) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1651.1, data_11_1651.2]

/-- Complete interval computation for depth 11, residue 1652. -/
theorem bounds_11_1652 : exactInterval 11 1652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1652 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1652) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1652 : oddCount 1652 11 = 6 ∧ acceleratedOrbit 11 1652 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1652 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1652) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1652.1, data_11_1652.2]

/-- Complete interval computation for depth 11, residue 1653. -/
theorem bounds_11_1653 : exactInterval 11 1653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1653 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1653) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1653 : oddCount 1653 11 = 6 ∧ acceleratedOrbit 11 1653 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1653 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1653) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1653.1, data_11_1653.2]

/-- Complete interval computation for depth 11, residue 1654. -/
theorem bounds_11_1654 : exactInterval 11 1654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1654 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1654) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1654 : oddCount 1654 11 = 5 ∧ acceleratedOrbit 11 1654 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1654 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1654) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1654.1, data_11_1654.2]

/-- Complete interval computation for depth 11, residue 1655. -/
theorem bounds_11_1655 : exactInterval 11 1655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1655 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1655) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1655 : oddCount 1655 11 = 5 ∧ acceleratedOrbit 11 1655 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1655 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1655) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1655.1, data_11_1655.2]

/-- Complete interval computation for depth 11, residue 1656. -/
theorem bounds_11_1656 : exactInterval 11 1656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1656 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1656) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1656 : oddCount 1656 11 = 6 ∧ acceleratedOrbit 11 1656 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1656 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1656) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1656.1, data_11_1656.2]

/-- Complete interval computation for depth 11, residue 1657. -/
theorem bounds_11_1657 : exactInterval 11 1657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1657 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1657) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1657 : oddCount 1657 11 = 7 ∧ acceleratedOrbit 11 1657 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1657 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1657) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1657.1, data_11_1657.2]

/-- Complete interval computation for depth 11, residue 1658. -/
theorem bounds_11_1658 : exactInterval 11 1658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1658 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1658) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1658 : oddCount 1658 11 = 6 ∧ acceleratedOrbit 11 1658 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1658 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1658) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1658.1, data_11_1658.2]

/-- Complete interval computation for depth 11, residue 1659. -/
theorem bounds_11_1659 : exactInterval 11 1659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1659 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1659) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1659 : oddCount 1659 11 = 5 ∧ acceleratedOrbit 11 1659 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1659 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1659) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1659.1, data_11_1659.2]

/-- Complete interval computation for depth 11, residue 1660. -/
theorem bounds_11_1660 : exactInterval 11 1660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1660 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1660) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1660 : oddCount 1660 11 = 7 ∧ acceleratedOrbit 11 1660 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1660 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1660) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1660.1, data_11_1660.2]

/-- Complete interval computation for depth 11, residue 1661. -/
theorem bounds_11_1661 : exactInterval 11 1661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1661 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1661) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1661 : oddCount 1661 11 = 7 ∧ acceleratedOrbit 11 1661 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1661 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1661) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1661.1, data_11_1661.2]

/-- Complete interval computation for depth 11, residue 1662. -/
theorem bounds_11_1662 : exactInterval 11 1662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1662 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1662) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1662 : oddCount 1662 11 = 7 ∧ acceleratedOrbit 11 1662 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1662 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1662) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1662.1, data_11_1662.2]

/-- Complete interval computation for depth 11, residue 1663. -/
theorem bounds_11_1663 : exactInterval 11 1663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1663 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1663) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1663 : oddCount 1663 11 = 10 ∧ acceleratedOrbit 11 1663 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1663 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1663) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1663.1, data_11_1663.2]

end Collatz.Research.StoppingAtlas.Batch0175
