import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0575

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1648. -/
theorem bounds_13_1648 : exactInterval 13 1648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1648 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1648) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1648 : oddCount 1648 13 = 7 ∧ acceleratedOrbit 13 1648 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1648 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1648) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1648.1, data_13_1648.2]

/-- Complete interval computation for depth 13, residue 1649. -/
theorem bounds_13_1649 : exactInterval 13 1649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1649 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1649) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1649 : oddCount 1649 13 = 4 ∧ acceleratedOrbit 13 1649 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1649 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1649) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1649.1, data_13_1649.2]

/-- Complete interval computation for depth 13, residue 1650. -/
theorem bounds_13_1650 : exactInterval 13 1650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1650 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1650) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1650 : oddCount 1650 13 = 7 ∧ acceleratedOrbit 13 1650 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1650 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1650) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1650.1, data_13_1650.2]

/-- Complete interval computation for depth 13, residue 1651. -/
theorem bounds_13_1651 : exactInterval 13 1651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1651 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1651) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1651 : oddCount 1651 13 = 7 ∧ acceleratedOrbit 13 1651 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1651 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1651) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1651.1, data_13_1651.2]

/-- Complete interval computation for depth 13, residue 1652. -/
theorem bounds_13_1652 : exactInterval 13 1652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1652 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1652) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1652 : oddCount 1652 13 = 7 ∧ acceleratedOrbit 13 1652 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1652 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1652) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1652.1, data_13_1652.2]

/-- Complete interval computation for depth 13, residue 1653. -/
theorem bounds_13_1653 : exactInterval 13 1653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1653 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1653) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1653 : oddCount 1653 13 = 7 ∧ acceleratedOrbit 13 1653 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1653 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1653) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1653.1, data_13_1653.2]

/-- Complete interval computation for depth 13, residue 1654. -/
theorem bounds_13_1654 : exactInterval 13 1654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1654 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1654) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1654 : oddCount 1654 13 = 6 ∧ acceleratedOrbit 13 1654 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1654 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1654) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1654.1, data_13_1654.2]

/-- Complete interval computation for depth 13, residue 1655. -/
theorem bounds_13_1655 : exactInterval 13 1655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1655 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1655) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1655 : oddCount 1655 13 = 6 ∧ acceleratedOrbit 13 1655 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1655 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1655) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1655.1, data_13_1655.2]

/-- Complete interval computation for depth 13, residue 1656. -/
theorem bounds_13_1656 : exactInterval 13 1656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1656 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1656) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1656 : oddCount 1656 13 = 7 ∧ acceleratedOrbit 13 1656 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1656 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1656) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1656.1, data_13_1656.2]

/-- Complete interval computation for depth 13, residue 1657. -/
theorem bounds_13_1657 : exactInterval 13 1657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1657 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1657) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1657 : oddCount 1657 13 = 7 ∧ acceleratedOrbit 13 1657 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1657 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1657) = 3 ^ 7 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1657.1, data_13_1657.2]

/-- Complete interval computation for depth 13, residue 1658. -/
theorem bounds_13_1658 : exactInterval 13 1658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1658 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1658) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1658 : oddCount 1658 13 = 7 ∧ acceleratedOrbit 13 1658 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1658 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1658) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1658.1, data_13_1658.2]

/-- Complete interval computation for depth 13, residue 1659. -/
theorem bounds_13_1659 : exactInterval 13 1659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1659 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1659) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1659 : oddCount 1659 13 = 6 ∧ acceleratedOrbit 13 1659 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1659 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1659) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1659.1, data_13_1659.2]

/-- Complete interval computation for depth 13, residue 1660. -/
theorem bounds_13_1660 : exactInterval 13 1660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1660 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1660) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1660 : oddCount 1660 13 = 8 ∧ acceleratedOrbit 13 1660 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1660 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1660) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1660.1, data_13_1660.2]

/-- Complete interval computation for depth 13, residue 1661. -/
theorem bounds_13_1661 : exactInterval 13 1661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1661 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1661) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1661 : oddCount 1661 13 = 8 ∧ acceleratedOrbit 13 1661 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1661 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1661) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1661.1, data_13_1661.2]

/-- Complete interval computation for depth 13, residue 1662. -/
theorem bounds_13_1662 : exactInterval 13 1662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1662 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1662) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1662 : oddCount 1662 13 = 8 ∧ acceleratedOrbit 13 1662 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1662 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1662) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1662.1, data_13_1662.2]

/-- Complete interval computation for depth 13, residue 1663. -/
theorem bounds_13_1663 : exactInterval 13 1663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1663 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1663) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1663 : oddCount 1663 13 = 11 ∧ acceleratedOrbit 13 1663 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1663 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1663) = 3 ^ 11 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1663.1, data_13_1663.2]

end Collatz.Research.StoppingAtlas.Batch0575
