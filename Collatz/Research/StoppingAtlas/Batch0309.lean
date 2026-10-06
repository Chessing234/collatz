import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0309

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1658. -/
theorem bounds_12_1658 : exactInterval 12 1658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1658 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1658) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1658 : oddCount 1658 12 = 7 ∧ acceleratedOrbit 12 1658 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1658 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1658) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1658.1, data_12_1658.2]

/-- Complete interval computation for depth 12, residue 1659. -/
theorem bounds_12_1659 : exactInterval 12 1659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1659 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1659) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1659 : oddCount 1659 12 = 6 ∧ acceleratedOrbit 12 1659 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1659 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1659) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1659.1, data_12_1659.2]

/-- Complete interval computation for depth 12, residue 1660. -/
theorem bounds_12_1660 : exactInterval 12 1660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1660 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1660) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1660 : oddCount 1660 12 = 8 ∧ acceleratedOrbit 12 1660 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1660 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1660) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1660.1, data_12_1660.2]

/-- Complete interval computation for depth 12, residue 1661. -/
theorem bounds_12_1661 : exactInterval 12 1661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1661 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1661) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1661 : oddCount 1661 12 = 8 ∧ acceleratedOrbit 12 1661 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1661 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1661) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1661.1, data_12_1661.2]

/-- Complete interval computation for depth 12, residue 1662. -/
theorem bounds_12_1662 : exactInterval 12 1662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1662 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1662) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1662 : oddCount 1662 12 = 8 ∧ acceleratedOrbit 12 1662 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1662 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1662) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1662.1, data_12_1662.2]

/-- Complete interval computation for depth 12, residue 1663. -/
theorem bounds_12_1663 : exactInterval 12 1663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1663 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1663) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1663 : oddCount 1663 12 = 10 ∧ acceleratedOrbit 12 1663 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1663 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1663) = 3 ^ 10 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1663.1, data_12_1663.2]

/-- Complete interval computation for depth 12, residue 1664. -/
theorem bounds_12_1664 : exactInterval 12 1664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1664 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1664) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1664 : oddCount 1664 12 = 2 ∧ acceleratedOrbit 12 1664 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1664 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1664) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1664.1, data_12_1664.2]

/-- Complete interval computation for depth 12, residue 1665. -/
theorem bounds_12_1665 : exactInterval 12 1665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1665 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1665) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1665 : oddCount 1665 12 = 9 ∧ acceleratedOrbit 12 1665 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1665 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1665) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1665.1, data_12_1665.2]

/-- Complete interval computation for depth 12, residue 1666. -/
theorem bounds_12_1666 : exactInterval 12 1666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1666 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1666) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1666 : oddCount 1666 12 = 3 ∧ acceleratedOrbit 12 1666 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1666 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1666) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1666.1, data_12_1666.2]

/-- Complete interval computation for depth 12, residue 1667. -/
theorem bounds_12_1667 : exactInterval 12 1667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1667 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1667) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1667 : oddCount 1667 12 = 3 ∧ acceleratedOrbit 12 1667 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1667 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1667) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1667.1, data_12_1667.2]

/-- Complete interval computation for depth 12, residue 1668. -/
theorem bounds_12_1668 : exactInterval 12 1668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1668 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1668) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1668 : oddCount 1668 12 = 6 ∧ acceleratedOrbit 12 1668 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1668 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1668) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1668.1, data_12_1668.2]

/-- Complete interval computation for depth 12, residue 1669. -/
theorem bounds_12_1669 : exactInterval 12 1669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1669 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1669) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1669 : oddCount 1669 12 = 6 ∧ acceleratedOrbit 12 1669 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1669 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1669) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1669.1, data_12_1669.2]

/-- Complete interval computation for depth 12, residue 1670. -/
theorem bounds_12_1670 : exactInterval 12 1670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1670 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1670) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1670 : oddCount 1670 12 = 6 ∧ acceleratedOrbit 12 1670 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1670 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1670) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1670.1, data_12_1670.2]

/-- Complete interval computation for depth 12, residue 1671. -/
theorem bounds_12_1671 : exactInterval 12 1671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1671 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1671) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1671 : oddCount 1671 12 = 6 ∧ acceleratedOrbit 12 1671 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1671 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1671) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1671.1, data_12_1671.2]

/-- Complete interval computation for depth 12, residue 1672. -/
theorem bounds_12_1672 : exactInterval 12 1672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1672 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1672) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1672 : oddCount 1672 12 = 5 ∧ acceleratedOrbit 12 1672 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1672 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1672) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1672.1, data_12_1672.2]

/-- Complete interval computation for depth 12, residue 1673. -/
theorem bounds_12_1673 : exactInterval 12 1673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1673 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1673) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1673 : oddCount 1673 12 = 8 ∧ acceleratedOrbit 12 1673 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1673 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1673) = 3 ^ 8 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1673.1, data_12_1673.2]

end Collatz.Research.StoppingAtlas.Batch0309
