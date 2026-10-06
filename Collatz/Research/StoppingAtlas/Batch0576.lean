import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0576

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1664. -/
theorem bounds_13_1664 : exactInterval 13 1664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1664 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1664) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1664 : oddCount 1664 13 = 2 ∧ acceleratedOrbit 13 1664 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1664 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1664) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1664.1, data_13_1664.2]

/-- Complete interval computation for depth 13, residue 1665. -/
theorem bounds_13_1665 : exactInterval 13 1665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1665 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1665) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1665 : oddCount 1665 13 = 9 ∧ acceleratedOrbit 13 1665 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1665 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1665) = 3 ^ 9 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1665.1, data_13_1665.2]

/-- Complete interval computation for depth 13, residue 1666. -/
theorem bounds_13_1666 : exactInterval 13 1666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1666 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1666) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1666 : oddCount 1666 13 = 4 ∧ acceleratedOrbit 13 1666 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1666 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1666) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1666.1, data_13_1666.2]

/-- Complete interval computation for depth 13, residue 1667. -/
theorem bounds_13_1667 : exactInterval 13 1667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1667 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1667) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1667 : oddCount 1667 13 = 4 ∧ acceleratedOrbit 13 1667 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1667 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1667) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1667.1, data_13_1667.2]

/-- Complete interval computation for depth 13, residue 1668. -/
theorem bounds_13_1668 : exactInterval 13 1668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1668 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1668) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1668 : oddCount 1668 13 = 7 ∧ acceleratedOrbit 13 1668 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1668 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1668) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1668.1, data_13_1668.2]

/-- Complete interval computation for depth 13, residue 1669. -/
theorem bounds_13_1669 : exactInterval 13 1669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1669 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1669) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1669 : oddCount 1669 13 = 7 ∧ acceleratedOrbit 13 1669 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1669 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1669) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1669.1, data_13_1669.2]

/-- Complete interval computation for depth 13, residue 1670. -/
theorem bounds_13_1670 : exactInterval 13 1670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1670 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1670) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1670 : oddCount 1670 13 = 7 ∧ acceleratedOrbit 13 1670 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1670 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1670) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1670.1, data_13_1670.2]

/-- Complete interval computation for depth 13, residue 1671. -/
theorem bounds_13_1671 : exactInterval 13 1671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1671 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1671) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1671 : oddCount 1671 13 = 6 ∧ acceleratedOrbit 13 1671 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1671 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1671) = 3 ^ 6 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1671.1, data_13_1671.2]

/-- Complete interval computation for depth 13, residue 1672. -/
theorem bounds_13_1672 : exactInterval 13 1672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1672 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1672) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1672 : oddCount 1672 13 = 6 ∧ acceleratedOrbit 13 1672 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1672 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1672) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1672.1, data_13_1672.2]

/-- Complete interval computation for depth 13, residue 1673. -/
theorem bounds_13_1673 : exactInterval 13 1673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1673 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1673) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1673 : oddCount 1673 13 = 9 ∧ acceleratedOrbit 13 1673 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1673 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1673) = 3 ^ 9 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1673.1, data_13_1673.2]

/-- Complete interval computation for depth 13, residue 1674. -/
theorem bounds_13_1674 : exactInterval 13 1674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1674 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1674) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1674 : oddCount 1674 13 = 6 ∧ acceleratedOrbit 13 1674 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1674 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1674) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1674.1, data_13_1674.2]

/-- Complete interval computation for depth 13, residue 1675. -/
theorem bounds_13_1675 : exactInterval 13 1675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1675 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1675) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1675 : oddCount 1675 13 = 7 ∧ acceleratedOrbit 13 1675 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1675 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1675) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1675.1, data_13_1675.2]

/-- Complete interval computation for depth 13, residue 1676. -/
theorem bounds_13_1676 : exactInterval 13 1676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1676 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1676) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1676 : oddCount 1676 13 = 6 ∧ acceleratedOrbit 13 1676 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1676 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1676) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1676.1, data_13_1676.2]

/-- Complete interval computation for depth 13, residue 1677. -/
theorem bounds_13_1677 : exactInterval 13 1677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1677 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1677) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1677 : oddCount 1677 13 = 6 ∧ acceleratedOrbit 13 1677 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1677 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1677) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1677.1, data_13_1677.2]

/-- Complete interval computation for depth 13, residue 1678. -/
theorem bounds_13_1678 : exactInterval 13 1678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1678 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1678) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1678 : oddCount 1678 13 = 9 ∧ acceleratedOrbit 13 1678 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1678 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1678) = 3 ^ 9 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1678.1, data_13_1678.2]

end Collatz.Research.StoppingAtlas.Batch0576
