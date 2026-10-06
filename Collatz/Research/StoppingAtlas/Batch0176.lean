import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0176

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1664. -/
theorem bounds_11_1664 : exactInterval 11 1664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1664 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1664) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1664 : oddCount 1664 11 = 2 ∧ acceleratedOrbit 11 1664 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1664 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1664) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1664.1, data_11_1664.2]

/-- Complete interval computation for depth 11, residue 1665. -/
theorem bounds_11_1665 : exactInterval 11 1665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1665 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1665) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1665 : oddCount 1665 11 = 8 ∧ acceleratedOrbit 11 1665 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1665 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1665) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1665.1, data_11_1665.2]

/-- Complete interval computation for depth 11, residue 1666. -/
theorem bounds_11_1666 : exactInterval 11 1666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1666 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1666) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1666 : oddCount 1666 11 = 3 ∧ acceleratedOrbit 11 1666 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1666 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1666) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1666.1, data_11_1666.2]

/-- Complete interval computation for depth 11, residue 1667. -/
theorem bounds_11_1667 : exactInterval 11 1667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1667 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1667) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1667 : oddCount 1667 11 = 3 ∧ acceleratedOrbit 11 1667 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1667 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1667) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1667.1, data_11_1667.2]

/-- Complete interval computation for depth 11, residue 1668. -/
theorem bounds_11_1668 : exactInterval 11 1668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1668 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1668) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1668 : oddCount 1668 11 = 5 ∧ acceleratedOrbit 11 1668 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1668 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1668) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1668.1, data_11_1668.2]

/-- Complete interval computation for depth 11, residue 1669. -/
theorem bounds_11_1669 : exactInterval 11 1669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1669 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1669) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1669 : oddCount 1669 11 = 5 ∧ acceleratedOrbit 11 1669 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1669 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1669) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1669.1, data_11_1669.2]

/-- Complete interval computation for depth 11, residue 1670. -/
theorem bounds_11_1670 : exactInterval 11 1670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1670 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1670) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1670 : oddCount 1670 11 = 5 ∧ acceleratedOrbit 11 1670 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1670 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1670) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1670.1, data_11_1670.2]

/-- Complete interval computation for depth 11, residue 1671. -/
theorem bounds_11_1671 : exactInterval 11 1671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1671 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1671) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1671 : oddCount 1671 11 = 6 ∧ acceleratedOrbit 11 1671 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1671 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1671) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1671.1, data_11_1671.2]

/-- Complete interval computation for depth 11, residue 1672. -/
theorem bounds_11_1672 : exactInterval 11 1672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1672 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1672) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1672 : oddCount 1672 11 = 4 ∧ acceleratedOrbit 11 1672 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1672 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1672) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1672.1, data_11_1672.2]

/-- Complete interval computation for depth 11, residue 1673. -/
theorem bounds_11_1673 : exactInterval 11 1673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1673 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1673) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1673 : oddCount 1673 11 = 8 ∧ acceleratedOrbit 11 1673 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1673 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1673) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1673.1, data_11_1673.2]

/-- Complete interval computation for depth 11, residue 1674. -/
theorem bounds_11_1674 : exactInterval 11 1674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1674 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1674) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1674 : oddCount 1674 11 = 4 ∧ acceleratedOrbit 11 1674 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1674 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1674) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1674.1, data_11_1674.2]

/-- Complete interval computation for depth 11, residue 1675. -/
theorem bounds_11_1675 : exactInterval 11 1675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1675 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1675) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1675 : oddCount 1675 11 = 5 ∧ acceleratedOrbit 11 1675 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1675 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1675) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1675.1, data_11_1675.2]

/-- Complete interval computation for depth 11, residue 1676. -/
theorem bounds_11_1676 : exactInterval 11 1676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1676 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1676) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1676 : oddCount 1676 11 = 4 ∧ acceleratedOrbit 11 1676 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1676 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1676) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1676.1, data_11_1676.2]

/-- Complete interval computation for depth 11, residue 1677. -/
theorem bounds_11_1677 : exactInterval 11 1677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1677 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1677) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1677 : oddCount 1677 11 = 4 ∧ acceleratedOrbit 11 1677 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1677 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1677) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1677.1, data_11_1677.2]

/-- Complete interval computation for depth 11, residue 1678. -/
theorem bounds_11_1678 : exactInterval 11 1678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1678 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1678) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1678 : oddCount 1678 11 = 7 ∧ acceleratedOrbit 11 1678 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1678 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1678) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1678.1, data_11_1678.2]

end Collatz.Research.StoppingAtlas.Batch0176
