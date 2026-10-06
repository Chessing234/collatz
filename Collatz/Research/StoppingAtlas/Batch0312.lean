import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0312

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1704. -/
theorem bounds_12_1704 : exactInterval 12 1704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1704 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1704) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1704 : oddCount 1704 12 = 2 ∧ acceleratedOrbit 12 1704 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1704 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1704) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1704.1, data_12_1704.2]

/-- Complete interval computation for depth 12, residue 1705. -/
theorem bounds_12_1705 : exactInterval 12 1705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1705 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1705) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1705 : oddCount 1705 12 = 9 ∧ acceleratedOrbit 12 1705 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1705 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1705) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1705.1, data_12_1705.2]

/-- Complete interval computation for depth 12, residue 1706. -/
theorem bounds_12_1706 : exactInterval 12 1706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1706 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1706) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1706 : oddCount 1706 12 = 2 ∧ acceleratedOrbit 12 1706 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1706 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1706) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1706.1, data_12_1706.2]

/-- Complete interval computation for depth 12, residue 1707. -/
theorem bounds_12_1707 : exactInterval 12 1707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1707 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1707) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1707 : oddCount 1707 12 = 7 ∧ acceleratedOrbit 12 1707 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1707 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1707) = 3 ^ 7 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1707.1, data_12_1707.2]

/-- Complete interval computation for depth 12, residue 1708. -/
theorem bounds_12_1708 : exactInterval 12 1708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1708 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1708) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1708 : oddCount 1708 12 = 7 ∧ acceleratedOrbit 12 1708 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1708 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1708) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1708.1, data_12_1708.2]

/-- Complete interval computation for depth 12, residue 1709. -/
theorem bounds_12_1709 : exactInterval 12 1709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1709 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1709) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1709 : oddCount 1709 12 = 7 ∧ acceleratedOrbit 12 1709 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1709 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1709) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1709.1, data_12_1709.2]

/-- Complete interval computation for depth 12, residue 1710. -/
theorem bounds_12_1710 : exactInterval 12 1710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1710 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1710) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1710 : oddCount 1710 12 = 7 ∧ acceleratedOrbit 12 1710 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1710 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1710) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1710.1, data_12_1710.2]

/-- Complete interval computation for depth 12, residue 1711. -/
theorem bounds_12_1711 : exactInterval 12 1711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1711 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1711) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1711 : oddCount 1711 12 = 8 ∧ acceleratedOrbit 12 1711 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1711 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1711) = 3 ^ 8 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1711.1, data_12_1711.2]

/-- Complete interval computation for depth 12, residue 1712. -/
theorem bounds_12_1712 : exactInterval 12 1712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1712 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1712) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1712 : oddCount 1712 12 = 5 ∧ acceleratedOrbit 12 1712 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1712 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1712) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1712.1, data_12_1712.2]

/-- Complete interval computation for depth 12, residue 1713. -/
theorem bounds_12_1713 : exactInterval 12 1713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1713 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1713) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1713 : oddCount 1713 12 = 4 ∧ acceleratedOrbit 12 1713 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1713 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1713) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1713.1, data_12_1713.2]

/-- Complete interval computation for depth 12, residue 1714. -/
theorem bounds_12_1714 : exactInterval 12 1714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1714 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1714) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1714 : oddCount 1714 12 = 4 ∧ acceleratedOrbit 12 1714 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1714 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1714) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1714.1, data_12_1714.2]

/-- Complete interval computation for depth 12, residue 1715. -/
theorem bounds_12_1715 : exactInterval 12 1715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1715 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1715) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1715 : oddCount 1715 12 = 4 ∧ acceleratedOrbit 12 1715 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1715 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1715) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1715.1, data_12_1715.2]

/-- Complete interval computation for depth 12, residue 1716. -/
theorem bounds_12_1716 : exactInterval 12 1716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1716 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1716) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1716 : oddCount 1716 12 = 5 ∧ acceleratedOrbit 12 1716 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1716 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1716) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1716.1, data_12_1716.2]

/-- Complete interval computation for depth 12, residue 1717. -/
theorem bounds_12_1717 : exactInterval 12 1717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1717 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1717) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1717 : oddCount 1717 12 = 5 ∧ acceleratedOrbit 12 1717 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1717 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1717) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1717.1, data_12_1717.2]

/-- Complete interval computation for depth 12, residue 1718. -/
theorem bounds_12_1718 : exactInterval 12 1718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1718 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1718) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1718 : oddCount 1718 12 = 7 ∧ acceleratedOrbit 12 1718 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1718 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1718) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1718.1, data_12_1718.2]

/-- Complete interval computation for depth 12, residue 1719. -/
theorem bounds_12_1719 : exactInterval 12 1719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1719 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1719) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1719 : oddCount 1719 12 = 7 ∧ acceleratedOrbit 12 1719 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1719 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1719) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1719.1, data_12_1719.2]

end Collatz.Research.StoppingAtlas.Batch0312
