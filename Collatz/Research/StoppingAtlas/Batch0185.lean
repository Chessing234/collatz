import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0185

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1802. -/
theorem bounds_11_1802 : exactInterval 11 1802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1802 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1802) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1802 : oddCount 1802 11 = 6 ∧ acceleratedOrbit 11 1802 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1802 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1802) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1802.1, data_11_1802.2]

/-- Complete interval computation for depth 11, residue 1803. -/
theorem bounds_11_1803 : exactInterval 11 1803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1803 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1803) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1803 : oddCount 1803 11 = 6 ∧ acceleratedOrbit 11 1803 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1803 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1803) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1803.1, data_11_1803.2]

/-- Complete interval computation for depth 11, residue 1804. -/
theorem bounds_11_1804 : exactInterval 11 1804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1804 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1804) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1804 : oddCount 1804 11 = 6 ∧ acceleratedOrbit 11 1804 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1804 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1804) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1804.1, data_11_1804.2]

/-- Complete interval computation for depth 11, residue 1805. -/
theorem bounds_11_1805 : exactInterval 11 1805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1805 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1805) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1805 : oddCount 1805 11 = 6 ∧ acceleratedOrbit 11 1805 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1805 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1805) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1805.1, data_11_1805.2]

/-- Complete interval computation for depth 11, residue 1806. -/
theorem bounds_11_1806 : exactInterval 11 1806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1806 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1806) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1806 : oddCount 1806 11 = 5 ∧ acceleratedOrbit 11 1806 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1806 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1806) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1806.1, data_11_1806.2]

/-- Complete interval computation for depth 11, residue 1807. -/
theorem bounds_11_1807 : exactInterval 11 1807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1807 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1807) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1807 : oddCount 1807 11 = 5 ∧ acceleratedOrbit 11 1807 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1807 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1807) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1807.1, data_11_1807.2]

/-- Complete interval computation for depth 11, residue 1808. -/
theorem bounds_11_1808 : exactInterval 11 1808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1808 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1808) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1808 : oddCount 1808 11 = 2 ∧ acceleratedOrbit 11 1808 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1808 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1808) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1808.1, data_11_1808.2]

/-- Complete interval computation for depth 11, residue 1809. -/
theorem bounds_11_1809 : exactInterval 11 1809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1809 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1809) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1809 : oddCount 1809 11 = 6 ∧ acceleratedOrbit 11 1809 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1809 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1809) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1809.1, data_11_1809.2]

/-- Complete interval computation for depth 11, residue 1810. -/
theorem bounds_11_1810 : exactInterval 11 1810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1810 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1810) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1810 : oddCount 1810 11 = 7 ∧ acceleratedOrbit 11 1810 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1810 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1810) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1810.1, data_11_1810.2]

/-- Complete interval computation for depth 11, residue 1811. -/
theorem bounds_11_1811 : exactInterval 11 1811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1811 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1811) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1811 : oddCount 1811 11 = 7 ∧ acceleratedOrbit 11 1811 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1811 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1811) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1811.1, data_11_1811.2]

/-- Complete interval computation for depth 11, residue 1812. -/
theorem bounds_11_1812 : exactInterval 11 1812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1812 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1812) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1812 : oddCount 1812 11 = 2 ∧ acceleratedOrbit 11 1812 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1812 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1812) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1812.1, data_11_1812.2]

/-- Complete interval computation for depth 11, residue 1813. -/
theorem bounds_11_1813 : exactInterval 11 1813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1813 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1813) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1813 : oddCount 1813 11 = 2 ∧ acceleratedOrbit 11 1813 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1813 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1813) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1813.1, data_11_1813.2]

/-- Complete interval computation for depth 11, residue 1814. -/
theorem bounds_11_1814 : exactInterval 11 1814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1814 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1814) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1814 : oddCount 1814 11 = 7 ∧ acceleratedOrbit 11 1814 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1814 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1814) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1814.1, data_11_1814.2]

/-- Complete interval computation for depth 11, residue 1815. -/
theorem bounds_11_1815 : exactInterval 11 1815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1815 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1815) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1815 : oddCount 1815 11 = 7 ∧ acceleratedOrbit 11 1815 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1815 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1815) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1815.1, data_11_1815.2]

/-- Complete interval computation for depth 11, residue 1816. -/
theorem bounds_11_1816 : exactInterval 11 1816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1816 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1816) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1816 : oddCount 1816 11 = 2 ∧ acceleratedOrbit 11 1816 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1816 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1816) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1816.1, data_11_1816.2]

end Collatz.Research.StoppingAtlas.Batch0185
