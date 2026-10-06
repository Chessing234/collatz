import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0585

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1802. -/
theorem bounds_13_1802 : exactInterval 13 1802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1802 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1802) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1802 : oddCount 1802 13 = 8 ∧ acceleratedOrbit 13 1802 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1802 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1802) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1802.1, data_13_1802.2]

/-- Complete interval computation for depth 13, residue 1803. -/
theorem bounds_13_1803 : exactInterval 13 1803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1803 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1803) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1803 : oddCount 1803 13 = 8 ∧ acceleratedOrbit 13 1803 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1803 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1803) = 3 ^ 8 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1803.1, data_13_1803.2]

/-- Complete interval computation for depth 13, residue 1804. -/
theorem bounds_13_1804 : exactInterval 13 1804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1804 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1804) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1804 : oddCount 1804 13 = 8 ∧ acceleratedOrbit 13 1804 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1804 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1804) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1804.1, data_13_1804.2]

/-- Complete interval computation for depth 13, residue 1805. -/
theorem bounds_13_1805 : exactInterval 13 1805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1805 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1805) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1805 : oddCount 1805 13 = 8 ∧ acceleratedOrbit 13 1805 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1805 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1805) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1805.1, data_13_1805.2]

/-- Complete interval computation for depth 13, residue 1806. -/
theorem bounds_13_1806 : exactInterval 13 1806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1806 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1806) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1806 : oddCount 1806 13 = 7 ∧ acceleratedOrbit 13 1806 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1806 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1806) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1806.1, data_13_1806.2]

/-- Complete interval computation for depth 13, residue 1807. -/
theorem bounds_13_1807 : exactInterval 13 1807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1807 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1807) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1807 : oddCount 1807 13 = 7 ∧ acceleratedOrbit 13 1807 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1807 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1807) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1807.1, data_13_1807.2]

/-- Complete interval computation for depth 13, residue 1808. -/
theorem bounds_13_1808 : exactInterval 13 1808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1808 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1808) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1808 : oddCount 1808 13 = 2 ∧ acceleratedOrbit 13 1808 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1808 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1808) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1808.1, data_13_1808.2]

/-- Complete interval computation for depth 13, residue 1809. -/
theorem bounds_13_1809 : exactInterval 13 1809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1809 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1809) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1809 : oddCount 1809 13 = 8 ∧ acceleratedOrbit 13 1809 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1809 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1809) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1809.1, data_13_1809.2]

/-- Complete interval computation for depth 13, residue 1810. -/
theorem bounds_13_1810 : exactInterval 13 1810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1810 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1810) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1810 : oddCount 1810 13 = 8 ∧ acceleratedOrbit 13 1810 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1810 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1810) = 3 ^ 8 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1810.1, data_13_1810.2]

/-- Complete interval computation for depth 13, residue 1811. -/
theorem bounds_13_1811 : exactInterval 13 1811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1811 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1811) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1811 : oddCount 1811 13 = 8 ∧ acceleratedOrbit 13 1811 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1811 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1811) = 3 ^ 8 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1811.1, data_13_1811.2]

/-- Complete interval computation for depth 13, residue 1812. -/
theorem bounds_13_1812 : exactInterval 13 1812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1812 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1812) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1812 : oddCount 1812 13 = 2 ∧ acceleratedOrbit 13 1812 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1812 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1812) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1812.1, data_13_1812.2]

/-- Complete interval computation for depth 13, residue 1813. -/
theorem bounds_13_1813 : exactInterval 13 1813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1813 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1813) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1813 : oddCount 1813 13 = 2 ∧ acceleratedOrbit 13 1813 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1813 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1813) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1813.1, data_13_1813.2]

/-- Complete interval computation for depth 13, residue 1814. -/
theorem bounds_13_1814 : exactInterval 13 1814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1814 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1814) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1814 : oddCount 1814 13 = 9 ∧ acceleratedOrbit 13 1814 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1814 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1814) = 3 ^ 9 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1814.1, data_13_1814.2]

/-- Complete interval computation for depth 13, residue 1815. -/
theorem bounds_13_1815 : exactInterval 13 1815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1815 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1815) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1815 : oddCount 1815 13 = 9 ∧ acceleratedOrbit 13 1815 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1815 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1815) = 3 ^ 9 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1815.1, data_13_1815.2]

/-- Complete interval computation for depth 13, residue 1816. -/
theorem bounds_13_1816 : exactInterval 13 1816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1816 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1816) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1816 : oddCount 1816 13 = 2 ∧ acceleratedOrbit 13 1816 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1816 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1816) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1816.1, data_13_1816.2]

end Collatz.Research.StoppingAtlas.Batch0585
