import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0056

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1802. -/
theorem bounds_15_1802 : exactInterval 15 1802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1802 : oddCount 1802 15 = 9 ∧ acceleratedOrbit 15 1802 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1802) = 3 ^ 9 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1802.1, data_15_1802.2]

/-- Complete interval computation for depth 15, residue 1803. -/
theorem bounds_15_1803 : exactInterval 15 1803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1803 : oddCount 1803 15 = 8 ∧ acceleratedOrbit 15 1803 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1803) = 3 ^ 8 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1803.1, data_15_1803.2]

/-- Complete interval computation for depth 15, residue 1804. -/
theorem bounds_15_1804 : exactInterval 15 1804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1804 : oddCount 1804 15 = 9 ∧ acceleratedOrbit 15 1804 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1804) = 3 ^ 9 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1804.1, data_15_1804.2]

/-- Complete interval computation for depth 15, residue 1805. -/
theorem bounds_15_1805 : exactInterval 15 1805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1805 : oddCount 1805 15 = 9 ∧ acceleratedOrbit 15 1805 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1805) = 3 ^ 9 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1805.1, data_15_1805.2]

/-- Complete interval computation for depth 15, residue 1806. -/
theorem bounds_15_1806 : exactInterval 15 1806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1806 : oddCount 1806 15 = 8 ∧ acceleratedOrbit 15 1806 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1806) = 3 ^ 8 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1806.1, data_15_1806.2]

/-- Complete interval computation for depth 15, residue 1807. -/
theorem bounds_15_1807 : exactInterval 15 1807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1807 : oddCount 1807 15 = 8 ∧ acceleratedOrbit 15 1807 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1807) = 3 ^ 8 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1807.1, data_15_1807.2]

/-- Complete interval computation for depth 15, residue 1808. -/
theorem bounds_15_1808 : exactInterval 15 1808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1808 : oddCount 1808 15 = 3 ∧ acceleratedOrbit 15 1808 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1808) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1808.1, data_15_1808.2]

/-- Complete interval computation for depth 15, residue 1809. -/
theorem bounds_15_1809 : exactInterval 15 1809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1809 : oddCount 1809 15 = 9 ∧ acceleratedOrbit 15 1809 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1809) = 3 ^ 9 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1809.1, data_15_1809.2]

/-- Complete interval computation for depth 15, residue 1810. -/
theorem bounds_15_1810 : exactInterval 15 1810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1810 : oddCount 1810 15 = 9 ∧ acceleratedOrbit 15 1810 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1810) = 3 ^ 9 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1810.1, data_15_1810.2]

/-- Complete interval computation for depth 15, residue 1811. -/
theorem bounds_15_1811 : exactInterval 15 1811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1811 : oddCount 1811 15 = 9 ∧ acceleratedOrbit 15 1811 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1811) = 3 ^ 9 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1811.1, data_15_1811.2]

/-- Complete interval computation for depth 15, residue 1812. -/
theorem bounds_15_1812 : exactInterval 15 1812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1812 : oddCount 1812 15 = 3 ∧ acceleratedOrbit 15 1812 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1812) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1812.1, data_15_1812.2]

/-- Complete interval computation for depth 15, residue 1813. -/
theorem bounds_15_1813 : exactInterval 15 1813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1813 : oddCount 1813 15 = 3 ∧ acceleratedOrbit 15 1813 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1813) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1813.1, data_15_1813.2]

/-- Complete interval computation for depth 15, residue 1814. -/
theorem bounds_15_1814 : exactInterval 15 1814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1814 : oddCount 1814 15 = 10 ∧ acceleratedOrbit 15 1814 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1814) = 3 ^ 10 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1814.1, data_15_1814.2]

/-- Complete interval computation for depth 15, residue 1815. -/
theorem bounds_15_1815 : exactInterval 15 1815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1815 : oddCount 1815 15 = 10 ∧ acceleratedOrbit 15 1815 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1815) = 3 ^ 10 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1815.1, data_15_1815.2]

/-- Complete interval computation for depth 15, residue 1816. -/
theorem bounds_15_1816 : exactInterval 15 1816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1816 : oddCount 1816 15 = 3 ∧ acceleratedOrbit 15 1816 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1816) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1816.1, data_15_1816.2]

/-- Complete interval computation for depth 15, residue 1817. -/
theorem bounds_15_1817 : exactInterval 15 1817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1817 : oddCount 1817 15 = 11 ∧ acceleratedOrbit 15 1817 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1817) = 3 ^ 11 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1817.1, data_15_1817.2]

/-- Complete interval computation for depth 15, residue 1818. -/
theorem bounds_15_1818 : exactInterval 15 1818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1818 : oddCount 1818 15 = 3 ∧ acceleratedOrbit 15 1818 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1818) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1818.1, data_15_1818.2]

/-- Complete interval computation for depth 15, residue 1819. -/
theorem bounds_15_1819 : exactInterval 15 1819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1819 : oddCount 1819 15 = 13 ∧ acceleratedOrbit 15 1819 = 88573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1819) = 3 ^ 13 * m + 88573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1819.1, data_15_1819.2]

/-- Complete interval computation for depth 15, residue 1820. -/
theorem bounds_15_1820 : exactInterval 15 1820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1820 : oddCount 1820 15 = 7 ∧ acceleratedOrbit 15 1820 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1820) = 3 ^ 7 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1820.1, data_15_1820.2]

/-- Complete interval computation for depth 15, residue 1821. -/
theorem bounds_15_1821 : exactInterval 15 1821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1821 : oddCount 1821 15 = 7 ∧ acceleratedOrbit 15 1821 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1821) = 3 ^ 7 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1821.1, data_15_1821.2]

/-- Complete interval computation for depth 15, residue 1822. -/
theorem bounds_15_1822 : exactInterval 15 1822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1822 : oddCount 1822 15 = 7 ∧ acceleratedOrbit 15 1822 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1822) = 3 ^ 7 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1822.1, data_15_1822.2]

/-- Complete interval computation for depth 15, residue 1823. -/
theorem bounds_15_1823 : exactInterval 15 1823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1823 : oddCount 1823 15 = 9 ∧ acceleratedOrbit 15 1823 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1823) = 3 ^ 9 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1823.1, data_15_1823.2]

/-- Complete interval computation for depth 15, residue 1824. -/
theorem bounds_15_1824 : exactInterval 15 1824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1824 : oddCount 1824 15 = 5 ∧ acceleratedOrbit 15 1824 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1824) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1824.1, data_15_1824.2]

/-- Complete interval computation for depth 15, residue 1825. -/
theorem bounds_15_1825 : exactInterval 15 1825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1825 : oddCount 1825 15 = 8 ∧ acceleratedOrbit 15 1825 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1825) = 3 ^ 8 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1825.1, data_15_1825.2]

/-- Complete interval computation for depth 15, residue 1826. -/
theorem bounds_15_1826 : exactInterval 15 1826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1826 : oddCount 1826 15 = 6 ∧ acceleratedOrbit 15 1826 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1826) = 3 ^ 6 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1826.1, data_15_1826.2]

/-- Complete interval computation for depth 15, residue 1827. -/
theorem bounds_15_1827 : exactInterval 15 1827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1827 : oddCount 1827 15 = 6 ∧ acceleratedOrbit 15 1827 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1827) = 3 ^ 6 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1827.1, data_15_1827.2]

/-- Complete interval computation for depth 15, residue 1828. -/
theorem bounds_15_1828 : exactInterval 15 1828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1828 : oddCount 1828 15 = 6 ∧ acceleratedOrbit 15 1828 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1828) = 3 ^ 6 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1828.1, data_15_1828.2]

/-- Complete interval computation for depth 15, residue 1829. -/
theorem bounds_15_1829 : exactInterval 15 1829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1829 : oddCount 1829 15 = 6 ∧ acceleratedOrbit 15 1829 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1829) = 3 ^ 6 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1829.1, data_15_1829.2]

/-- Complete interval computation for depth 15, residue 1830. -/
theorem bounds_15_1830 : exactInterval 15 1830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1830 : oddCount 1830 15 = 6 ∧ acceleratedOrbit 15 1830 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1830) = 3 ^ 6 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1830.1, data_15_1830.2]

/-- Complete interval computation for depth 15, residue 1831. -/
theorem bounds_15_1831 : exactInterval 15 1831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1831 : oddCount 1831 15 = 8 ∧ acceleratedOrbit 15 1831 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1831) = 3 ^ 8 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1831.1, data_15_1831.2]

/-- Complete interval computation for depth 15, residue 1832. -/
theorem bounds_15_1832 : exactInterval 15 1832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1832 : oddCount 1832 15 = 5 ∧ acceleratedOrbit 15 1832 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1832) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1832.1, data_15_1832.2]

/-- Complete interval computation for depth 15, residue 1833. -/
theorem bounds_15_1833 : exactInterval 15 1833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1833 : oddCount 1833 15 = 8 ∧ acceleratedOrbit 15 1833 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1833) = 3 ^ 8 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1833.1, data_15_1833.2]

/-- Complete interval computation for depth 15, residue 1834. -/
theorem bounds_15_1834 : exactInterval 15 1834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1834 : oddCount 1834 15 = 5 ∧ acceleratedOrbit 15 1834 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1834) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1834.1, data_15_1834.2]

end Collatz.Research.PassageAtlas.Batch0056
