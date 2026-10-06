import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0318

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1797. -/
theorem bounds_12_1797 : exactInterval 12 1797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1797 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1797) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1797 : oddCount 1797 12 = 6 ∧ acceleratedOrbit 12 1797 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1797 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1797) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1797.1, data_12_1797.2]

/-- Complete interval computation for depth 12, residue 1798. -/
theorem bounds_12_1798 : exactInterval 12 1798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1798 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1798) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1798 : oddCount 1798 12 = 6 ∧ acceleratedOrbit 12 1798 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1798 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1798) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1798.1, data_12_1798.2]

/-- Complete interval computation for depth 12, residue 1799. -/
theorem bounds_12_1799 : exactInterval 12 1799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1799 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1799) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1799 : oddCount 1799 12 = 7 ∧ acceleratedOrbit 12 1799 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1799 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1799) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1799.1, data_12_1799.2]

/-- Complete interval computation for depth 12, residue 1800. -/
theorem bounds_12_1800 : exactInterval 12 1800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1800 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1800) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1800 : oddCount 1800 12 = 7 ∧ acceleratedOrbit 12 1800 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1800 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1800) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1800.1, data_12_1800.2]

/-- Complete interval computation for depth 12, residue 1801. -/
theorem bounds_12_1801 : exactInterval 12 1801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1801 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1801) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1801 : oddCount 1801 12 = 9 ∧ acceleratedOrbit 12 1801 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1801 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1801) = 3 ^ 9 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1801.1, data_12_1801.2]

/-- Complete interval computation for depth 12, residue 1802. -/
theorem bounds_12_1802 : exactInterval 12 1802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1802 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1802) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1802 : oddCount 1802 12 = 7 ∧ acceleratedOrbit 12 1802 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1802 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1802) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1802.1, data_12_1802.2]

/-- Complete interval computation for depth 12, residue 1803. -/
theorem bounds_12_1803 : exactInterval 12 1803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1803 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1803) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1803 : oddCount 1803 12 = 7 ∧ acceleratedOrbit 12 1803 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1803 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1803) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1803.1, data_12_1803.2]

/-- Complete interval computation for depth 12, residue 1804. -/
theorem bounds_12_1804 : exactInterval 12 1804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1804 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1804) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1804 : oddCount 1804 12 = 7 ∧ acceleratedOrbit 12 1804 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1804 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1804) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1804.1, data_12_1804.2]

/-- Complete interval computation for depth 12, residue 1805. -/
theorem bounds_12_1805 : exactInterval 12 1805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1805 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1805) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1805 : oddCount 1805 12 = 7 ∧ acceleratedOrbit 12 1805 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1805 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1805) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1805.1, data_12_1805.2]

/-- Complete interval computation for depth 12, residue 1806. -/
theorem bounds_12_1806 : exactInterval 12 1806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1806 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1806) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1806 : oddCount 1806 12 = 6 ∧ acceleratedOrbit 12 1806 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1806 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1806) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1806.1, data_12_1806.2]

/-- Complete interval computation for depth 12, residue 1807. -/
theorem bounds_12_1807 : exactInterval 12 1807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1807 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1807) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1807 : oddCount 1807 12 = 6 ∧ acceleratedOrbit 12 1807 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1807 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1807) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1807.1, data_12_1807.2]

/-- Complete interval computation for depth 12, residue 1808. -/
theorem bounds_12_1808 : exactInterval 12 1808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1808 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1808) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1808 : oddCount 1808 12 = 2 ∧ acceleratedOrbit 12 1808 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1808 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1808) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1808.1, data_12_1808.2]

/-- Complete interval computation for depth 12, residue 1809. -/
theorem bounds_12_1809 : exactInterval 12 1809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1809 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1809) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1809 : oddCount 1809 12 = 7 ∧ acceleratedOrbit 12 1809 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1809 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1809) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1809.1, data_12_1809.2]

/-- Complete interval computation for depth 12, residue 1810. -/
theorem bounds_12_1810 : exactInterval 12 1810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1810 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1810) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1810 : oddCount 1810 12 = 8 ∧ acceleratedOrbit 12 1810 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1810 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1810) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1810.1, data_12_1810.2]

/-- Complete interval computation for depth 12, residue 1811. -/
theorem bounds_12_1811 : exactInterval 12 1811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1811 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1811) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1811 : oddCount 1811 12 = 8 ∧ acceleratedOrbit 12 1811 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1811 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1811) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1811.1, data_12_1811.2]

end Collatz.Research.StoppingAtlas.Batch0318
