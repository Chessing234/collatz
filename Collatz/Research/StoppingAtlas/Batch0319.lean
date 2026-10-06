import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0319

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1812. -/
theorem bounds_12_1812 : exactInterval 12 1812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1812 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1812) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1812 : oddCount 1812 12 = 2 ∧ acceleratedOrbit 12 1812 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1812 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1812) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1812.1, data_12_1812.2]

/-- Complete interval computation for depth 12, residue 1813. -/
theorem bounds_12_1813 : exactInterval 12 1813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1813 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1813) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1813 : oddCount 1813 12 = 2 ∧ acceleratedOrbit 12 1813 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1813 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1813) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1813.1, data_12_1813.2]

/-- Complete interval computation for depth 12, residue 1814. -/
theorem bounds_12_1814 : exactInterval 12 1814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1814 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1814) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1814 : oddCount 1814 12 = 8 ∧ acceleratedOrbit 12 1814 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1814 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1814) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1814.1, data_12_1814.2]

/-- Complete interval computation for depth 12, residue 1815. -/
theorem bounds_12_1815 : exactInterval 12 1815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1815 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1815) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1815 : oddCount 1815 12 = 8 ∧ acceleratedOrbit 12 1815 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1815 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1815) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1815.1, data_12_1815.2]

/-- Complete interval computation for depth 12, residue 1816. -/
theorem bounds_12_1816 : exactInterval 12 1816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1816 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1816) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1816 : oddCount 1816 12 = 2 ∧ acceleratedOrbit 12 1816 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1816 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1816) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1816.1, data_12_1816.2]

/-- Complete interval computation for depth 12, residue 1817. -/
theorem bounds_12_1817 : exactInterval 12 1817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1817 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1817) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1817 : oddCount 1817 12 = 9 ∧ acceleratedOrbit 12 1817 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1817 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1817) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1817.1, data_12_1817.2]

/-- Complete interval computation for depth 12, residue 1818. -/
theorem bounds_12_1818 : exactInterval 12 1818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1818 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1818) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1818 : oddCount 1818 12 = 2 ∧ acceleratedOrbit 12 1818 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1818 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1818) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1818.1, data_12_1818.2]

/-- Complete interval computation for depth 12, residue 1819. -/
theorem bounds_12_1819 : exactInterval 12 1819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1819 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1819) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1819 : oddCount 1819 12 = 11 ∧ acceleratedOrbit 12 1819 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1819 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1819) = 3 ^ 11 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1819.1, data_12_1819.2]

/-- Complete interval computation for depth 12, residue 1820. -/
theorem bounds_12_1820 : exactInterval 12 1820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1820 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1820) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1820 : oddCount 1820 12 = 6 ∧ acceleratedOrbit 12 1820 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1820 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1820) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1820.1, data_12_1820.2]

/-- Complete interval computation for depth 12, residue 1821. -/
theorem bounds_12_1821 : exactInterval 12 1821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1821 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1821) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1821 : oddCount 1821 12 = 6 ∧ acceleratedOrbit 12 1821 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1821 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1821) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1821.1, data_12_1821.2]

/-- Complete interval computation for depth 12, residue 1822. -/
theorem bounds_12_1822 : exactInterval 12 1822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1822 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1822) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1822 : oddCount 1822 12 = 6 ∧ acceleratedOrbit 12 1822 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1822 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1822) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1822.1, data_12_1822.2]

/-- Complete interval computation for depth 12, residue 1823. -/
theorem bounds_12_1823 : exactInterval 12 1823 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1823 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1823) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1823 : oddCount 1823 12 = 7 ∧ acceleratedOrbit 12 1823 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1823 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1823) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1823.1, data_12_1823.2]

/-- Complete interval computation for depth 12, residue 1824. -/
theorem bounds_12_1824 : exactInterval 12 1824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1824 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1824) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1824 : oddCount 1824 12 = 4 ∧ acceleratedOrbit 12 1824 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1824 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1824) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1824.1, data_12_1824.2]

/-- Complete interval computation for depth 12, residue 1825. -/
theorem bounds_12_1825 : exactInterval 12 1825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1825 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1825) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1825 : oddCount 1825 12 = 6 ∧ acceleratedOrbit 12 1825 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1825 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1825) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1825.1, data_12_1825.2]

/-- Complete interval computation for depth 12, residue 1826. -/
theorem bounds_12_1826 : exactInterval 12 1826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1826 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1826) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1826 : oddCount 1826 12 = 5 ∧ acceleratedOrbit 12 1826 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1826 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1826) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1826.1, data_12_1826.2]

end Collatz.Research.StoppingAtlas.Batch0319
