import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0186

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1817. -/
theorem bounds_11_1817 : exactInterval 11 1817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1817 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1817) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1817 : oddCount 1817 11 = 8 ∧ acceleratedOrbit 11 1817 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1817 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1817) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1817.1, data_11_1817.2]

/-- Complete interval computation for depth 11, residue 1818. -/
theorem bounds_11_1818 : exactInterval 11 1818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1818 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1818) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1818 : oddCount 1818 11 = 2 ∧ acceleratedOrbit 11 1818 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1818 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1818) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1818.1, data_11_1818.2]

/-- Complete interval computation for depth 11, residue 1819. -/
theorem bounds_11_1819 : exactInterval 11 1819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1819 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1819) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1819 : oddCount 1819 11 = 10 ∧ acceleratedOrbit 11 1819 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1819 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1819) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1819.1, data_11_1819.2]

/-- Complete interval computation for depth 11, residue 1820. -/
theorem bounds_11_1820 : exactInterval 11 1820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1820 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1820) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1820 : oddCount 1820 11 = 6 ∧ acceleratedOrbit 11 1820 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1820 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1820) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1820.1, data_11_1820.2]

/-- Complete interval computation for depth 11, residue 1821. -/
theorem bounds_11_1821 : exactInterval 11 1821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1821 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1821) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1821 : oddCount 1821 11 = 6 ∧ acceleratedOrbit 11 1821 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1821 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1821) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1821.1, data_11_1821.2]

/-- Complete interval computation for depth 11, residue 1822. -/
theorem bounds_11_1822 : exactInterval 11 1822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1822 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1822) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1822 : oddCount 1822 11 = 6 ∧ acceleratedOrbit 11 1822 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1822 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1822) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1822.1, data_11_1822.2]

/-- Complete interval computation for depth 11, residue 1823. -/
theorem bounds_11_1823 : exactInterval 11 1823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1823 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1823) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1823 : oddCount 1823 11 = 7 ∧ acceleratedOrbit 11 1823 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1823 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1823) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1823.1, data_11_1823.2]

/-- Complete interval computation for depth 11, residue 1824. -/
theorem bounds_11_1824 : exactInterval 11 1824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1824 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1824) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1824 : oddCount 1824 11 = 4 ∧ acceleratedOrbit 11 1824 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1824 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1824) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1824.1, data_11_1824.2]

/-- Complete interval computation for depth 11, residue 1825. -/
theorem bounds_11_1825 : exactInterval 11 1825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1825 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1825) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1825 : oddCount 1825 11 = 5 ∧ acceleratedOrbit 11 1825 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1825 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1825) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1825.1, data_11_1825.2]

/-- Complete interval computation for depth 11, residue 1826. -/
theorem bounds_11_1826 : exactInterval 11 1826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1826 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1826) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1826 : oddCount 1826 11 = 5 ∧ acceleratedOrbit 11 1826 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1826 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1826) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1826.1, data_11_1826.2]

/-- Complete interval computation for depth 11, residue 1827. -/
theorem bounds_11_1827 : exactInterval 11 1827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1827 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1827) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1827 : oddCount 1827 11 = 5 ∧ acceleratedOrbit 11 1827 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1827 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1827) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1827.1, data_11_1827.2]

/-- Complete interval computation for depth 11, residue 1828. -/
theorem bounds_11_1828 : exactInterval 11 1828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1828 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1828) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1828 : oddCount 1828 11 = 5 ∧ acceleratedOrbit 11 1828 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1828 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1828) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1828.1, data_11_1828.2]

/-- Complete interval computation for depth 11, residue 1829. -/
theorem bounds_11_1829 : exactInterval 11 1829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1829 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1829) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1829 : oddCount 1829 11 = 5 ∧ acceleratedOrbit 11 1829 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1829 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1829) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1829.1, data_11_1829.2]

/-- Complete interval computation for depth 11, residue 1830. -/
theorem bounds_11_1830 : exactInterval 11 1830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1830 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1830) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1830 : oddCount 1830 11 = 5 ∧ acceleratedOrbit 11 1830 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1830 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1830) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1830.1, data_11_1830.2]

/-- Complete interval computation for depth 11, residue 1831. -/
theorem bounds_11_1831 : exactInterval 11 1831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1831 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1831) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1831 : oddCount 1831 11 = 7 ∧ acceleratedOrbit 11 1831 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1831 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1831) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1831.1, data_11_1831.2]

end Collatz.Research.StoppingAtlas.Batch0186
