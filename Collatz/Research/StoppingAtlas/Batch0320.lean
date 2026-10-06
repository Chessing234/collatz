import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0320

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1827. -/
theorem bounds_12_1827 : exactInterval 12 1827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1827 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1827) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1827 : oddCount 1827 12 = 5 ∧ acceleratedOrbit 12 1827 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1827 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1827) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1827.1, data_12_1827.2]

/-- Complete interval computation for depth 12, residue 1828. -/
theorem bounds_12_1828 : exactInterval 12 1828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1828 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1828) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1828 : oddCount 1828 12 = 5 ∧ acceleratedOrbit 12 1828 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1828 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1828) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1828.1, data_12_1828.2]

/-- Complete interval computation for depth 12, residue 1829. -/
theorem bounds_12_1829 : exactInterval 12 1829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1829 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1829) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1829 : oddCount 1829 12 = 5 ∧ acceleratedOrbit 12 1829 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1829 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1829) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1829.1, data_12_1829.2]

/-- Complete interval computation for depth 12, residue 1830. -/
theorem bounds_12_1830 : exactInterval 12 1830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1830 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1830) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1830 : oddCount 1830 12 = 5 ∧ acceleratedOrbit 12 1830 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1830 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1830) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1830.1, data_12_1830.2]

/-- Complete interval computation for depth 12, residue 1831. -/
theorem bounds_12_1831 : exactInterval 12 1831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1831 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1831) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1831 : oddCount 1831 12 = 8 ∧ acceleratedOrbit 12 1831 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1831 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1831) = 3 ^ 8 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1831.1, data_12_1831.2]

/-- Complete interval computation for depth 12, residue 1832. -/
theorem bounds_12_1832 : exactInterval 12 1832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1832 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1832) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1832 : oddCount 1832 12 = 4 ∧ acceleratedOrbit 12 1832 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1832 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1832) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1832.1, data_12_1832.2]

/-- Complete interval computation for depth 12, residue 1833. -/
theorem bounds_12_1833 : exactInterval 12 1833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1833 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1833) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1833 : oddCount 1833 12 = 7 ∧ acceleratedOrbit 12 1833 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1833 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1833) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1833.1, data_12_1833.2]

/-- Complete interval computation for depth 12, residue 1834. -/
theorem bounds_12_1834 : exactInterval 12 1834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1834 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1834) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1834 : oddCount 1834 12 = 4 ∧ acceleratedOrbit 12 1834 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1834 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1834) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1834.1, data_12_1834.2]

/-- Complete interval computation for depth 12, residue 1835. -/
theorem bounds_12_1835 : exactInterval 12 1835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1835 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1835) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1835 : oddCount 1835 12 = 5 ∧ acceleratedOrbit 12 1835 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1835 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1835) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1835.1, data_12_1835.2]

/-- Complete interval computation for depth 12, residue 1836. -/
theorem bounds_12_1836 : exactInterval 12 1836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1836 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1836) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1836 : oddCount 1836 12 = 5 ∧ acceleratedOrbit 12 1836 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1836 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1836) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1836.1, data_12_1836.2]

/-- Complete interval computation for depth 12, residue 1837. -/
theorem bounds_12_1837 : exactInterval 12 1837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1837 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1837) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1837 : oddCount 1837 12 = 5 ∧ acceleratedOrbit 12 1837 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1837 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1837) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1837.1, data_12_1837.2]

/-- Complete interval computation for depth 12, residue 1838. -/
theorem bounds_12_1838 : exactInterval 12 1838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1838 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1838) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1838 : oddCount 1838 12 = 5 ∧ acceleratedOrbit 12 1838 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1838 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1838) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1838.1, data_12_1838.2]

/-- Complete interval computation for depth 12, residue 1839. -/
theorem bounds_12_1839 : exactInterval 12 1839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1839 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1839) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1839 : oddCount 1839 12 = 7 ∧ acceleratedOrbit 12 1839 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1839 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1839) = 3 ^ 7 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1839.1, data_12_1839.2]

/-- Complete interval computation for depth 12, residue 1840. -/
theorem bounds_12_1840 : exactInterval 12 1840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1840 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1840) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1840 : oddCount 1840 12 = 4 ∧ acceleratedOrbit 12 1840 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1840 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1840) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1840.1, data_12_1840.2]

/-- Complete interval computation for depth 12, residue 1841. -/
theorem bounds_12_1841 : exactInterval 12 1841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1841 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1841) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1841 : oddCount 1841 12 = 5 ∧ acceleratedOrbit 12 1841 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1841 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1841) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1841.1, data_12_1841.2]

/-- Complete interval computation for depth 12, residue 1842. -/
theorem bounds_12_1842 : exactInterval 12 1842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1842 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1842) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1842 : oddCount 1842 12 = 5 ∧ acceleratedOrbit 12 1842 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1842 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1842) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1842.1, data_12_1842.2]

end Collatz.Research.StoppingAtlas.Batch0320
