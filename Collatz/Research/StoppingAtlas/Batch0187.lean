import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0187

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1832. -/
theorem bounds_11_1832 : exactInterval 11 1832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1832 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1832) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1832 : oddCount 1832 11 = 4 ∧ acceleratedOrbit 11 1832 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1832 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1832) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1832.1, data_11_1832.2]

/-- Complete interval computation for depth 11, residue 1833. -/
theorem bounds_11_1833 : exactInterval 11 1833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1833 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1833) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1833 : oddCount 1833 11 = 6 ∧ acceleratedOrbit 11 1833 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1833 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1833) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1833.1, data_11_1833.2]

/-- Complete interval computation for depth 11, residue 1834. -/
theorem bounds_11_1834 : exactInterval 11 1834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1834 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1834) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1834 : oddCount 1834 11 = 4 ∧ acceleratedOrbit 11 1834 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1834 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1834) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1834.1, data_11_1834.2]

/-- Complete interval computation for depth 11, residue 1835. -/
theorem bounds_11_1835 : exactInterval 11 1835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1835 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1835) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1835 : oddCount 1835 11 = 5 ∧ acceleratedOrbit 11 1835 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1835 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1835) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1835.1, data_11_1835.2]

/-- Complete interval computation for depth 11, residue 1836. -/
theorem bounds_11_1836 : exactInterval 11 1836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1836 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1836) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1836 : oddCount 1836 11 = 4 ∧ acceleratedOrbit 11 1836 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1836 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1836) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1836.1, data_11_1836.2]

/-- Complete interval computation for depth 11, residue 1837. -/
theorem bounds_11_1837 : exactInterval 11 1837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1837 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1837) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1837 : oddCount 1837 11 = 4 ∧ acceleratedOrbit 11 1837 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1837 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1837) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1837.1, data_11_1837.2]

/-- Complete interval computation for depth 11, residue 1838. -/
theorem bounds_11_1838 : exactInterval 11 1838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1838 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1838) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1838 : oddCount 1838 11 = 4 ∧ acceleratedOrbit 11 1838 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1838 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1838) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1838.1, data_11_1838.2]

/-- Complete interval computation for depth 11, residue 1839. -/
theorem bounds_11_1839 : exactInterval 11 1839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1839 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1839) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1839 : oddCount 1839 11 = 6 ∧ acceleratedOrbit 11 1839 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1839 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1839) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1839.1, data_11_1839.2]

/-- Complete interval computation for depth 11, residue 1840. -/
theorem bounds_11_1840 : exactInterval 11 1840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1840 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1840) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1840 : oddCount 1840 11 = 4 ∧ acceleratedOrbit 11 1840 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1840 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1840) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1840.1, data_11_1840.2]

/-- Complete interval computation for depth 11, residue 1841. -/
theorem bounds_11_1841 : exactInterval 11 1841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1841 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1841) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1841 : oddCount 1841 11 = 4 ∧ acceleratedOrbit 11 1841 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1841 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1841) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1841.1, data_11_1841.2]

/-- Complete interval computation for depth 11, residue 1842. -/
theorem bounds_11_1842 : exactInterval 11 1842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1842 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1842) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1842 : oddCount 1842 11 = 4 ∧ acceleratedOrbit 11 1842 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1842 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1842) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1842.1, data_11_1842.2]

/-- Complete interval computation for depth 11, residue 1843. -/
theorem bounds_11_1843 : exactInterval 11 1843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1843 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1843) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1843 : oddCount 1843 11 = 4 ∧ acceleratedOrbit 11 1843 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1843 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1843) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1843.1, data_11_1843.2]

/-- Complete interval computation for depth 11, residue 1844. -/
theorem bounds_11_1844 : exactInterval 11 1844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1844 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1844) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1844 : oddCount 1844 11 = 4 ∧ acceleratedOrbit 11 1844 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1844 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1844) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1844.1, data_11_1844.2]

/-- Complete interval computation for depth 11, residue 1845. -/
theorem bounds_11_1845 : exactInterval 11 1845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1845 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1845) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1845 : oddCount 1845 11 = 4 ∧ acceleratedOrbit 11 1845 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1845 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1845) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1845.1, data_11_1845.2]

/-- Complete interval computation for depth 11, residue 1846. -/
theorem bounds_11_1846 : exactInterval 11 1846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1846 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1846) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1846 : oddCount 1846 11 = 6 ∧ acceleratedOrbit 11 1846 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1846 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1846) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1846.1, data_11_1846.2]

/-- Complete interval computation for depth 11, residue 1847. -/
theorem bounds_11_1847 : exactInterval 11 1847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1847 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1847) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1847 : oddCount 1847 11 = 6 ∧ acceleratedOrbit 11 1847 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1847 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1847) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1847.1, data_11_1847.2]

end Collatz.Research.StoppingAtlas.Batch0187
