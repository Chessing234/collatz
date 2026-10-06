import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0587

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1832. -/
theorem bounds_13_1832 : exactInterval 13 1832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1832 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1832) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1832 : oddCount 1832 13 = 5 ∧ acceleratedOrbit 13 1832 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1832 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1832) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1832.1, data_13_1832.2]

/-- Complete interval computation for depth 13, residue 1833. -/
theorem bounds_13_1833 : exactInterval 13 1833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1833 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1833) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1833 : oddCount 1833 13 = 7 ∧ acceleratedOrbit 13 1833 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1833 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1833) = 3 ^ 7 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1833.1, data_13_1833.2]

/-- Complete interval computation for depth 13, residue 1834. -/
theorem bounds_13_1834 : exactInterval 13 1834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1834 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1834) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1834 : oddCount 1834 13 = 5 ∧ acceleratedOrbit 13 1834 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1834 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1834) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1834.1, data_13_1834.2]

/-- Complete interval computation for depth 13, residue 1835. -/
theorem bounds_13_1835 : exactInterval 13 1835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1835 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1835) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1835 : oddCount 1835 13 = 6 ∧ acceleratedOrbit 13 1835 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1835 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1835) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1835.1, data_13_1835.2]

/-- Complete interval computation for depth 13, residue 1836. -/
theorem bounds_13_1836 : exactInterval 13 1836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1836 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1836) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1836 : oddCount 1836 13 = 5 ∧ acceleratedOrbit 13 1836 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1836 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1836) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1836.1, data_13_1836.2]

/-- Complete interval computation for depth 13, residue 1837. -/
theorem bounds_13_1837 : exactInterval 13 1837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1837 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1837) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1837 : oddCount 1837 13 = 5 ∧ acceleratedOrbit 13 1837 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1837 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1837) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1837.1, data_13_1837.2]

/-- Complete interval computation for depth 13, residue 1838. -/
theorem bounds_13_1838 : exactInterval 13 1838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1838 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1838) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1838 : oddCount 1838 13 = 5 ∧ acceleratedOrbit 13 1838 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1838 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1838) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1838.1, data_13_1838.2]

/-- Complete interval computation for depth 13, residue 1839. -/
theorem bounds_13_1839 : exactInterval 13 1839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1839 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1839) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1839 : oddCount 1839 13 = 8 ∧ acceleratedOrbit 13 1839 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1839 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1839) = 3 ^ 8 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1839.1, data_13_1839.2]

/-- Complete interval computation for depth 13, residue 1840. -/
theorem bounds_13_1840 : exactInterval 13 1840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1840 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1840) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1840 : oddCount 1840 13 = 5 ∧ acceleratedOrbit 13 1840 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1840 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1840) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1840.1, data_13_1840.2]

/-- Complete interval computation for depth 13, residue 1841. -/
theorem bounds_13_1841 : exactInterval 13 1841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1841 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1841) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1841 : oddCount 1841 13 = 5 ∧ acceleratedOrbit 13 1841 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1841 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1841) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1841.1, data_13_1841.2]

/-- Complete interval computation for depth 13, residue 1842. -/
theorem bounds_13_1842 : exactInterval 13 1842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1842 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1842) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1842 : oddCount 1842 13 = 5 ∧ acceleratedOrbit 13 1842 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1842 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1842) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1842.1, data_13_1842.2]

/-- Complete interval computation for depth 13, residue 1843. -/
theorem bounds_13_1843 : exactInterval 13 1843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1843 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1843) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1843 : oddCount 1843 13 = 5 ∧ acceleratedOrbit 13 1843 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1843 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1843) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1843.1, data_13_1843.2]

/-- Complete interval computation for depth 13, residue 1844. -/
theorem bounds_13_1844 : exactInterval 13 1844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1844 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1844) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1844 : oddCount 1844 13 = 5 ∧ acceleratedOrbit 13 1844 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1844 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1844) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1844.1, data_13_1844.2]

/-- Complete interval computation for depth 13, residue 1845. -/
theorem bounds_13_1845 : exactInterval 13 1845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1845 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1845) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1845 : oddCount 1845 13 = 5 ∧ acceleratedOrbit 13 1845 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1845 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1845) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1845.1, data_13_1845.2]

/-- Complete interval computation for depth 13, residue 1846. -/
theorem bounds_13_1846 : exactInterval 13 1846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1846 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1846) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1846 : oddCount 1846 13 = 7 ∧ acceleratedOrbit 13 1846 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1846 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1846) = 3 ^ 7 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1846.1, data_13_1846.2]

/-- Complete interval computation for depth 13, residue 1847. -/
theorem bounds_13_1847 : exactInterval 13 1847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1847 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1847) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1847 : oddCount 1847 13 = 7 ∧ acceleratedOrbit 13 1847 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1847 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1847) = 3 ^ 7 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1847.1, data_13_1847.2]

end Collatz.Research.StoppingAtlas.Batch0587
