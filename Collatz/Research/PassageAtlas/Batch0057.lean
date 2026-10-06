import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0057

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1835. -/
theorem bounds_15_1835 : exactInterval 15 1835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1835 : oddCount 1835 15 = 6 ∧ acceleratedOrbit 15 1835 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1835) = 3 ^ 6 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1835.1, data_15_1835.2]

/-- Complete interval computation for depth 15, residue 1836. -/
theorem bounds_15_1836 : exactInterval 15 1836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1836 : oddCount 1836 15 = 7 ∧ acceleratedOrbit 15 1836 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1836) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1836.1, data_15_1836.2]

/-- Complete interval computation for depth 15, residue 1837. -/
theorem bounds_15_1837 : exactInterval 15 1837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1837 : oddCount 1837 15 = 7 ∧ acceleratedOrbit 15 1837 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1837) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1837.1, data_15_1837.2]

/-- Complete interval computation for depth 15, residue 1838. -/
theorem bounds_15_1838 : exactInterval 15 1838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1838 : oddCount 1838 15 = 7 ∧ acceleratedOrbit 15 1838 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1838) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1838.1, data_15_1838.2]

/-- Complete interval computation for depth 15, residue 1839. -/
theorem bounds_15_1839 : exactInterval 15 1839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1839 : oddCount 1839 15 = 10 ∧ acceleratedOrbit 15 1839 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1839) = 3 ^ 10 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1839.1, data_15_1839.2]

/-- Complete interval computation for depth 15, residue 1840. -/
theorem bounds_15_1840 : exactInterval 15 1840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1840 : oddCount 1840 15 = 5 ∧ acceleratedOrbit 15 1840 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1840) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1840.1, data_15_1840.2]

/-- Complete interval computation for depth 15, residue 1841. -/
theorem bounds_15_1841 : exactInterval 15 1841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1841 : oddCount 1841 15 = 7 ∧ acceleratedOrbit 15 1841 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1841) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1841.1, data_15_1841.2]

/-- Complete interval computation for depth 15, residue 1842. -/
theorem bounds_15_1842 : exactInterval 15 1842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1842 : oddCount 1842 15 = 7 ∧ acceleratedOrbit 15 1842 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1842) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1842.1, data_15_1842.2]

/-- Complete interval computation for depth 15, residue 1843. -/
theorem bounds_15_1843 : exactInterval 15 1843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1843 : oddCount 1843 15 = 7 ∧ acceleratedOrbit 15 1843 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1843) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1843.1, data_15_1843.2]

/-- Complete interval computation for depth 15, residue 1844. -/
theorem bounds_15_1844 : exactInterval 15 1844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1844 : oddCount 1844 15 = 5 ∧ acceleratedOrbit 15 1844 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1844) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1844.1, data_15_1844.2]

/-- Complete interval computation for depth 15, residue 1845. -/
theorem bounds_15_1845 : exactInterval 15 1845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1845 : oddCount 1845 15 = 5 ∧ acceleratedOrbit 15 1845 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1845) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1845.1, data_15_1845.2]

/-- Complete interval computation for depth 15, residue 1846. -/
theorem bounds_15_1846 : exactInterval 15 1846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1846 : oddCount 1846 15 = 8 ∧ acceleratedOrbit 15 1846 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1846) = 3 ^ 8 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1846.1, data_15_1846.2]

/-- Complete interval computation for depth 15, residue 1847. -/
theorem bounds_15_1847 : exactInterval 15 1847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1847 : oddCount 1847 15 = 8 ∧ acceleratedOrbit 15 1847 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1847) = 3 ^ 8 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1847.1, data_15_1847.2]

/-- Complete interval computation for depth 15, residue 1848. -/
theorem bounds_15_1848 : exactInterval 15 1848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1848 : oddCount 1848 15 = 7 ∧ acceleratedOrbit 15 1848 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1848) = 3 ^ 7 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1848.1, data_15_1848.2]

/-- Complete interval computation for depth 15, residue 1849. -/
theorem bounds_15_1849 : exactInterval 15 1849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1849 : oddCount 1849 15 = 8 ∧ acceleratedOrbit 15 1849 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1849) = 3 ^ 8 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1849.1, data_15_1849.2]

/-- Complete interval computation for depth 15, residue 1850. -/
theorem bounds_15_1850 : exactInterval 15 1850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1850 : oddCount 1850 15 = 7 ∧ acceleratedOrbit 15 1850 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1850) = 3 ^ 7 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1850.1, data_15_1850.2]

/-- Complete interval computation for depth 15, residue 1851. -/
theorem bounds_15_1851 : exactInterval 15 1851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1851 : oddCount 1851 15 = 7 ∧ acceleratedOrbit 15 1851 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1851) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1851.1, data_15_1851.2]

/-- Complete interval computation for depth 15, residue 1852. -/
theorem bounds_15_1852 : exactInterval 15 1852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1852 : oddCount 1852 15 = 7 ∧ acceleratedOrbit 15 1852 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1852) = 3 ^ 7 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1852.1, data_15_1852.2]

/-- Complete interval computation for depth 15, residue 1853. -/
theorem bounds_15_1853 : exactInterval 15 1853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1853 : oddCount 1853 15 = 7 ∧ acceleratedOrbit 15 1853 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1853) = 3 ^ 7 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1853.1, data_15_1853.2]

/-- Complete interval computation for depth 15, residue 1854. -/
theorem bounds_15_1854 : exactInterval 15 1854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1854 : oddCount 1854 15 = 10 ∧ acceleratedOrbit 15 1854 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1854) = 3 ^ 10 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1854.1, data_15_1854.2]

/-- Complete interval computation for depth 15, residue 1855. -/
theorem bounds_15_1855 : exactInterval 15 1855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1855 : oddCount 1855 15 = 10 ∧ acceleratedOrbit 15 1855 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1855) = 3 ^ 10 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1855.1, data_15_1855.2]

/-- Complete interval computation for depth 15, residue 1856. -/
theorem bounds_15_1856 : exactInterval 15 1856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1856 : oddCount 1856 15 = 4 ∧ acceleratedOrbit 15 1856 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1856) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1856.1, data_15_1856.2]

/-- Complete interval computation for depth 15, residue 1857. -/
theorem bounds_15_1857 : exactInterval 15 1857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1857 : oddCount 1857 15 = 5 ∧ acceleratedOrbit 15 1857 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1857) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1857.1, data_15_1857.2]

/-- Complete interval computation for depth 15, residue 1858. -/
theorem bounds_15_1858 : exactInterval 15 1858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1858 : oddCount 1858 15 = 7 ∧ acceleratedOrbit 15 1858 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1858) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1858.1, data_15_1858.2]

/-- Complete interval computation for depth 15, residue 1859. -/
theorem bounds_15_1859 : exactInterval 15 1859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1859 : oddCount 1859 15 = 7 ∧ acceleratedOrbit 15 1859 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1859) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1859.1, data_15_1859.2]

/-- Complete interval computation for depth 15, residue 1860. -/
theorem bounds_15_1860 : exactInterval 15 1860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1860 : oddCount 1860 15 = 5 ∧ acceleratedOrbit 15 1860 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1860) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1860.1, data_15_1860.2]

/-- Complete interval computation for depth 15, residue 1861. -/
theorem bounds_15_1861 : exactInterval 15 1861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1861 : oddCount 1861 15 = 5 ∧ acceleratedOrbit 15 1861 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1861) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1861.1, data_15_1861.2]

/-- Complete interval computation for depth 15, residue 1862. -/
theorem bounds_15_1862 : exactInterval 15 1862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1862 : oddCount 1862 15 = 5 ∧ acceleratedOrbit 15 1862 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1862) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1862.1, data_15_1862.2]

/-- Complete interval computation for depth 15, residue 1863. -/
theorem bounds_15_1863 : exactInterval 15 1863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1863 : oddCount 1863 15 = 10 ∧ acceleratedOrbit 15 1863 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1863) = 3 ^ 10 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1863.1, data_15_1863.2]

/-- Complete interval computation for depth 15, residue 1864. -/
theorem bounds_15_1864 : exactInterval 15 1864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1864 : oddCount 1864 15 = 8 ∧ acceleratedOrbit 15 1864 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1864) = 3 ^ 8 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1864.1, data_15_1864.2]

/-- Complete interval computation for depth 15, residue 1865. -/
theorem bounds_15_1865 : exactInterval 15 1865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1865 : oddCount 1865 15 = 9 ∧ acceleratedOrbit 15 1865 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1865) = 3 ^ 9 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1865.1, data_15_1865.2]

/-- Complete interval computation for depth 15, residue 1866. -/
theorem bounds_15_1866 : exactInterval 15 1866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1866 : oddCount 1866 15 = 8 ∧ acceleratedOrbit 15 1866 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1866) = 3 ^ 8 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1866.1, data_15_1866.2]

end Collatz.Research.PassageAtlas.Batch0057
