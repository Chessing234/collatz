import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0321

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1843. -/
theorem bounds_12_1843 : exactInterval 12 1843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1843 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1843) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1843 : oddCount 1843 12 = 5 ∧ acceleratedOrbit 12 1843 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1843 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1843) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1843.1, data_12_1843.2]

/-- Complete interval computation for depth 12, residue 1844. -/
theorem bounds_12_1844 : exactInterval 12 1844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1844 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1844) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1844 : oddCount 1844 12 = 4 ∧ acceleratedOrbit 12 1844 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1844 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1844) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1844.1, data_12_1844.2]

/-- Complete interval computation for depth 12, residue 1845. -/
theorem bounds_12_1845 : exactInterval 12 1845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1845 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1845) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1845 : oddCount 1845 12 = 4 ∧ acceleratedOrbit 12 1845 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1845 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1845) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1845.1, data_12_1845.2]

/-- Complete interval computation for depth 12, residue 1846. -/
theorem bounds_12_1846 : exactInterval 12 1846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1846 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1846) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1846 : oddCount 1846 12 = 6 ∧ acceleratedOrbit 12 1846 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1846 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1846) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1846.1, data_12_1846.2]

/-- Complete interval computation for depth 12, residue 1847. -/
theorem bounds_12_1847 : exactInterval 12 1847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1847 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1847) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1847 : oddCount 1847 12 = 6 ∧ acceleratedOrbit 12 1847 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1847 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1847) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1847.1, data_12_1847.2]

/-- Complete interval computation for depth 12, residue 1848. -/
theorem bounds_12_1848 : exactInterval 12 1848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1848 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1848) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1848 : oddCount 1848 12 = 7 ∧ acceleratedOrbit 12 1848 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1848 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1848) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1848.1, data_12_1848.2]

/-- Complete interval computation for depth 12, residue 1849. -/
theorem bounds_12_1849 : exactInterval 12 1849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1849 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1849) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1849 : oddCount 1849 12 = 7 ∧ acceleratedOrbit 12 1849 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1849 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1849) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1849.1, data_12_1849.2]

/-- Complete interval computation for depth 12, residue 1850. -/
theorem bounds_12_1850 : exactInterval 12 1850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1850 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1850) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1850 : oddCount 1850 12 = 7 ∧ acceleratedOrbit 12 1850 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1850 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1850) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1850.1, data_12_1850.2]

/-- Complete interval computation for depth 12, residue 1851. -/
theorem bounds_12_1851 : exactInterval 12 1851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1851 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1851) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1851 : oddCount 1851 12 = 5 ∧ acceleratedOrbit 12 1851 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1851 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1851) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1851.1, data_12_1851.2]

/-- Complete interval computation for depth 12, residue 1852. -/
theorem bounds_12_1852 : exactInterval 12 1852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1852 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1852) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1852 : oddCount 1852 12 = 7 ∧ acceleratedOrbit 12 1852 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1852 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1852) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1852.1, data_12_1852.2]

/-- Complete interval computation for depth 12, residue 1853. -/
theorem bounds_12_1853 : exactInterval 12 1853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1853 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1853) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1853 : oddCount 1853 12 = 7 ∧ acceleratedOrbit 12 1853 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1853 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1853) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1853.1, data_12_1853.2]

/-- Complete interval computation for depth 12, residue 1854. -/
theorem bounds_12_1854 : exactInterval 12 1854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1854 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1854) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1854 : oddCount 1854 12 = 7 ∧ acceleratedOrbit 12 1854 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1854 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1854) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1854.1, data_12_1854.2]

/-- Complete interval computation for depth 12, residue 1855. -/
theorem bounds_12_1855 : exactInterval 12 1855 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1855 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1855) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1855 : oddCount 1855 12 = 7 ∧ acceleratedOrbit 12 1855 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1855 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1855) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1855.1, data_12_1855.2]

/-- Complete interval computation for depth 12, residue 1856. -/
theorem bounds_12_1856 : exactInterval 12 1856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1856 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1856) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1856 : oddCount 1856 12 = 3 ∧ acceleratedOrbit 12 1856 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1856 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1856) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1856.1, data_12_1856.2]

/-- Complete interval computation for depth 12, residue 1857. -/
theorem bounds_12_1857 : exactInterval 12 1857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1857 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1857) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1857 : oddCount 1857 12 = 4 ∧ acceleratedOrbit 12 1857 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1857 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1857) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1857.1, data_12_1857.2]

end Collatz.Research.StoppingAtlas.Batch0321
