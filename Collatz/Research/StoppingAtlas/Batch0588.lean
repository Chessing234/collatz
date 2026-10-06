import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0588

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1848. -/
theorem bounds_13_1848 : exactInterval 13 1848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1848 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1848) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1848 : oddCount 1848 13 = 7 ∧ acceleratedOrbit 13 1848 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1848 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1848) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1848.1, data_13_1848.2]

/-- Complete interval computation for depth 13, residue 1849. -/
theorem bounds_13_1849 : exactInterval 13 1849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1849 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1849) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1849 : oddCount 1849 13 = 8 ∧ acceleratedOrbit 13 1849 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1849 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1849) = 3 ^ 8 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1849.1, data_13_1849.2]

/-- Complete interval computation for depth 13, residue 1850. -/
theorem bounds_13_1850 : exactInterval 13 1850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1850 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1850) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1850 : oddCount 1850 13 = 7 ∧ acceleratedOrbit 13 1850 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1850 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1850) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1850.1, data_13_1850.2]

/-- Complete interval computation for depth 13, residue 1851. -/
theorem bounds_13_1851 : exactInterval 13 1851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1851 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1851) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1851 : oddCount 1851 13 = 5 ∧ acceleratedOrbit 13 1851 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1851 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1851) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1851.1, data_13_1851.2]

/-- Complete interval computation for depth 13, residue 1852. -/
theorem bounds_13_1852 : exactInterval 13 1852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1852 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1852) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1852 : oddCount 1852 13 = 7 ∧ acceleratedOrbit 13 1852 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1852 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1852) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1852.1, data_13_1852.2]

/-- Complete interval computation for depth 13, residue 1853. -/
theorem bounds_13_1853 : exactInterval 13 1853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1853 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1853) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1853 : oddCount 1853 13 = 7 ∧ acceleratedOrbit 13 1853 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1853 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1853) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1853.1, data_13_1853.2]

/-- Complete interval computation for depth 13, residue 1854. -/
theorem bounds_13_1854 : exactInterval 13 1854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1854 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1854) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1854 : oddCount 1854 13 = 8 ∧ acceleratedOrbit 13 1854 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1854 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1854) = 3 ^ 8 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1854.1, data_13_1854.2]

/-- Complete interval computation for depth 13, residue 1855. -/
theorem bounds_13_1855 : exactInterval 13 1855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1855 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1855) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1855 : oddCount 1855 13 = 8 ∧ acceleratedOrbit 13 1855 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1855 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1855) = 3 ^ 8 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1855.1, data_13_1855.2]

/-- Complete interval computation for depth 13, residue 1856. -/
theorem bounds_13_1856 : exactInterval 13 1856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1856 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1856) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1856 : oddCount 1856 13 = 4 ∧ acceleratedOrbit 13 1856 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1856 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1856) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1856.1, data_13_1856.2]

/-- Complete interval computation for depth 13, residue 1857. -/
theorem bounds_13_1857 : exactInterval 13 1857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1857 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1857) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1857 : oddCount 1857 13 = 5 ∧ acceleratedOrbit 13 1857 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1857 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1857) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1857.1, data_13_1857.2]

/-- Complete interval computation for depth 13, residue 1858. -/
theorem bounds_13_1858 : exactInterval 13 1858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1858 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1858) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1858 : oddCount 1858 13 = 6 ∧ acceleratedOrbit 13 1858 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1858 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1858) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1858.1, data_13_1858.2]

/-- Complete interval computation for depth 13, residue 1859. -/
theorem bounds_13_1859 : exactInterval 13 1859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1859 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1859) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1859 : oddCount 1859 13 = 6 ∧ acceleratedOrbit 13 1859 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1859 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1859) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1859.1, data_13_1859.2]

/-- Complete interval computation for depth 13, residue 1860. -/
theorem bounds_13_1860 : exactInterval 13 1860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1860 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1860) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1860 : oddCount 1860 13 = 5 ∧ acceleratedOrbit 13 1860 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1860 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1860) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1860.1, data_13_1860.2]

/-- Complete interval computation for depth 13, residue 1861. -/
theorem bounds_13_1861 : exactInterval 13 1861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1861 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1861) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1861 : oddCount 1861 13 = 5 ∧ acceleratedOrbit 13 1861 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1861 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1861) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1861.1, data_13_1861.2]

/-- Complete interval computation for depth 13, residue 1862. -/
theorem bounds_13_1862 : exactInterval 13 1862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1862 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1862) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1862 : oddCount 1862 13 = 5 ∧ acceleratedOrbit 13 1862 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1862 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1862) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1862.1, data_13_1862.2]

end Collatz.Research.StoppingAtlas.Batch0588
