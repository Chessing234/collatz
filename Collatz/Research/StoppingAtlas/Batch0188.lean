import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0188

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1848. -/
theorem bounds_11_1848 : exactInterval 11 1848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1848 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1848) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1848 : oddCount 1848 11 = 6 ∧ acceleratedOrbit 11 1848 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1848 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1848) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1848.1, data_11_1848.2]

/-- Complete interval computation for depth 11, residue 1849. -/
theorem bounds_11_1849 : exactInterval 11 1849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1849 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1849) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1849 : oddCount 1849 11 = 6 ∧ acceleratedOrbit 11 1849 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1849 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1849) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1849.1, data_11_1849.2]

/-- Complete interval computation for depth 11, residue 1850. -/
theorem bounds_11_1850 : exactInterval 11 1850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1850 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1850) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1850 : oddCount 1850 11 = 6 ∧ acceleratedOrbit 11 1850 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1850 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1850) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1850.1, data_11_1850.2]

/-- Complete interval computation for depth 11, residue 1851. -/
theorem bounds_11_1851 : exactInterval 11 1851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1851 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1851) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1851 : oddCount 1851 11 = 5 ∧ acceleratedOrbit 11 1851 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1851 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1851) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1851.1, data_11_1851.2]

/-- Complete interval computation for depth 11, residue 1852. -/
theorem bounds_11_1852 : exactInterval 11 1852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1852 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1852) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1852 : oddCount 1852 11 = 6 ∧ acceleratedOrbit 11 1852 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1852 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1852) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1852.1, data_11_1852.2]

/-- Complete interval computation for depth 11, residue 1853. -/
theorem bounds_11_1853 : exactInterval 11 1853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1853 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1853) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1853 : oddCount 1853 11 = 6 ∧ acceleratedOrbit 11 1853 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1853 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1853) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1853.1, data_11_1853.2]

/-- Complete interval computation for depth 11, residue 1854. -/
theorem bounds_11_1854 : exactInterval 11 1854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1854 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1854) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1854 : oddCount 1854 11 = 7 ∧ acceleratedOrbit 11 1854 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1854 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1854) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1854.1, data_11_1854.2]

/-- Complete interval computation for depth 11, residue 1855. -/
theorem bounds_11_1855 : exactInterval 11 1855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1855 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1855) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1855 : oddCount 1855 11 = 7 ∧ acceleratedOrbit 11 1855 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1855 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1855) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1855.1, data_11_1855.2]

/-- Complete interval computation for depth 11, residue 1856. -/
theorem bounds_11_1856 : exactInterval 11 1856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1856 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1856) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1856 : oddCount 1856 11 = 3 ∧ acceleratedOrbit 11 1856 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1856 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1856) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1856.1, data_11_1856.2]

/-- Complete interval computation for depth 11, residue 1857. -/
theorem bounds_11_1857 : exactInterval 11 1857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1857 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1857) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1857 : oddCount 1857 11 = 4 ∧ acceleratedOrbit 11 1857 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1857 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1857) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1857.1, data_11_1857.2]

/-- Complete interval computation for depth 11, residue 1858. -/
theorem bounds_11_1858 : exactInterval 11 1858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1858 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1858) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1858 : oddCount 1858 11 = 5 ∧ acceleratedOrbit 11 1858 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1858 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1858) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1858.1, data_11_1858.2]

/-- Complete interval computation for depth 11, residue 1859. -/
theorem bounds_11_1859 : exactInterval 11 1859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1859 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1859) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1859 : oddCount 1859 11 = 5 ∧ acceleratedOrbit 11 1859 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1859 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1859) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1859.1, data_11_1859.2]

/-- Complete interval computation for depth 11, residue 1860. -/
theorem bounds_11_1860 : exactInterval 11 1860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1860 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1860) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1860 : oddCount 1860 11 = 4 ∧ acceleratedOrbit 11 1860 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1860 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1860) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1860.1, data_11_1860.2]

/-- Complete interval computation for depth 11, residue 1861. -/
theorem bounds_11_1861 : exactInterval 11 1861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1861 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1861) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1861 : oddCount 1861 11 = 4 ∧ acceleratedOrbit 11 1861 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1861 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1861) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1861.1, data_11_1861.2]

/-- Complete interval computation for depth 11, residue 1862. -/
theorem bounds_11_1862 : exactInterval 11 1862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1862 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1862) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1862 : oddCount 1862 11 = 4 ∧ acceleratedOrbit 11 1862 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1862 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1862) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1862.1, data_11_1862.2]

end Collatz.Research.StoppingAtlas.Batch0188
