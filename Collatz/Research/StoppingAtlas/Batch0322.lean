import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0322

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1858. -/
theorem bounds_12_1858 : exactInterval 12 1858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1858 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1858) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1858 : oddCount 1858 12 = 6 ∧ acceleratedOrbit 12 1858 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1858 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1858) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1858.1, data_12_1858.2]

/-- Complete interval computation for depth 12, residue 1859. -/
theorem bounds_12_1859 : exactInterval 12 1859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1859 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1859) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1859 : oddCount 1859 12 = 6 ∧ acceleratedOrbit 12 1859 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1859 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1859) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1859.1, data_12_1859.2]

/-- Complete interval computation for depth 12, residue 1860. -/
theorem bounds_12_1860 : exactInterval 12 1860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1860 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1860) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1860 : oddCount 1860 12 = 4 ∧ acceleratedOrbit 12 1860 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1860 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1860) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1860.1, data_12_1860.2]

/-- Complete interval computation for depth 12, residue 1861. -/
theorem bounds_12_1861 : exactInterval 12 1861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1861 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1861) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1861 : oddCount 1861 12 = 4 ∧ acceleratedOrbit 12 1861 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1861 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1861) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1861.1, data_12_1861.2]

/-- Complete interval computation for depth 12, residue 1862. -/
theorem bounds_12_1862 : exactInterval 12 1862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1862 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1862) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1862 : oddCount 1862 12 = 4 ∧ acceleratedOrbit 12 1862 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1862 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1862) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1862.1, data_12_1862.2]

/-- Complete interval computation for depth 12, residue 1863. -/
theorem bounds_12_1863 : exactInterval 12 1863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1863 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1863) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1863 : oddCount 1863 12 = 8 ∧ acceleratedOrbit 12 1863 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1863 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1863) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1863.1, data_12_1863.2]

/-- Complete interval computation for depth 12, residue 1864. -/
theorem bounds_12_1864 : exactInterval 12 1864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1864 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1864) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1864 : oddCount 1864 12 = 6 ∧ acceleratedOrbit 12 1864 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1864 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1864) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1864.1, data_12_1864.2]

/-- Complete interval computation for depth 12, residue 1865. -/
theorem bounds_12_1865 : exactInterval 12 1865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1865 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1865) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1865 : oddCount 1865 12 = 7 ∧ acceleratedOrbit 12 1865 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1865 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1865) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1865.1, data_12_1865.2]

/-- Complete interval computation for depth 12, residue 1866. -/
theorem bounds_12_1866 : exactInterval 12 1866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1866 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1866) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1866 : oddCount 1866 12 = 6 ∧ acceleratedOrbit 12 1866 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1866 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1866) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1866.1, data_12_1866.2]

/-- Complete interval computation for depth 12, residue 1867. -/
theorem bounds_12_1867 : exactInterval 12 1867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1867 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1867) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1867 : oddCount 1867 12 = 4 ∧ acceleratedOrbit 12 1867 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1867 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1867) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1867.1, data_12_1867.2]

/-- Complete interval computation for depth 12, residue 1868. -/
theorem bounds_12_1868 : exactInterval 12 1868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1868 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1868) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1868 : oddCount 1868 12 = 6 ∧ acceleratedOrbit 12 1868 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1868 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1868) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1868.1, data_12_1868.2]

/-- Complete interval computation for depth 12, residue 1869. -/
theorem bounds_12_1869 : exactInterval 12 1869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1869 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1869) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1869 : oddCount 1869 12 = 6 ∧ acceleratedOrbit 12 1869 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1869 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1869) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1869.1, data_12_1869.2]

/-- Complete interval computation for depth 12, residue 1870. -/
theorem bounds_12_1870 : exactInterval 12 1870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1870 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1870) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1870 : oddCount 1870 12 = 7 ∧ acceleratedOrbit 12 1870 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1870 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1870) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1870.1, data_12_1870.2]

/-- Complete interval computation for depth 12, residue 1871. -/
theorem bounds_12_1871 : exactInterval 12 1871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1871 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1871) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1871 : oddCount 1871 12 = 7 ∧ acceleratedOrbit 12 1871 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1871 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1871) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1871.1, data_12_1871.2]

/-- Complete interval computation for depth 12, residue 1872. -/
theorem bounds_12_1872 : exactInterval 12 1872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1872 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1872) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1872 : oddCount 1872 12 = 3 ∧ acceleratedOrbit 12 1872 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1872 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1872) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1872.1, data_12_1872.2]

end Collatz.Research.StoppingAtlas.Batch0322
