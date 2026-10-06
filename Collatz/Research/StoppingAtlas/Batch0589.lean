import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0589

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1863. -/
theorem bounds_13_1863 : exactInterval 13 1863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1863 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1863) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1863 : oddCount 1863 13 = 9 ∧ acceleratedOrbit 13 1863 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1863 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1863) = 3 ^ 9 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1863.1, data_13_1863.2]

/-- Complete interval computation for depth 13, residue 1864. -/
theorem bounds_13_1864 : exactInterval 13 1864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1864 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1864) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1864 : oddCount 1864 13 = 6 ∧ acceleratedOrbit 13 1864 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1864 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1864) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1864.1, data_13_1864.2]

/-- Complete interval computation for depth 13, residue 1865. -/
theorem bounds_13_1865 : exactInterval 13 1865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1865 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1865) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1865 : oddCount 1865 13 = 7 ∧ acceleratedOrbit 13 1865 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1865 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1865) = 3 ^ 7 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1865.1, data_13_1865.2]

/-- Complete interval computation for depth 13, residue 1866. -/
theorem bounds_13_1866 : exactInterval 13 1866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1866 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1866) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1866 : oddCount 1866 13 = 6 ∧ acceleratedOrbit 13 1866 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1866 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1866) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1866.1, data_13_1866.2]

/-- Complete interval computation for depth 13, residue 1867. -/
theorem bounds_13_1867 : exactInterval 13 1867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1867 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1867) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1867 : oddCount 1867 13 = 5 ∧ acceleratedOrbit 13 1867 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1867 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1867) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1867.1, data_13_1867.2]

/-- Complete interval computation for depth 13, residue 1868. -/
theorem bounds_13_1868 : exactInterval 13 1868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1868 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1868) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1868 : oddCount 1868 13 = 6 ∧ acceleratedOrbit 13 1868 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1868 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1868) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1868.1, data_13_1868.2]

/-- Complete interval computation for depth 13, residue 1869. -/
theorem bounds_13_1869 : exactInterval 13 1869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1869 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1869) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1869 : oddCount 1869 13 = 6 ∧ acceleratedOrbit 13 1869 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1869 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1869) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1869.1, data_13_1869.2]

/-- Complete interval computation for depth 13, residue 1870. -/
theorem bounds_13_1870 : exactInterval 13 1870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1870 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1870) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1870 : oddCount 1870 13 = 7 ∧ acceleratedOrbit 13 1870 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1870 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1870) = 3 ^ 7 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1870.1, data_13_1870.2]

/-- Complete interval computation for depth 13, residue 1871. -/
theorem bounds_13_1871 : exactInterval 13 1871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1871 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1871) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1871 : oddCount 1871 13 = 7 ∧ acceleratedOrbit 13 1871 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1871 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1871) = 3 ^ 7 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1871.1, data_13_1871.2]

/-- Complete interval computation for depth 13, residue 1872. -/
theorem bounds_13_1872 : exactInterval 13 1872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1872 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1872) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1872 : oddCount 1872 13 = 4 ∧ acceleratedOrbit 13 1872 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1872 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1872) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1872.1, data_13_1872.2]

/-- Complete interval computation for depth 13, residue 1873. -/
theorem bounds_13_1873 : exactInterval 13 1873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1873 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1873) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1873 : oddCount 1873 13 = 6 ∧ acceleratedOrbit 13 1873 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1873 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1873) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1873.1, data_13_1873.2]

/-- Complete interval computation for depth 13, residue 1874. -/
theorem bounds_13_1874 : exactInterval 13 1874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1874 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1874) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1874 : oddCount 1874 13 = 9 ∧ acceleratedOrbit 13 1874 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1874 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1874) = 3 ^ 9 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1874.1, data_13_1874.2]

/-- Complete interval computation for depth 13, residue 1875. -/
theorem bounds_13_1875 : exactInterval 13 1875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1875 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1875) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1875 : oddCount 1875 13 = 9 ∧ acceleratedOrbit 13 1875 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1875 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1875) = 3 ^ 9 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1875.1, data_13_1875.2]

/-- Complete interval computation for depth 13, residue 1876. -/
theorem bounds_13_1876 : exactInterval 13 1876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1876 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1876) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1876 : oddCount 1876 13 = 4 ∧ acceleratedOrbit 13 1876 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1876 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1876) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1876.1, data_13_1876.2]

/-- Complete interval computation for depth 13, residue 1877. -/
theorem bounds_13_1877 : exactInterval 13 1877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1877 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1877) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1877 : oddCount 1877 13 = 4 ∧ acceleratedOrbit 13 1877 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1877 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1877) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1877.1, data_13_1877.2]

/-- Complete interval computation for depth 13, residue 1878. -/
theorem bounds_13_1878 : exactInterval 13 1878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1878 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1878) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1878 : oddCount 1878 13 = 7 ∧ acceleratedOrbit 13 1878 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1878 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1878) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1878.1, data_13_1878.2]

end Collatz.Research.StoppingAtlas.Batch0589
