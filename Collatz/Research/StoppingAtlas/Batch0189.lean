import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0189

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1863. -/
theorem bounds_11_1863 : exactInterval 11 1863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1863 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1863) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1863 : oddCount 1863 11 = 7 ∧ acceleratedOrbit 11 1863 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1863 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1863) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1863.1, data_11_1863.2]

/-- Complete interval computation for depth 11, residue 1864. -/
theorem bounds_11_1864 : exactInterval 11 1864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1864 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1864) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1864 : oddCount 1864 11 = 6 ∧ acceleratedOrbit 11 1864 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1864 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1864) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1864.1, data_11_1864.2]

/-- Complete interval computation for depth 11, residue 1865. -/
theorem bounds_11_1865 : exactInterval 11 1865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1865 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1865) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1865 : oddCount 1865 11 = 6 ∧ acceleratedOrbit 11 1865 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1865 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1865) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1865.1, data_11_1865.2]

/-- Complete interval computation for depth 11, residue 1866. -/
theorem bounds_11_1866 : exactInterval 11 1866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1866 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1866) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1866 : oddCount 1866 11 = 6 ∧ acceleratedOrbit 11 1866 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1866 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1866) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1866.1, data_11_1866.2]

/-- Complete interval computation for depth 11, residue 1867. -/
theorem bounds_11_1867 : exactInterval 11 1867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1867 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1867) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1867 : oddCount 1867 11 = 4 ∧ acceleratedOrbit 11 1867 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1867 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1867) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1867.1, data_11_1867.2]

/-- Complete interval computation for depth 11, residue 1868. -/
theorem bounds_11_1868 : exactInterval 11 1868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1868 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1868) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1868 : oddCount 1868 11 = 6 ∧ acceleratedOrbit 11 1868 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1868 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1868) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1868.1, data_11_1868.2]

/-- Complete interval computation for depth 11, residue 1869. -/
theorem bounds_11_1869 : exactInterval 11 1869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1869 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1869) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1869 : oddCount 1869 11 = 6 ∧ acceleratedOrbit 11 1869 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1869 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1869) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1869.1, data_11_1869.2]

/-- Complete interval computation for depth 11, residue 1870. -/
theorem bounds_11_1870 : exactInterval 11 1870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1870 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1870) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1870 : oddCount 1870 11 = 7 ∧ acceleratedOrbit 11 1870 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1870 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1870) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1870.1, data_11_1870.2]

/-- Complete interval computation for depth 11, residue 1871. -/
theorem bounds_11_1871 : exactInterval 11 1871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1871 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1871) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1871 : oddCount 1871 11 = 7 ∧ acceleratedOrbit 11 1871 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1871 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1871) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1871.1, data_11_1871.2]

/-- Complete interval computation for depth 11, residue 1872. -/
theorem bounds_11_1872 : exactInterval 11 1872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1872 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1872) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1872 : oddCount 1872 11 = 3 ∧ acceleratedOrbit 11 1872 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1872 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1872) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1872.1, data_11_1872.2]

/-- Complete interval computation for depth 11, residue 1873. -/
theorem bounds_11_1873 : exactInterval 11 1873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1873 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1873) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1873 : oddCount 1873 11 = 6 ∧ acceleratedOrbit 11 1873 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1873 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1873) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1873.1, data_11_1873.2]

/-- Complete interval computation for depth 11, residue 1874. -/
theorem bounds_11_1874 : exactInterval 11 1874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1874 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1874) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1874 : oddCount 1874 11 = 8 ∧ acceleratedOrbit 11 1874 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1874 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1874) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1874.1, data_11_1874.2]

/-- Complete interval computation for depth 11, residue 1875. -/
theorem bounds_11_1875 : exactInterval 11 1875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1875 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1875) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1875 : oddCount 1875 11 = 8 ∧ acceleratedOrbit 11 1875 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1875 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1875) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1875.1, data_11_1875.2]

/-- Complete interval computation for depth 11, residue 1876. -/
theorem bounds_11_1876 : exactInterval 11 1876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1876 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1876) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1876 : oddCount 1876 11 = 3 ∧ acceleratedOrbit 11 1876 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1876 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1876) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1876.1, data_11_1876.2]

/-- Complete interval computation for depth 11, residue 1877. -/
theorem bounds_11_1877 : exactInterval 11 1877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1877 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1877) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1877 : oddCount 1877 11 = 3 ∧ acceleratedOrbit 11 1877 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1877 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1877) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1877.1, data_11_1877.2]

/-- Complete interval computation for depth 11, residue 1878. -/
theorem bounds_11_1878 : exactInterval 11 1878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1878 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1878) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1878 : oddCount 1878 11 = 6 ∧ acceleratedOrbit 11 1878 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1878 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1878) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1878.1, data_11_1878.2]

end Collatz.Research.StoppingAtlas.Batch0189
