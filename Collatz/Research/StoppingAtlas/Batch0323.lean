import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0323

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1873. -/
theorem bounds_12_1873 : exactInterval 12 1873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1873 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1873) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1873 : oddCount 1873 12 = 6 ∧ acceleratedOrbit 12 1873 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1873 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1873) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1873.1, data_12_1873.2]

/-- Complete interval computation for depth 12, residue 1874. -/
theorem bounds_12_1874 : exactInterval 12 1874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1874 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1874) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1874 : oddCount 1874 12 = 8 ∧ acceleratedOrbit 12 1874 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1874 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1874) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1874.1, data_12_1874.2]

/-- Complete interval computation for depth 12, residue 1875. -/
theorem bounds_12_1875 : exactInterval 12 1875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1875 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1875) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1875 : oddCount 1875 12 = 8 ∧ acceleratedOrbit 12 1875 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1875 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1875) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1875.1, data_12_1875.2]

/-- Complete interval computation for depth 12, residue 1876. -/
theorem bounds_12_1876 : exactInterval 12 1876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1876 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1876) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1876 : oddCount 1876 12 = 3 ∧ acceleratedOrbit 12 1876 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1876 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1876) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1876.1, data_12_1876.2]

/-- Complete interval computation for depth 12, residue 1877. -/
theorem bounds_12_1877 : exactInterval 12 1877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1877 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1877) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1877 : oddCount 1877 12 = 3 ∧ acceleratedOrbit 12 1877 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1877 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1877) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1877.1, data_12_1877.2]

/-- Complete interval computation for depth 12, residue 1878. -/
theorem bounds_12_1878 : exactInterval 12 1878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1878 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1878) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1878 : oddCount 1878 12 = 6 ∧ acceleratedOrbit 12 1878 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1878 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1878) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1878.1, data_12_1878.2]

/-- Complete interval computation for depth 12, residue 1879. -/
theorem bounds_12_1879 : exactInterval 12 1879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1879 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1879) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1879 : oddCount 1879 12 = 6 ∧ acceleratedOrbit 12 1879 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1879 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1879) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1879.1, data_12_1879.2]

/-- Complete interval computation for depth 12, residue 1880. -/
theorem bounds_12_1880 : exactInterval 12 1880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1880 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1880) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1880 : oddCount 1880 12 = 6 ∧ acceleratedOrbit 12 1880 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1880 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1880) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1880.1, data_12_1880.2]

/-- Complete interval computation for depth 12, residue 1881. -/
theorem bounds_12_1881 : exactInterval 12 1881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1881 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1881) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1881 : oddCount 1881 12 = 5 ∧ acceleratedOrbit 12 1881 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1881 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1881) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1881.1, data_12_1881.2]

/-- Complete interval computation for depth 12, residue 1882. -/
theorem bounds_12_1882 : exactInterval 12 1882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1882 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1882) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1882 : oddCount 1882 12 = 6 ∧ acceleratedOrbit 12 1882 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1882 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1882) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1882.1, data_12_1882.2]

/-- Complete interval computation for depth 12, residue 1883. -/
theorem bounds_12_1883 : exactInterval 12 1883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1883 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1883) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1883 : oddCount 1883 12 = 8 ∧ acceleratedOrbit 12 1883 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1883 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1883) = 3 ^ 8 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1883.1, data_12_1883.2]

/-- Complete interval computation for depth 12, residue 1884. -/
theorem bounds_12_1884 : exactInterval 12 1884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1884 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1884) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1884 : oddCount 1884 12 = 6 ∧ acceleratedOrbit 12 1884 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1884 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1884) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1884.1, data_12_1884.2]

/-- Complete interval computation for depth 12, residue 1885. -/
theorem bounds_12_1885 : exactInterval 12 1885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1885 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1885) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1885 : oddCount 1885 12 = 6 ∧ acceleratedOrbit 12 1885 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1885 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1885) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1885.1, data_12_1885.2]

/-- Complete interval computation for depth 12, residue 1886. -/
theorem bounds_12_1886 : exactInterval 12 1886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1886 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1886) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1886 : oddCount 1886 12 = 5 ∧ acceleratedOrbit 12 1886 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1886 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1886) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1886.1, data_12_1886.2]

/-- Complete interval computation for depth 12, residue 1887. -/
theorem bounds_12_1887 : exactInterval 12 1887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1887 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1887) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1887 : oddCount 1887 12 = 5 ∧ acceleratedOrbit 12 1887 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1887 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1887) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1887.1, data_12_1887.2]

/-- Complete interval computation for depth 12, residue 1888. -/
theorem bounds_12_1888 : exactInterval 12 1888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1888 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1888) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1888 : oddCount 1888 12 = 4 ∧ acceleratedOrbit 12 1888 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1888 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1888) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1888.1, data_12_1888.2]

end Collatz.Research.StoppingAtlas.Batch0323
