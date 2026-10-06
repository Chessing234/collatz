import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0058

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1867. -/
theorem bounds_15_1867 : exactInterval 15 1867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1867 : oddCount 1867 15 = 5 ∧ acceleratedOrbit 15 1867 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1867) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1867.1, data_15_1867.2]

/-- Complete interval computation for depth 15, residue 1868. -/
theorem bounds_15_1868 : exactInterval 15 1868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1868 : oddCount 1868 15 = 8 ∧ acceleratedOrbit 15 1868 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1868) = 3 ^ 8 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1868.1, data_15_1868.2]

/-- Complete interval computation for depth 15, residue 1869. -/
theorem bounds_15_1869 : exactInterval 15 1869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1869 : oddCount 1869 15 = 8 ∧ acceleratedOrbit 15 1869 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1869) = 3 ^ 8 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1869.1, data_15_1869.2]

/-- Complete interval computation for depth 15, residue 1870. -/
theorem bounds_15_1870 : exactInterval 15 1870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1870 : oddCount 1870 15 = 7 ∧ acceleratedOrbit 15 1870 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1870) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1870.1, data_15_1870.2]

/-- Complete interval computation for depth 15, residue 1871. -/
theorem bounds_15_1871 : exactInterval 15 1871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1871 : oddCount 1871 15 = 7 ∧ acceleratedOrbit 15 1871 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1871) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1871.1, data_15_1871.2]

/-- Complete interval computation for depth 15, residue 1872. -/
theorem bounds_15_1872 : exactInterval 15 1872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1872 : oddCount 1872 15 = 4 ∧ acceleratedOrbit 15 1872 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1872) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1872.1, data_15_1872.2]

/-- Complete interval computation for depth 15, residue 1873. -/
theorem bounds_15_1873 : exactInterval 15 1873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1873 : oddCount 1873 15 = 8 ∧ acceleratedOrbit 15 1873 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1873) = 3 ^ 8 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1873.1, data_15_1873.2]

/-- Complete interval computation for depth 15, residue 1874. -/
theorem bounds_15_1874 : exactInterval 15 1874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1874 : oddCount 1874 15 = 11 ∧ acceleratedOrbit 15 1874 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1874) = 3 ^ 11 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1874.1, data_15_1874.2]

/-- Complete interval computation for depth 15, residue 1875. -/
theorem bounds_15_1875 : exactInterval 15 1875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1875 : oddCount 1875 15 = 11 ∧ acceleratedOrbit 15 1875 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1875) = 3 ^ 11 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1875.1, data_15_1875.2]

/-- Complete interval computation for depth 15, residue 1876. -/
theorem bounds_15_1876 : exactInterval 15 1876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1876 : oddCount 1876 15 = 4 ∧ acceleratedOrbit 15 1876 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1876) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1876.1, data_15_1876.2]

/-- Complete interval computation for depth 15, residue 1877. -/
theorem bounds_15_1877 : exactInterval 15 1877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1877 : oddCount 1877 15 = 4 ∧ acceleratedOrbit 15 1877 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1877) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1877.1, data_15_1877.2]

/-- Complete interval computation for depth 15, residue 1878. -/
theorem bounds_15_1878 : exactInterval 15 1878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1878 : oddCount 1878 15 = 9 ∧ acceleratedOrbit 15 1878 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1878) = 3 ^ 9 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1878.1, data_15_1878.2]

/-- Complete interval computation for depth 15, residue 1879. -/
theorem bounds_15_1879 : exactInterval 15 1879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1879 : oddCount 1879 15 = 9 ∧ acceleratedOrbit 15 1879 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1879) = 3 ^ 9 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1879.1, data_15_1879.2]

/-- Complete interval computation for depth 15, residue 1880. -/
theorem bounds_15_1880 : exactInterval 15 1880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1880 : oddCount 1880 15 = 8 ∧ acceleratedOrbit 15 1880 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1880) = 3 ^ 8 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1880.1, data_15_1880.2]

/-- Complete interval computation for depth 15, residue 1881. -/
theorem bounds_15_1881 : exactInterval 15 1881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1881 : oddCount 1881 15 = 5 ∧ acceleratedOrbit 15 1881 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1881) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1881.1, data_15_1881.2]

/-- Complete interval computation for depth 15, residue 1882. -/
theorem bounds_15_1882 : exactInterval 15 1882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1882 : oddCount 1882 15 = 8 ∧ acceleratedOrbit 15 1882 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1882) = 3 ^ 8 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1882.1, data_15_1882.2]

/-- Complete interval computation for depth 15, residue 1883. -/
theorem bounds_15_1883 : exactInterval 15 1883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1883 : oddCount 1883 15 = 10 ∧ acceleratedOrbit 15 1883 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1883) = 3 ^ 10 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1883.1, data_15_1883.2]

/-- Complete interval computation for depth 15, residue 1884. -/
theorem bounds_15_1884 : exactInterval 15 1884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1884 : oddCount 1884 15 = 8 ∧ acceleratedOrbit 15 1884 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1884) = 3 ^ 8 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1884.1, data_15_1884.2]

/-- Complete interval computation for depth 15, residue 1885. -/
theorem bounds_15_1885 : exactInterval 15 1885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1885 : oddCount 1885 15 = 8 ∧ acceleratedOrbit 15 1885 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1885) = 3 ^ 8 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1885.1, data_15_1885.2]

/-- Complete interval computation for depth 15, residue 1886. -/
theorem bounds_15_1886 : exactInterval 15 1886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1886 : oddCount 1886 15 = 5 ∧ acceleratedOrbit 15 1886 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1886) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1886.1, data_15_1886.2]

/-- Complete interval computation for depth 15, residue 1887. -/
theorem bounds_15_1887 : exactInterval 15 1887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1887 : oddCount 1887 15 = 5 ∧ acceleratedOrbit 15 1887 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1887) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1887.1, data_15_1887.2]

/-- Complete interval computation for depth 15, residue 1888. -/
theorem bounds_15_1888 : exactInterval 15 1888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1888 : oddCount 1888 15 = 6 ∧ acceleratedOrbit 15 1888 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1888) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1888.1, data_15_1888.2]

/-- Complete interval computation for depth 15, residue 1889. -/
theorem bounds_15_1889 : exactInterval 15 1889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1889 : oddCount 1889 15 = 8 ∧ acceleratedOrbit 15 1889 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1889) = 3 ^ 8 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1889.1, data_15_1889.2]

/-- Complete interval computation for depth 15, residue 1890. -/
theorem bounds_15_1890 : exactInterval 15 1890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1890 : oddCount 1890 15 = 6 ∧ acceleratedOrbit 15 1890 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1890) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1890.1, data_15_1890.2]

/-- Complete interval computation for depth 15, residue 1891. -/
theorem bounds_15_1891 : exactInterval 15 1891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1891 : oddCount 1891 15 = 6 ∧ acceleratedOrbit 15 1891 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1891) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1891.1, data_15_1891.2]

/-- Complete interval computation for depth 15, residue 1892. -/
theorem bounds_15_1892 : exactInterval 15 1892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1892 : oddCount 1892 15 = 6 ∧ acceleratedOrbit 15 1892 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1892) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1892.1, data_15_1892.2]

/-- Complete interval computation for depth 15, residue 1893. -/
theorem bounds_15_1893 : exactInterval 15 1893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1893 : oddCount 1893 15 = 6 ∧ acceleratedOrbit 15 1893 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1893) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1893.1, data_15_1893.2]

/-- Complete interval computation for depth 15, residue 1894. -/
theorem bounds_15_1894 : exactInterval 15 1894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1894 : oddCount 1894 15 = 6 ∧ acceleratedOrbit 15 1894 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1894) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1894.1, data_15_1894.2]

/-- Complete interval computation for depth 15, residue 1895. -/
theorem bounds_15_1895 : exactInterval 15 1895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1895 : oddCount 1895 15 = 12 ∧ acceleratedOrbit 15 1895 = 30755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1895) = 3 ^ 12 * m + 30755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1895.1, data_15_1895.2]

/-- Complete interval computation for depth 15, residue 1896. -/
theorem bounds_15_1896 : exactInterval 15 1896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1896 : oddCount 1896 15 = 6 ∧ acceleratedOrbit 15 1896 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1896) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1896.1, data_15_1896.2]

/-- Complete interval computation for depth 15, residue 1897. -/
theorem bounds_15_1897 : exactInterval 15 1897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1897 : oddCount 1897 15 = 7 ∧ acceleratedOrbit 15 1897 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1897) = 3 ^ 7 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1897.1, data_15_1897.2]

/-- Complete interval computation for depth 15, residue 1898. -/
theorem bounds_15_1898 : exactInterval 15 1898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1898 : oddCount 1898 15 = 6 ∧ acceleratedOrbit 15 1898 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1898) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1898.1, data_15_1898.2]

/-- Complete interval computation for depth 15, residue 1899. -/
theorem bounds_15_1899 : exactInterval 15 1899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1899 : oddCount 1899 15 = 7 ∧ acceleratedOrbit 15 1899 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1899) = 3 ^ 7 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1899.1, data_15_1899.2]

end Collatz.Research.PassageAtlas.Batch0058
