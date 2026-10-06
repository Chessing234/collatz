import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0190

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1879. -/
theorem bounds_11_1879 : exactInterval 11 1879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1879 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1879) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1879 : oddCount 1879 11 = 6 ∧ acceleratedOrbit 11 1879 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1879 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1879) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1879.1, data_11_1879.2]

/-- Complete interval computation for depth 11, residue 1880. -/
theorem bounds_11_1880 : exactInterval 11 1880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1880 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1880) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1880 : oddCount 1880 11 = 6 ∧ acceleratedOrbit 11 1880 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1880 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1880) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1880.1, data_11_1880.2]

/-- Complete interval computation for depth 11, residue 1881. -/
theorem bounds_11_1881 : exactInterval 11 1881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1881 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1881) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1881 : oddCount 1881 11 = 5 ∧ acceleratedOrbit 11 1881 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1881 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1881) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1881.1, data_11_1881.2]

/-- Complete interval computation for depth 11, residue 1882. -/
theorem bounds_11_1882 : exactInterval 11 1882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1882 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1882) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1882 : oddCount 1882 11 = 6 ∧ acceleratedOrbit 11 1882 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1882 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1882) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1882.1, data_11_1882.2]

/-- Complete interval computation for depth 11, residue 1883. -/
theorem bounds_11_1883 : exactInterval 11 1883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1883 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1883) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1883 : oddCount 1883 11 = 8 ∧ acceleratedOrbit 11 1883 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1883 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1883) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1883.1, data_11_1883.2]

/-- Complete interval computation for depth 11, residue 1884. -/
theorem bounds_11_1884 : exactInterval 11 1884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1884 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1884) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1884 : oddCount 1884 11 = 6 ∧ acceleratedOrbit 11 1884 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1884 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1884) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1884.1, data_11_1884.2]

/-- Complete interval computation for depth 11, residue 1885. -/
theorem bounds_11_1885 : exactInterval 11 1885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1885 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1885) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1885 : oddCount 1885 11 = 6 ∧ acceleratedOrbit 11 1885 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1885 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1885) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1885.1, data_11_1885.2]

/-- Complete interval computation for depth 11, residue 1886. -/
theorem bounds_11_1886 : exactInterval 11 1886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1886 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1886) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1886 : oddCount 1886 11 = 5 ∧ acceleratedOrbit 11 1886 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1886 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1886) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1886.1, data_11_1886.2]

/-- Complete interval computation for depth 11, residue 1887. -/
theorem bounds_11_1887 : exactInterval 11 1887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1887 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1887) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1887 : oddCount 1887 11 = 5 ∧ acceleratedOrbit 11 1887 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1887 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1887) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1887.1, data_11_1887.2]

/-- Complete interval computation for depth 11, residue 1888. -/
theorem bounds_11_1888 : exactInterval 11 1888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1888 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1888) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1888 : oddCount 1888 11 = 4 ∧ acceleratedOrbit 11 1888 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1888 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1888) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1888.1, data_11_1888.2]

/-- Complete interval computation for depth 11, residue 1889. -/
theorem bounds_11_1889 : exactInterval 11 1889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1889 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1889) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1889 : oddCount 1889 11 = 7 ∧ acceleratedOrbit 11 1889 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1889 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1889) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1889.1, data_11_1889.2]

/-- Complete interval computation for depth 11, residue 1890. -/
theorem bounds_11_1890 : exactInterval 11 1890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1890 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1890) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1890 : oddCount 1890 11 = 3 ∧ acceleratedOrbit 11 1890 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1890 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1890) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1890.1, data_11_1890.2]

/-- Complete interval computation for depth 11, residue 1891. -/
theorem bounds_11_1891 : exactInterval 11 1891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1891 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1891) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1891 : oddCount 1891 11 = 3 ∧ acceleratedOrbit 11 1891 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1891 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1891) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1891.1, data_11_1891.2]

/-- Complete interval computation for depth 11, residue 1892. -/
theorem bounds_11_1892 : exactInterval 11 1892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1892 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1892) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1892 : oddCount 1892 11 = 3 ∧ acceleratedOrbit 11 1892 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1892 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1892) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1892.1, data_11_1892.2]

/-- Complete interval computation for depth 11, residue 1893. -/
theorem bounds_11_1893 : exactInterval 11 1893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1893 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1893) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1893 : oddCount 1893 11 = 3 ∧ acceleratedOrbit 11 1893 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1893 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1893) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1893.1, data_11_1893.2]

end Collatz.Research.StoppingAtlas.Batch0190
