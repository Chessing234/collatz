import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0590

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1879. -/
theorem bounds_13_1879 : exactInterval 13 1879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1879 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1879) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1879 : oddCount 1879 13 = 7 ∧ acceleratedOrbit 13 1879 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1879 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1879) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1879.1, data_13_1879.2]

/-- Complete interval computation for depth 13, residue 1880. -/
theorem bounds_13_1880 : exactInterval 13 1880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1880 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1880) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1880 : oddCount 1880 13 = 7 ∧ acceleratedOrbit 13 1880 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1880 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1880) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1880.1, data_13_1880.2]

/-- Complete interval computation for depth 13, residue 1881. -/
theorem bounds_13_1881 : exactInterval 13 1881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1881 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1881) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1881 : oddCount 1881 13 = 5 ∧ acceleratedOrbit 13 1881 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1881 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1881) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1881.1, data_13_1881.2]

/-- Complete interval computation for depth 13, residue 1882. -/
theorem bounds_13_1882 : exactInterval 13 1882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1882 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1882) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1882 : oddCount 1882 13 = 7 ∧ acceleratedOrbit 13 1882 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1882 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1882) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1882.1, data_13_1882.2]

/-- Complete interval computation for depth 13, residue 1883. -/
theorem bounds_13_1883 : exactInterval 13 1883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1883 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1883) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1883 : oddCount 1883 13 = 9 ∧ acceleratedOrbit 13 1883 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1883 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1883) = 3 ^ 9 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1883.1, data_13_1883.2]

/-- Complete interval computation for depth 13, residue 1884. -/
theorem bounds_13_1884 : exactInterval 13 1884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1884 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1884) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1884 : oddCount 1884 13 = 7 ∧ acceleratedOrbit 13 1884 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1884 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1884) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1884.1, data_13_1884.2]

/-- Complete interval computation for depth 13, residue 1885. -/
theorem bounds_13_1885 : exactInterval 13 1885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1885 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1885) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1885 : oddCount 1885 13 = 7 ∧ acceleratedOrbit 13 1885 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1885 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1885) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1885.1, data_13_1885.2]

/-- Complete interval computation for depth 13, residue 1886. -/
theorem bounds_13_1886 : exactInterval 13 1886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1886 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1886) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1886 : oddCount 1886 13 = 5 ∧ acceleratedOrbit 13 1886 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1886 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1886) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1886.1, data_13_1886.2]

/-- Complete interval computation for depth 13, residue 1887. -/
theorem bounds_13_1887 : exactInterval 13 1887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1887 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1887) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1887 : oddCount 1887 13 = 5 ∧ acceleratedOrbit 13 1887 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1887 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1887) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1887.1, data_13_1887.2]

/-- Complete interval computation for depth 13, residue 1888. -/
theorem bounds_13_1888 : exactInterval 13 1888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1888 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1888) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1888 : oddCount 1888 13 = 4 ∧ acceleratedOrbit 13 1888 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1888 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1888) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1888.1, data_13_1888.2]

/-- Complete interval computation for depth 13, residue 1889. -/
theorem bounds_13_1889 : exactInterval 13 1889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1889 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1889) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1889 : oddCount 1889 13 = 7 ∧ acceleratedOrbit 13 1889 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1889 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1889) = 3 ^ 7 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1889.1, data_13_1889.2]

/-- Complete interval computation for depth 13, residue 1890. -/
theorem bounds_13_1890 : exactInterval 13 1890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1890 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1890) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1890 : oddCount 1890 13 = 4 ∧ acceleratedOrbit 13 1890 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1890 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1890) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1890.1, data_13_1890.2]

/-- Complete interval computation for depth 13, residue 1891. -/
theorem bounds_13_1891 : exactInterval 13 1891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1891 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1891) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1891 : oddCount 1891 13 = 4 ∧ acceleratedOrbit 13 1891 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1891 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1891) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1891.1, data_13_1891.2]

/-- Complete interval computation for depth 13, residue 1892. -/
theorem bounds_13_1892 : exactInterval 13 1892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1892 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1892) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1892 : oddCount 1892 13 = 4 ∧ acceleratedOrbit 13 1892 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1892 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1892) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1892.1, data_13_1892.2]

/-- Complete interval computation for depth 13, residue 1893. -/
theorem bounds_13_1893 : exactInterval 13 1893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1893 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1893) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1893 : oddCount 1893 13 = 4 ∧ acceleratedOrbit 13 1893 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1893 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1893) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1893.1, data_13_1893.2]

end Collatz.Research.StoppingAtlas.Batch0590
