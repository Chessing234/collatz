import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0324

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1889. -/
theorem bounds_12_1889 : exactInterval 12 1889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1889 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1889) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1889 : oddCount 1889 12 = 7 ∧ acceleratedOrbit 12 1889 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1889 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1889) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1889.1, data_12_1889.2]

/-- Complete interval computation for depth 12, residue 1890. -/
theorem bounds_12_1890 : exactInterval 12 1890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1890 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1890) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1890 : oddCount 1890 12 = 4 ∧ acceleratedOrbit 12 1890 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1890 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1890) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1890.1, data_12_1890.2]

/-- Complete interval computation for depth 12, residue 1891. -/
theorem bounds_12_1891 : exactInterval 12 1891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1891 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1891) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1891 : oddCount 1891 12 = 4 ∧ acceleratedOrbit 12 1891 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1891 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1891) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1891.1, data_12_1891.2]

/-- Complete interval computation for depth 12, residue 1892. -/
theorem bounds_12_1892 : exactInterval 12 1892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1892 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1892) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1892 : oddCount 1892 12 = 4 ∧ acceleratedOrbit 12 1892 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1892 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1892) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1892.1, data_12_1892.2]

/-- Complete interval computation for depth 12, residue 1893. -/
theorem bounds_12_1893 : exactInterval 12 1893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1893 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1893) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1893 : oddCount 1893 12 = 4 ∧ acceleratedOrbit 12 1893 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1893 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1893) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1893.1, data_12_1893.2]

/-- Complete interval computation for depth 12, residue 1894. -/
theorem bounds_12_1894 : exactInterval 12 1894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1894 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1894) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1894 : oddCount 1894 12 = 4 ∧ acceleratedOrbit 12 1894 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1894 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1894) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1894.1, data_12_1894.2]

/-- Complete interval computation for depth 12, residue 1895. -/
theorem bounds_12_1895 : exactInterval 12 1895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1895 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1895) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1895 : oddCount 1895 12 = 10 ∧ acceleratedOrbit 12 1895 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1895 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1895) = 3 ^ 10 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1895.1, data_12_1895.2]

/-- Complete interval computation for depth 12, residue 1896. -/
theorem bounds_12_1896 : exactInterval 12 1896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1896 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1896) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1896 : oddCount 1896 12 = 4 ∧ acceleratedOrbit 12 1896 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1896 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1896) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1896.1, data_12_1896.2]

/-- Complete interval computation for depth 12, residue 1897. -/
theorem bounds_12_1897 : exactInterval 12 1897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1897 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1897) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1897 : oddCount 1897 12 = 6 ∧ acceleratedOrbit 12 1897 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1897 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1897) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1897.1, data_12_1897.2]

/-- Complete interval computation for depth 12, residue 1898. -/
theorem bounds_12_1898 : exactInterval 12 1898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1898 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1898) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1898 : oddCount 1898 12 = 4 ∧ acceleratedOrbit 12 1898 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1898 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1898) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1898.1, data_12_1898.2]

/-- Complete interval computation for depth 12, residue 1899. -/
theorem bounds_12_1899 : exactInterval 12 1899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1899 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1899) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1899 : oddCount 1899 12 = 7 ∧ acceleratedOrbit 12 1899 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1899 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1899) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1899.1, data_12_1899.2]

/-- Complete interval computation for depth 12, residue 1900. -/
theorem bounds_12_1900 : exactInterval 12 1900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1900 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1900) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1900 : oddCount 1900 12 = 5 ∧ acceleratedOrbit 12 1900 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1900 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1900) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1900.1, data_12_1900.2]

/-- Complete interval computation for depth 12, residue 1901. -/
theorem bounds_12_1901 : exactInterval 12 1901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1901 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1901) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1901 : oddCount 1901 12 = 5 ∧ acceleratedOrbit 12 1901 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1901 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1901) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1901.1, data_12_1901.2]

/-- Complete interval computation for depth 12, residue 1902. -/
theorem bounds_12_1902 : exactInterval 12 1902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1902 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1902) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1902 : oddCount 1902 12 = 5 ∧ acceleratedOrbit 12 1902 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1902 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1902) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1902.1, data_12_1902.2]

/-- Complete interval computation for depth 12, residue 1903. -/
theorem bounds_12_1903 : exactInterval 12 1903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1903 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1903) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1903 : oddCount 1903 12 = 9 ∧ acceleratedOrbit 12 1903 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1903 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1903) = 3 ^ 9 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1903.1, data_12_1903.2]

end Collatz.Research.StoppingAtlas.Batch0324
