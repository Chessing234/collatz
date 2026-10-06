import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0591

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1894. -/
theorem bounds_13_1894 : exactInterval 13 1894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1894 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1894) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1894 : oddCount 1894 13 = 4 ∧ acceleratedOrbit 13 1894 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1894 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1894) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1894.1, data_13_1894.2]

/-- Complete interval computation for depth 13, residue 1895. -/
theorem bounds_13_1895 : exactInterval 13 1895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1895 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1895) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1895 : oddCount 1895 13 = 11 ∧ acceleratedOrbit 13 1895 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1895 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1895) = 3 ^ 11 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1895.1, data_13_1895.2]

/-- Complete interval computation for depth 13, residue 1896. -/
theorem bounds_13_1896 : exactInterval 13 1896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1896 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1896) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1896 : oddCount 1896 13 = 4 ∧ acceleratedOrbit 13 1896 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1896 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1896) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1896.1, data_13_1896.2]

/-- Complete interval computation for depth 13, residue 1897. -/
theorem bounds_13_1897 : exactInterval 13 1897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1897 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1897) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1897 : oddCount 1897 13 = 6 ∧ acceleratedOrbit 13 1897 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1897 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1897) = 3 ^ 6 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1897.1, data_13_1897.2]

/-- Complete interval computation for depth 13, residue 1898. -/
theorem bounds_13_1898 : exactInterval 13 1898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1898 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1898) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1898 : oddCount 1898 13 = 4 ∧ acceleratedOrbit 13 1898 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1898 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1898) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1898.1, data_13_1898.2]

/-- Complete interval computation for depth 13, residue 1899. -/
theorem bounds_13_1899 : exactInterval 13 1899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1899 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1899) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1899 : oddCount 1899 13 = 7 ∧ acceleratedOrbit 13 1899 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1899 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1899) = 3 ^ 7 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1899.1, data_13_1899.2]

/-- Complete interval computation for depth 13, residue 1900. -/
theorem bounds_13_1900 : exactInterval 13 1900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1900 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1900) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1900 : oddCount 1900 13 = 6 ∧ acceleratedOrbit 13 1900 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1900 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1900) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1900.1, data_13_1900.2]

/-- Complete interval computation for depth 13, residue 1901. -/
theorem bounds_13_1901 : exactInterval 13 1901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1901 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1901) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1901 : oddCount 1901 13 = 6 ∧ acceleratedOrbit 13 1901 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1901 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1901) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1901.1, data_13_1901.2]

/-- Complete interval computation for depth 13, residue 1902. -/
theorem bounds_13_1902 : exactInterval 13 1902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1902 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1902) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1902 : oddCount 1902 13 = 6 ∧ acceleratedOrbit 13 1902 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1902 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1902) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1902.1, data_13_1902.2]

/-- Complete interval computation for depth 13, residue 1903. -/
theorem bounds_13_1903 : exactInterval 13 1903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1903 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1903) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1903 : oddCount 1903 13 = 9 ∧ acceleratedOrbit 13 1903 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1903 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1903) = 3 ^ 9 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1903.1, data_13_1903.2]

/-- Complete interval computation for depth 13, residue 1904. -/
theorem bounds_13_1904 : exactInterval 13 1904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1904 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1904) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1904 : oddCount 1904 13 = 4 ∧ acceleratedOrbit 13 1904 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1904 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1904) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1904.1, data_13_1904.2]

/-- Complete interval computation for depth 13, residue 1905. -/
theorem bounds_13_1905 : exactInterval 13 1905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1905 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1905) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1905 : oddCount 1905 13 = 4 ∧ acceleratedOrbit 13 1905 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1905 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1905) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1905.1, data_13_1905.2]

/-- Complete interval computation for depth 13, residue 1906. -/
theorem bounds_13_1906 : exactInterval 13 1906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1906 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1906) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1906 : oddCount 1906 13 = 7 ∧ acceleratedOrbit 13 1906 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1906 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1906) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1906.1, data_13_1906.2]

/-- Complete interval computation for depth 13, residue 1907. -/
theorem bounds_13_1907 : exactInterval 13 1907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1907 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1907) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1907 : oddCount 1907 13 = 7 ∧ acceleratedOrbit 13 1907 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1907 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1907) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1907.1, data_13_1907.2]

/-- Complete interval computation for depth 13, residue 1908. -/
theorem bounds_13_1908 : exactInterval 13 1908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1908 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1908) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1908 : oddCount 1908 13 = 4 ∧ acceleratedOrbit 13 1908 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1908 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1908) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1908.1, data_13_1908.2]

end Collatz.Research.StoppingAtlas.Batch0591
