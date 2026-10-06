import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0191

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1894. -/
theorem bounds_11_1894 : exactInterval 11 1894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1894 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1894) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1894 : oddCount 1894 11 = 3 ∧ acceleratedOrbit 11 1894 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1894 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1894) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1894.1, data_11_1894.2]

/-- Complete interval computation for depth 11, residue 1895. -/
theorem bounds_11_1895 : exactInterval 11 1895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1895 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1895) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1895 : oddCount 1895 11 = 10 ∧ acceleratedOrbit 11 1895 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1895 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1895) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1895.1, data_11_1895.2]

/-- Complete interval computation for depth 11, residue 1896. -/
theorem bounds_11_1896 : exactInterval 11 1896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1896 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1896) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1896 : oddCount 1896 11 = 4 ∧ acceleratedOrbit 11 1896 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1896 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1896) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1896.1, data_11_1896.2]

/-- Complete interval computation for depth 11, residue 1897. -/
theorem bounds_11_1897 : exactInterval 11 1897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1897 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1897) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1897 : oddCount 1897 11 = 6 ∧ acceleratedOrbit 11 1897 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1897 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1897) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1897.1, data_11_1897.2]

/-- Complete interval computation for depth 11, residue 1898. -/
theorem bounds_11_1898 : exactInterval 11 1898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1898 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1898) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1898 : oddCount 1898 11 = 4 ∧ acceleratedOrbit 11 1898 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1898 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1898) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1898.1, data_11_1898.2]

/-- Complete interval computation for depth 11, residue 1899. -/
theorem bounds_11_1899 : exactInterval 11 1899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1899 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1899) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1899 : oddCount 1899 11 = 6 ∧ acceleratedOrbit 11 1899 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1899 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1899) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1899.1, data_11_1899.2]

/-- Complete interval computation for depth 11, residue 1900. -/
theorem bounds_11_1900 : exactInterval 11 1900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1900 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1900) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1900 : oddCount 1900 11 = 5 ∧ acceleratedOrbit 11 1900 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1900 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1900) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1900.1, data_11_1900.2]

/-- Complete interval computation for depth 11, residue 1901. -/
theorem bounds_11_1901 : exactInterval 11 1901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1901 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1901) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1901 : oddCount 1901 11 = 5 ∧ acceleratedOrbit 11 1901 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1901 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1901) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1901.1, data_11_1901.2]

/-- Complete interval computation for depth 11, residue 1902. -/
theorem bounds_11_1902 : exactInterval 11 1902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1902 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1902) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1902 : oddCount 1902 11 = 5 ∧ acceleratedOrbit 11 1902 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1902 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1902) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1902.1, data_11_1902.2]

/-- Complete interval computation for depth 11, residue 1903. -/
theorem bounds_11_1903 : exactInterval 11 1903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1903 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1903) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1903 : oddCount 1903 11 = 8 ∧ acceleratedOrbit 11 1903 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1903 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1903) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1903.1, data_11_1903.2]

/-- Complete interval computation for depth 11, residue 1904. -/
theorem bounds_11_1904 : exactInterval 11 1904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1904 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1904) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1904 : oddCount 1904 11 = 4 ∧ acceleratedOrbit 11 1904 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1904 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1904) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1904.1, data_11_1904.2]

/-- Complete interval computation for depth 11, residue 1905. -/
theorem bounds_11_1905 : exactInterval 11 1905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1905 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1905) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1905 : oddCount 1905 11 = 4 ∧ acceleratedOrbit 11 1905 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1905 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1905) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1905.1, data_11_1905.2]

/-- Complete interval computation for depth 11, residue 1906. -/
theorem bounds_11_1906 : exactInterval 11 1906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1906 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1906) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1906 : oddCount 1906 11 = 5 ∧ acceleratedOrbit 11 1906 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1906 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1906) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1906.1, data_11_1906.2]

/-- Complete interval computation for depth 11, residue 1907. -/
theorem bounds_11_1907 : exactInterval 11 1907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1907 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1907) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1907 : oddCount 1907 11 = 5 ∧ acceleratedOrbit 11 1907 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1907 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1907) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1907.1, data_11_1907.2]

/-- Complete interval computation for depth 11, residue 1908. -/
theorem bounds_11_1908 : exactInterval 11 1908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1908 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1908) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1908 : oddCount 1908 11 = 4 ∧ acceleratedOrbit 11 1908 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1908 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1908) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1908.1, data_11_1908.2]

end Collatz.Research.StoppingAtlas.Batch0191
