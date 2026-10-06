import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0325

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1904. -/
theorem bounds_12_1904 : exactInterval 12 1904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1904 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1904) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1904 : oddCount 1904 12 = 4 ∧ acceleratedOrbit 12 1904 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1904 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1904) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1904.1, data_12_1904.2]

/-- Complete interval computation for depth 12, residue 1905. -/
theorem bounds_12_1905 : exactInterval 12 1905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1905 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1905) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1905 : oddCount 1905 12 = 4 ∧ acceleratedOrbit 12 1905 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1905 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1905) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1905.1, data_12_1905.2]

/-- Complete interval computation for depth 12, residue 1906. -/
theorem bounds_12_1906 : exactInterval 12 1906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1906 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1906) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1906 : oddCount 1906 12 = 6 ∧ acceleratedOrbit 12 1906 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1906 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1906) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1906.1, data_12_1906.2]

/-- Complete interval computation for depth 12, residue 1907. -/
theorem bounds_12_1907 : exactInterval 12 1907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1907 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1907) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1907 : oddCount 1907 12 = 6 ∧ acceleratedOrbit 12 1907 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1907 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1907) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1907.1, data_12_1907.2]

/-- Complete interval computation for depth 12, residue 1908. -/
theorem bounds_12_1908 : exactInterval 12 1908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1908 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1908) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1908 : oddCount 1908 12 = 4 ∧ acceleratedOrbit 12 1908 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1908 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1908) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1908.1, data_12_1908.2]

/-- Complete interval computation for depth 12, residue 1909. -/
theorem bounds_12_1909 : exactInterval 12 1909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1909 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1909) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1909 : oddCount 1909 12 = 4 ∧ acceleratedOrbit 12 1909 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1909 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1909) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1909.1, data_12_1909.2]

/-- Complete interval computation for depth 12, residue 1910. -/
theorem bounds_12_1910 : exactInterval 12 1910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1910 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1910) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1910 : oddCount 1910 12 = 6 ∧ acceleratedOrbit 12 1910 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1910 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1910) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1910.1, data_12_1910.2]

/-- Complete interval computation for depth 12, residue 1911. -/
theorem bounds_12_1911 : exactInterval 12 1911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1911 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1911) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1911 : oddCount 1911 12 = 6 ∧ acceleratedOrbit 12 1911 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1911 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1911) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1911.1, data_12_1911.2]

/-- Complete interval computation for depth 12, residue 1912. -/
theorem bounds_12_1912 : exactInterval 12 1912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1912 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1912) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1912 : oddCount 1912 12 = 8 ∧ acceleratedOrbit 12 1912 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1912 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1912) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1912.1, data_12_1912.2]

/-- Complete interval computation for depth 12, residue 1913. -/
theorem bounds_12_1913 : exactInterval 12 1913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1913 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1913) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1913 : oddCount 1913 12 = 8 ∧ acceleratedOrbit 12 1913 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1913 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1913) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1913.1, data_12_1913.2]

/-- Complete interval computation for depth 12, residue 1914. -/
theorem bounds_12_1914 : exactInterval 12 1914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1914 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1914) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1914 : oddCount 1914 12 = 8 ∧ acceleratedOrbit 12 1914 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1914 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1914) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1914.1, data_12_1914.2]

/-- Complete interval computation for depth 12, residue 1915. -/
theorem bounds_12_1915 : exactInterval 12 1915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1915 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1915) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1915 : oddCount 1915 12 = 8 ∧ acceleratedOrbit 12 1915 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1915 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1915) = 3 ^ 8 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1915.1, data_12_1915.2]

/-- Complete interval computation for depth 12, residue 1916. -/
theorem bounds_12_1916 : exactInterval 12 1916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1916 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1916) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1916 : oddCount 1916 12 = 8 ∧ acceleratedOrbit 12 1916 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1916 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1916) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1916.1, data_12_1916.2]

/-- Complete interval computation for depth 12, residue 1917. -/
theorem bounds_12_1917 : exactInterval 12 1917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1917 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1917) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1917 : oddCount 1917 12 = 8 ∧ acceleratedOrbit 12 1917 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1917 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1917) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1917.1, data_12_1917.2]

/-- Complete interval computation for depth 12, residue 1918. -/
theorem bounds_12_1918 : exactInterval 12 1918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1918 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1918) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1918 : oddCount 1918 12 = 9 ∧ acceleratedOrbit 12 1918 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1918 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1918) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1918.1, data_12_1918.2]

/-- Complete interval computation for depth 12, residue 1919. -/
theorem bounds_12_1919 : exactInterval 12 1919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1919 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1919) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1919 : oddCount 1919 12 = 9 ∧ acceleratedOrbit 12 1919 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1919 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1919) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1919.1, data_12_1919.2]

end Collatz.Research.StoppingAtlas.Batch0325
