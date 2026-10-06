import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0192

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1909. -/
theorem bounds_11_1909 : exactInterval 11 1909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1909 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1909) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1909 : oddCount 1909 11 = 4 ∧ acceleratedOrbit 11 1909 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1909 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1909) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1909.1, data_11_1909.2]

/-- Complete interval computation for depth 11, residue 1910. -/
theorem bounds_11_1910 : exactInterval 11 1910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1910 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1910) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1910 : oddCount 1910 11 = 5 ∧ acceleratedOrbit 11 1910 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1910 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1910) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1910.1, data_11_1910.2]

/-- Complete interval computation for depth 11, residue 1911. -/
theorem bounds_11_1911 : exactInterval 11 1911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1911 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1911) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1911 : oddCount 1911 11 = 5 ∧ acceleratedOrbit 11 1911 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1911 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1911) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1911.1, data_11_1911.2]

/-- Complete interval computation for depth 11, residue 1912. -/
theorem bounds_11_1912 : exactInterval 11 1912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1912 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1912) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1912 : oddCount 1912 11 = 7 ∧ acceleratedOrbit 11 1912 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1912 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1912) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1912.1, data_11_1912.2]

/-- Complete interval computation for depth 11, residue 1913. -/
theorem bounds_11_1913 : exactInterval 11 1913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1913 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1913) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1913 : oddCount 1913 11 = 7 ∧ acceleratedOrbit 11 1913 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1913 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1913) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1913.1, data_11_1913.2]

/-- Complete interval computation for depth 11, residue 1914. -/
theorem bounds_11_1914 : exactInterval 11 1914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1914 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1914) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1914 : oddCount 1914 11 = 7 ∧ acceleratedOrbit 11 1914 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1914 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1914) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1914.1, data_11_1914.2]

/-- Complete interval computation for depth 11, residue 1915. -/
theorem bounds_11_1915 : exactInterval 11 1915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1915 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1915) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1915 : oddCount 1915 11 = 7 ∧ acceleratedOrbit 11 1915 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1915 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1915) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1915.1, data_11_1915.2]

/-- Complete interval computation for depth 11, residue 1916. -/
theorem bounds_11_1916 : exactInterval 11 1916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1916 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1916) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1916 : oddCount 1916 11 = 7 ∧ acceleratedOrbit 11 1916 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1916 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1916) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1916.1, data_11_1916.2]

/-- Complete interval computation for depth 11, residue 1917. -/
theorem bounds_11_1917 : exactInterval 11 1917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1917 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1917) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1917 : oddCount 1917 11 = 7 ∧ acceleratedOrbit 11 1917 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1917 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1917) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1917.1, data_11_1917.2]

/-- Complete interval computation for depth 11, residue 1918. -/
theorem bounds_11_1918 : exactInterval 11 1918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1918 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1918) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1918 : oddCount 1918 11 = 8 ∧ acceleratedOrbit 11 1918 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1918 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1918) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1918.1, data_11_1918.2]

/-- Complete interval computation for depth 11, residue 1919. -/
theorem bounds_11_1919 : exactInterval 11 1919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1919 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1919) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1919 : oddCount 1919 11 = 8 ∧ acceleratedOrbit 11 1919 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1919 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1919) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1919.1, data_11_1919.2]

/-- Complete interval computation for depth 11, residue 1920. -/
theorem bounds_11_1920 : exactInterval 11 1920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1920 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1920) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1920 : oddCount 1920 11 = 4 ∧ acceleratedOrbit 11 1920 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1920 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1920) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1920.1, data_11_1920.2]

/-- Complete interval computation for depth 11, residue 1921. -/
theorem bounds_11_1921 : exactInterval 11 1921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1921 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1921) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1921 : oddCount 1921 11 = 6 ∧ acceleratedOrbit 11 1921 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1921 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1921) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1921.1, data_11_1921.2]

/-- Complete interval computation for depth 11, residue 1922. -/
theorem bounds_11_1922 : exactInterval 11 1922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1922 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1922) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1922 : oddCount 1922 11 = 5 ∧ acceleratedOrbit 11 1922 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1922 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1922) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1922.1, data_11_1922.2]

/-- Complete interval computation for depth 11, residue 1923. -/
theorem bounds_11_1923 : exactInterval 11 1923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1923 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1923) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1923 : oddCount 1923 11 = 5 ∧ acceleratedOrbit 11 1923 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1923 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1923) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1923.1, data_11_1923.2]

/-- Complete interval computation for depth 11, residue 1924. -/
theorem bounds_11_1924 : exactInterval 11 1924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1924 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1924) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1924 : oddCount 1924 11 = 6 ∧ acceleratedOrbit 11 1924 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1924 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1924) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1924.1, data_11_1924.2]

end Collatz.Research.StoppingAtlas.Batch0192
