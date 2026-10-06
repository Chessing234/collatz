import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0592

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1909. -/
theorem bounds_13_1909 : exactInterval 13 1909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1909 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1909) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1909 : oddCount 1909 13 = 4 ∧ acceleratedOrbit 13 1909 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1909 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1909) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1909.1, data_13_1909.2]

/-- Complete interval computation for depth 13, residue 1910. -/
theorem bounds_13_1910 : exactInterval 13 1910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1910 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1910) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1910 : oddCount 1910 13 = 7 ∧ acceleratedOrbit 13 1910 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1910 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1910) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1910.1, data_13_1910.2]

/-- Complete interval computation for depth 13, residue 1911. -/
theorem bounds_13_1911 : exactInterval 13 1911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1911 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1911) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1911 : oddCount 1911 13 = 7 ∧ acceleratedOrbit 13 1911 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1911 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1911) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1911.1, data_13_1911.2]

/-- Complete interval computation for depth 13, residue 1912. -/
theorem bounds_13_1912 : exactInterval 13 1912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1912 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1912) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1912 : oddCount 1912 13 = 9 ∧ acceleratedOrbit 13 1912 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1912 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1912) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1912.1, data_13_1912.2]

/-- Complete interval computation for depth 13, residue 1913. -/
theorem bounds_13_1913 : exactInterval 13 1913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1913 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1913) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1913 : oddCount 1913 13 = 8 ∧ acceleratedOrbit 13 1913 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1913 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1913) = 3 ^ 8 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1913.1, data_13_1913.2]

/-- Complete interval computation for depth 13, residue 1914. -/
theorem bounds_13_1914 : exactInterval 13 1914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1914 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1914) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1914 : oddCount 1914 13 = 9 ∧ acceleratedOrbit 13 1914 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1914 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1914) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1914.1, data_13_1914.2]

/-- Complete interval computation for depth 13, residue 1915. -/
theorem bounds_13_1915 : exactInterval 13 1915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1915 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1915) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1915 : oddCount 1915 13 = 9 ∧ acceleratedOrbit 13 1915 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1915 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1915) = 3 ^ 9 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1915.1, data_13_1915.2]

/-- Complete interval computation for depth 13, residue 1916. -/
theorem bounds_13_1916 : exactInterval 13 1916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1916 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1916) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1916 : oddCount 1916 13 = 9 ∧ acceleratedOrbit 13 1916 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1916 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1916) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1916.1, data_13_1916.2]

/-- Complete interval computation for depth 13, residue 1917. -/
theorem bounds_13_1917 : exactInterval 13 1917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1917 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1917) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1917 : oddCount 1917 13 = 9 ∧ acceleratedOrbit 13 1917 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1917 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1917) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1917.1, data_13_1917.2]

/-- Complete interval computation for depth 13, residue 1918. -/
theorem bounds_13_1918 : exactInterval 13 1918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1918 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1918) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1918 : oddCount 1918 13 = 10 ∧ acceleratedOrbit 13 1918 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1918 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1918) = 3 ^ 10 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1918.1, data_13_1918.2]

/-- Complete interval computation for depth 13, residue 1919. -/
theorem bounds_13_1919 : exactInterval 13 1919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1919 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1919) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1919 : oddCount 1919 13 = 10 ∧ acceleratedOrbit 13 1919 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1919 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1919) = 3 ^ 10 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1919.1, data_13_1919.2]

/-- Complete interval computation for depth 13, residue 1920. -/
theorem bounds_13_1920 : exactInterval 13 1920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1920 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1920) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1920 : oddCount 1920 13 = 4 ∧ acceleratedOrbit 13 1920 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1920 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1920) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1920.1, data_13_1920.2]

/-- Complete interval computation for depth 13, residue 1921. -/
theorem bounds_13_1921 : exactInterval 13 1921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1921 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1921) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1921 : oddCount 1921 13 = 7 ∧ acceleratedOrbit 13 1921 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1921 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1921) = 3 ^ 7 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1921.1, data_13_1921.2]

/-- Complete interval computation for depth 13, residue 1922. -/
theorem bounds_13_1922 : exactInterval 13 1922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1922 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1922) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1922 : oddCount 1922 13 = 6 ∧ acceleratedOrbit 13 1922 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1922 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1922) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1922.1, data_13_1922.2]

/-- Complete interval computation for depth 13, residue 1923. -/
theorem bounds_13_1923 : exactInterval 13 1923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1923 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1923) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1923 : oddCount 1923 13 = 6 ∧ acceleratedOrbit 13 1923 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1923 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1923) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1923.1, data_13_1923.2]

/-- Complete interval computation for depth 13, residue 1924. -/
theorem bounds_13_1924 : exactInterval 13 1924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1924 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1924) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1924 : oddCount 1924 13 = 6 ∧ acceleratedOrbit 13 1924 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1924 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1924) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1924.1, data_13_1924.2]

end Collatz.Research.StoppingAtlas.Batch0592
