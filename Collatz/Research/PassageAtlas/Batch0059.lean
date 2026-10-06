import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0059

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1900. -/
theorem bounds_15_1900 : exactInterval 15 1900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1900 : oddCount 1900 15 = 7 ∧ acceleratedOrbit 15 1900 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1900) = 3 ^ 7 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1900.1, data_15_1900.2]

/-- Complete interval computation for depth 15, residue 1901. -/
theorem bounds_15_1901 : exactInterval 15 1901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1901 : oddCount 1901 15 = 7 ∧ acceleratedOrbit 15 1901 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1901) = 3 ^ 7 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1901.1, data_15_1901.2]

/-- Complete interval computation for depth 15, residue 1902. -/
theorem bounds_15_1902 : exactInterval 15 1902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1902 : oddCount 1902 15 = 7 ∧ acceleratedOrbit 15 1902 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1902) = 3 ^ 7 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1902.1, data_15_1902.2]

/-- Complete interval computation for depth 15, residue 1903. -/
theorem bounds_15_1903 : exactInterval 15 1903 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1903) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1903 : oddCount 1903 15 = 9 ∧ acceleratedOrbit 15 1903 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1903) = 3 ^ 9 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1903.1, data_15_1903.2]

/-- Complete interval computation for depth 15, residue 1904. -/
theorem bounds_15_1904 : exactInterval 15 1904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1904 : oddCount 1904 15 = 6 ∧ acceleratedOrbit 15 1904 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1904) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1904.1, data_15_1904.2]

/-- Complete interval computation for depth 15, residue 1905. -/
theorem bounds_15_1905 : exactInterval 15 1905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1905 : oddCount 1905 15 = 6 ∧ acceleratedOrbit 15 1905 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1905) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1905.1, data_15_1905.2]

/-- Complete interval computation for depth 15, residue 1906. -/
theorem bounds_15_1906 : exactInterval 15 1906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1906 : oddCount 1906 15 = 7 ∧ acceleratedOrbit 15 1906 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1906) = 3 ^ 7 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1906.1, data_15_1906.2]

/-- Complete interval computation for depth 15, residue 1907. -/
theorem bounds_15_1907 : exactInterval 15 1907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1907 : oddCount 1907 15 = 7 ∧ acceleratedOrbit 15 1907 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1907) = 3 ^ 7 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1907.1, data_15_1907.2]

/-- Complete interval computation for depth 15, residue 1908. -/
theorem bounds_15_1908 : exactInterval 15 1908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1908 : oddCount 1908 15 = 6 ∧ acceleratedOrbit 15 1908 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1908) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1908.1, data_15_1908.2]

/-- Complete interval computation for depth 15, residue 1909. -/
theorem bounds_15_1909 : exactInterval 15 1909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1909 : oddCount 1909 15 = 6 ∧ acceleratedOrbit 15 1909 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1909) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1909.1, data_15_1909.2]

/-- Complete interval computation for depth 15, residue 1910. -/
theorem bounds_15_1910 : exactInterval 15 1910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1910 : oddCount 1910 15 = 7 ∧ acceleratedOrbit 15 1910 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1910) = 3 ^ 7 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1910.1, data_15_1910.2]

/-- Complete interval computation for depth 15, residue 1911. -/
theorem bounds_15_1911 : exactInterval 15 1911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1911 : oddCount 1911 15 = 7 ∧ acceleratedOrbit 15 1911 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1911) = 3 ^ 7 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1911.1, data_15_1911.2]

/-- Complete interval computation for depth 15, residue 1912. -/
theorem bounds_15_1912 : exactInterval 15 1912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1912 : oddCount 1912 15 = 9 ∧ acceleratedOrbit 15 1912 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1912) = 3 ^ 9 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1912.1, data_15_1912.2]

/-- Complete interval computation for depth 15, residue 1913. -/
theorem bounds_15_1913 : exactInterval 15 1913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1913 : oddCount 1913 15 = 9 ∧ acceleratedOrbit 15 1913 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1913) = 3 ^ 9 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1913.1, data_15_1913.2]

/-- Complete interval computation for depth 15, residue 1914. -/
theorem bounds_15_1914 : exactInterval 15 1914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1914 : oddCount 1914 15 = 9 ∧ acceleratedOrbit 15 1914 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1914) = 3 ^ 9 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1914.1, data_15_1914.2]

/-- Complete interval computation for depth 15, residue 1915. -/
theorem bounds_15_1915 : exactInterval 15 1915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1915 : oddCount 1915 15 = 11 ∧ acceleratedOrbit 15 1915 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1915) = 3 ^ 11 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1915.1, data_15_1915.2]

/-- Complete interval computation for depth 15, residue 1916. -/
theorem bounds_15_1916 : exactInterval 15 1916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1916 : oddCount 1916 15 = 9 ∧ acceleratedOrbit 15 1916 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1916) = 3 ^ 9 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1916.1, data_15_1916.2]

/-- Complete interval computation for depth 15, residue 1917. -/
theorem bounds_15_1917 : exactInterval 15 1917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1917 : oddCount 1917 15 = 9 ∧ acceleratedOrbit 15 1917 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1917) = 3 ^ 9 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1917.1, data_15_1917.2]

/-- Complete interval computation for depth 15, residue 1918. -/
theorem bounds_15_1918 : exactInterval 15 1918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1918 : oddCount 1918 15 = 11 ∧ acceleratedOrbit 15 1918 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1918) = 3 ^ 11 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1918.1, data_15_1918.2]

/-- Complete interval computation for depth 15, residue 1919. -/
theorem bounds_15_1919 : exactInterval 15 1919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1919 : oddCount 1919 15 = 11 ∧ acceleratedOrbit 15 1919 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1919) = 3 ^ 11 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1919.1, data_15_1919.2]

/-- Complete interval computation for depth 15, residue 1920. -/
theorem bounds_15_1920 : exactInterval 15 1920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1920 : oddCount 1920 15 = 4 ∧ acceleratedOrbit 15 1920 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1920) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1920.1, data_15_1920.2]

/-- Complete interval computation for depth 15, residue 1921. -/
theorem bounds_15_1921 : exactInterval 15 1921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1921 : oddCount 1921 15 = 8 ∧ acceleratedOrbit 15 1921 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1921) = 3 ^ 8 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1921.1, data_15_1921.2]

/-- Complete interval computation for depth 15, residue 1922. -/
theorem bounds_15_1922 : exactInterval 15 1922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1922 : oddCount 1922 15 = 6 ∧ acceleratedOrbit 15 1922 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1922) = 3 ^ 6 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1922.1, data_15_1922.2]

/-- Complete interval computation for depth 15, residue 1923. -/
theorem bounds_15_1923 : exactInterval 15 1923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1923 : oddCount 1923 15 = 6 ∧ acceleratedOrbit 15 1923 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1923) = 3 ^ 6 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1923.1, data_15_1923.2]

/-- Complete interval computation for depth 15, residue 1924. -/
theorem bounds_15_1924 : exactInterval 15 1924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1924 : oddCount 1924 15 = 6 ∧ acceleratedOrbit 15 1924 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1924) = 3 ^ 6 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1924.1, data_15_1924.2]

/-- Complete interval computation for depth 15, residue 1925. -/
theorem bounds_15_1925 : exactInterval 15 1925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1925 : oddCount 1925 15 = 6 ∧ acceleratedOrbit 15 1925 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1925) = 3 ^ 6 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1925.1, data_15_1925.2]

/-- Complete interval computation for depth 15, residue 1926. -/
theorem bounds_15_1926 : exactInterval 15 1926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1926 : oddCount 1926 15 = 6 ∧ acceleratedOrbit 15 1926 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1926) = 3 ^ 6 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1926.1, data_15_1926.2]

/-- Complete interval computation for depth 15, residue 1927. -/
theorem bounds_15_1927 : exactInterval 15 1927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1927 : oddCount 1927 15 = 6 ∧ acceleratedOrbit 15 1927 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1927) = 3 ^ 6 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1927.1, data_15_1927.2]

/-- Complete interval computation for depth 15, residue 1928. -/
theorem bounds_15_1928 : exactInterval 15 1928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1928 : oddCount 1928 15 = 4 ∧ acceleratedOrbit 15 1928 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1928) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1928.1, data_15_1928.2]

/-- Complete interval computation for depth 15, residue 1929. -/
theorem bounds_15_1929 : exactInterval 15 1929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1929 : oddCount 1929 15 = 10 ∧ acceleratedOrbit 15 1929 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1929) = 3 ^ 10 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1929.1, data_15_1929.2]

/-- Complete interval computation for depth 15, residue 1930. -/
theorem bounds_15_1930 : exactInterval 15 1930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1930 : oddCount 1930 15 = 4 ∧ acceleratedOrbit 15 1930 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1930) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1930.1, data_15_1930.2]

/-- Complete interval computation for depth 15, residue 1931. -/
theorem bounds_15_1931 : exactInterval 15 1931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1931 : oddCount 1931 15 = 9 ∧ acceleratedOrbit 15 1931 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1931) = 3 ^ 9 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1931.1, data_15_1931.2]

/-- Complete interval computation for depth 15, residue 1932. -/
theorem bounds_15_1932 : exactInterval 15 1932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1932 : oddCount 1932 15 = 4 ∧ acceleratedOrbit 15 1932 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1932) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1932.1, data_15_1932.2]

end Collatz.Research.PassageAtlas.Batch0059
