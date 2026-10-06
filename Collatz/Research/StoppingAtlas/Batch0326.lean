import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0326

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1920. -/
theorem bounds_12_1920 : exactInterval 12 1920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1920 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1920) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1920 : oddCount 1920 12 = 4 ∧ acceleratedOrbit 12 1920 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1920 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1920) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1920.1, data_12_1920.2]

/-- Complete interval computation for depth 12, residue 1921. -/
theorem bounds_12_1921 : exactInterval 12 1921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1921 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1921) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1921 : oddCount 1921 12 = 7 ∧ acceleratedOrbit 12 1921 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1921 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1921) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1921.1, data_12_1921.2]

/-- Complete interval computation for depth 12, residue 1922. -/
theorem bounds_12_1922 : exactInterval 12 1922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1922 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1922) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1922 : oddCount 1922 12 = 6 ∧ acceleratedOrbit 12 1922 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1922 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1922) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1922.1, data_12_1922.2]

/-- Complete interval computation for depth 12, residue 1923. -/
theorem bounds_12_1923 : exactInterval 12 1923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1923 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1923) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1923 : oddCount 1923 12 = 6 ∧ acceleratedOrbit 12 1923 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1923 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1923) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1923.1, data_12_1923.2]

/-- Complete interval computation for depth 12, residue 1924. -/
theorem bounds_12_1924 : exactInterval 12 1924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1924 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1924) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1924 : oddCount 1924 12 = 6 ∧ acceleratedOrbit 12 1924 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1924 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1924) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1924.1, data_12_1924.2]

/-- Complete interval computation for depth 12, residue 1925. -/
theorem bounds_12_1925 : exactInterval 12 1925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1925 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1925) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1925 : oddCount 1925 12 = 6 ∧ acceleratedOrbit 12 1925 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1925 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1925) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1925.1, data_12_1925.2]

/-- Complete interval computation for depth 12, residue 1926. -/
theorem bounds_12_1926 : exactInterval 12 1926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1926 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1926) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1926 : oddCount 1926 12 = 6 ∧ acceleratedOrbit 12 1926 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1926 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1926) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1926.1, data_12_1926.2]

/-- Complete interval computation for depth 12, residue 1927. -/
theorem bounds_12_1927 : exactInterval 12 1927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1927 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1927) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1927 : oddCount 1927 12 = 6 ∧ acceleratedOrbit 12 1927 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1927 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1927) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1927.1, data_12_1927.2]

/-- Complete interval computation for depth 12, residue 1928. -/
theorem bounds_12_1928 : exactInterval 12 1928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1928 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1928) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1928 : oddCount 1928 12 = 3 ∧ acceleratedOrbit 12 1928 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1928 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1928) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1928.1, data_12_1928.2]

/-- Complete interval computation for depth 12, residue 1929. -/
theorem bounds_12_1929 : exactInterval 12 1929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1929 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1929) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1929 : oddCount 1929 12 = 7 ∧ acceleratedOrbit 12 1929 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1929 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1929) = 3 ^ 7 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1929.1, data_12_1929.2]

/-- Complete interval computation for depth 12, residue 1930. -/
theorem bounds_12_1930 : exactInterval 12 1930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1930 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1930) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1930 : oddCount 1930 12 = 3 ∧ acceleratedOrbit 12 1930 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1930 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1930) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1930.1, data_12_1930.2]

/-- Complete interval computation for depth 12, residue 1931. -/
theorem bounds_12_1931 : exactInterval 12 1931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1931 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1931) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1931 : oddCount 1931 12 = 8 ∧ acceleratedOrbit 12 1931 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1931 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1931) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1931.1, data_12_1931.2]

/-- Complete interval computation for depth 12, residue 1932. -/
theorem bounds_12_1932 : exactInterval 12 1932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1932 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1932) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1932 : oddCount 1932 12 = 3 ∧ acceleratedOrbit 12 1932 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1932 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1932) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1932.1, data_12_1932.2]

/-- Complete interval computation for depth 12, residue 1933. -/
theorem bounds_12_1933 : exactInterval 12 1933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1933 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1933) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1933 : oddCount 1933 12 = 3 ∧ acceleratedOrbit 12 1933 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1933 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1933) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1933.1, data_12_1933.2]

/-- Complete interval computation for depth 12, residue 1934. -/
theorem bounds_12_1934 : exactInterval 12 1934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1934 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1934) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1934 : oddCount 1934 12 = 8 ∧ acceleratedOrbit 12 1934 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1934 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1934) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1934.1, data_12_1934.2]

end Collatz.Research.StoppingAtlas.Batch0326
