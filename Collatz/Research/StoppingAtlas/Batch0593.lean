import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0593

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1925. -/
theorem bounds_13_1925 : exactInterval 13 1925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1925 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1925) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1925 : oddCount 1925 13 = 6 ∧ acceleratedOrbit 13 1925 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1925 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1925) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1925.1, data_13_1925.2]

/-- Complete interval computation for depth 13, residue 1926. -/
theorem bounds_13_1926 : exactInterval 13 1926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1926 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1926) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1926 : oddCount 1926 13 = 6 ∧ acceleratedOrbit 13 1926 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1926 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1926) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1926.1, data_13_1926.2]

/-- Complete interval computation for depth 13, residue 1927. -/
theorem bounds_13_1927 : exactInterval 13 1927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1927 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1927) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1927 : oddCount 1927 13 = 6 ∧ acceleratedOrbit 13 1927 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1927 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1927) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1927.1, data_13_1927.2]

/-- Complete interval computation for depth 13, residue 1928. -/
theorem bounds_13_1928 : exactInterval 13 1928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1928 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1928) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1928 : oddCount 1928 13 = 4 ∧ acceleratedOrbit 13 1928 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1928 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1928) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1928.1, data_13_1928.2]

/-- Complete interval computation for depth 13, residue 1929. -/
theorem bounds_13_1929 : exactInterval 13 1929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1929 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1929) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1929 : oddCount 1929 13 = 8 ∧ acceleratedOrbit 13 1929 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1929 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1929) = 3 ^ 8 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1929.1, data_13_1929.2]

/-- Complete interval computation for depth 13, residue 1930. -/
theorem bounds_13_1930 : exactInterval 13 1930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1930 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1930) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1930 : oddCount 1930 13 = 4 ∧ acceleratedOrbit 13 1930 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1930 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1930) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1930.1, data_13_1930.2]

/-- Complete interval computation for depth 13, residue 1931. -/
theorem bounds_13_1931 : exactInterval 13 1931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1931 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1931) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1931 : oddCount 1931 13 = 8 ∧ acceleratedOrbit 13 1931 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1931 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1931) = 3 ^ 8 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1931.1, data_13_1931.2]

/-- Complete interval computation for depth 13, residue 1932. -/
theorem bounds_13_1932 : exactInterval 13 1932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1932 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1932) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1932 : oddCount 1932 13 = 4 ∧ acceleratedOrbit 13 1932 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1932 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1932) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1932.1, data_13_1932.2]

/-- Complete interval computation for depth 13, residue 1933. -/
theorem bounds_13_1933 : exactInterval 13 1933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1933 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1933) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1933 : oddCount 1933 13 = 4 ∧ acceleratedOrbit 13 1933 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1933 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1933) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1933.1, data_13_1933.2]

/-- Complete interval computation for depth 13, residue 1934. -/
theorem bounds_13_1934 : exactInterval 13 1934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1934 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1934) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1934 : oddCount 1934 13 = 8 ∧ acceleratedOrbit 13 1934 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1934 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1934) = 3 ^ 8 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1934.1, data_13_1934.2]

/-- Complete interval computation for depth 13, residue 1935. -/
theorem bounds_13_1935 : exactInterval 13 1935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1935 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1935) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1935 : oddCount 1935 13 = 8 ∧ acceleratedOrbit 13 1935 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1935 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1935) = 3 ^ 8 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1935.1, data_13_1935.2]

/-- Complete interval computation for depth 13, residue 1936. -/
theorem bounds_13_1936 : exactInterval 13 1936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1936 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1936) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1936 : oddCount 1936 13 = 6 ∧ acceleratedOrbit 13 1936 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1936 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1936) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1936.1, data_13_1936.2]

/-- Complete interval computation for depth 13, residue 1937. -/
theorem bounds_13_1937 : exactInterval 13 1937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1937 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1937) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1937 : oddCount 1937 13 = 6 ∧ acceleratedOrbit 13 1937 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1937 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1937) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1937.1, data_13_1937.2]

/-- Complete interval computation for depth 13, residue 1938. -/
theorem bounds_13_1938 : exactInterval 13 1938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1938 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1938) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1938 : oddCount 1938 13 = 6 ∧ acceleratedOrbit 13 1938 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1938 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1938) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1938.1, data_13_1938.2]

/-- Complete interval computation for depth 13, residue 1939. -/
theorem bounds_13_1939 : exactInterval 13 1939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1939 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1939) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1939 : oddCount 1939 13 = 6 ∧ acceleratedOrbit 13 1939 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1939 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1939) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1939.1, data_13_1939.2]

end Collatz.Research.StoppingAtlas.Batch0593
