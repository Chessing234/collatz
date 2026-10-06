import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0193

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1925. -/
theorem bounds_11_1925 : exactInterval 11 1925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1925 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1925) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1925 : oddCount 1925 11 = 6 ∧ acceleratedOrbit 11 1925 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1925 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1925) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1925.1, data_11_1925.2]

/-- Complete interval computation for depth 11, residue 1926. -/
theorem bounds_11_1926 : exactInterval 11 1926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1926 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1926) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1926 : oddCount 1926 11 = 6 ∧ acceleratedOrbit 11 1926 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1926 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1926) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1926.1, data_11_1926.2]

/-- Complete interval computation for depth 11, residue 1927. -/
theorem bounds_11_1927 : exactInterval 11 1927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1927 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1927) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1927 : oddCount 1927 11 = 5 ∧ acceleratedOrbit 11 1927 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1927 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1927) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1927.1, data_11_1927.2]

/-- Complete interval computation for depth 11, residue 1928. -/
theorem bounds_11_1928 : exactInterval 11 1928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1928 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1928) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1928 : oddCount 1928 11 = 3 ∧ acceleratedOrbit 11 1928 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1928 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1928) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1928.1, data_11_1928.2]

/-- Complete interval computation for depth 11, residue 1929. -/
theorem bounds_11_1929 : exactInterval 11 1929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1929 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1929) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1929 : oddCount 1929 11 = 7 ∧ acceleratedOrbit 11 1929 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1929 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1929) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1929.1, data_11_1929.2]

/-- Complete interval computation for depth 11, residue 1930. -/
theorem bounds_11_1930 : exactInterval 11 1930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1930 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1930) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1930 : oddCount 1930 11 = 3 ∧ acceleratedOrbit 11 1930 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1930 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1930) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1930.1, data_11_1930.2]

/-- Complete interval computation for depth 11, residue 1931. -/
theorem bounds_11_1931 : exactInterval 11 1931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1931 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1931) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1931 : oddCount 1931 11 = 7 ∧ acceleratedOrbit 11 1931 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1931 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1931) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1931.1, data_11_1931.2]

/-- Complete interval computation for depth 11, residue 1932. -/
theorem bounds_11_1932 : exactInterval 11 1932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1932 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1932) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1932 : oddCount 1932 11 = 3 ∧ acceleratedOrbit 11 1932 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1932 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1932) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1932.1, data_11_1932.2]

/-- Complete interval computation for depth 11, residue 1933. -/
theorem bounds_11_1933 : exactInterval 11 1933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1933 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1933) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1933 : oddCount 1933 11 = 3 ∧ acceleratedOrbit 11 1933 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1933 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1933) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1933.1, data_11_1933.2]

/-- Complete interval computation for depth 11, residue 1934. -/
theorem bounds_11_1934 : exactInterval 11 1934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1934 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1934) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1934 : oddCount 1934 11 = 7 ∧ acceleratedOrbit 11 1934 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1934 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1934) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1934.1, data_11_1934.2]

/-- Complete interval computation for depth 11, residue 1935. -/
theorem bounds_11_1935 : exactInterval 11 1935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1935 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1935) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1935 : oddCount 1935 11 = 7 ∧ acceleratedOrbit 11 1935 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1935 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1935) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1935.1, data_11_1935.2]

/-- Complete interval computation for depth 11, residue 1936. -/
theorem bounds_11_1936 : exactInterval 11 1936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1936 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1936) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1936 : oddCount 1936 11 = 5 ∧ acceleratedOrbit 11 1936 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1936 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1936) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1936.1, data_11_1936.2]

/-- Complete interval computation for depth 11, residue 1937. -/
theorem bounds_11_1937 : exactInterval 11 1937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1937 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1937) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1937 : oddCount 1937 11 = 6 ∧ acceleratedOrbit 11 1937 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1937 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1937) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1937.1, data_11_1937.2]

/-- Complete interval computation for depth 11, residue 1938. -/
theorem bounds_11_1938 : exactInterval 11 1938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1938 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1938) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1938 : oddCount 1938 11 = 6 ∧ acceleratedOrbit 11 1938 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1938 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1938) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1938.1, data_11_1938.2]

/-- Complete interval computation for depth 11, residue 1939. -/
theorem bounds_11_1939 : exactInterval 11 1939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1939 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1939) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1939 : oddCount 1939 11 = 6 ∧ acceleratedOrbit 11 1939 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1939 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1939) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1939.1, data_11_1939.2]

end Collatz.Research.StoppingAtlas.Batch0193
