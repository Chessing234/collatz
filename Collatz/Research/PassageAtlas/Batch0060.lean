import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0060

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1933. -/
theorem bounds_15_1933 : exactInterval 15 1933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1933 : oddCount 1933 15 = 4 ∧ acceleratedOrbit 15 1933 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1933) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1933.1, data_15_1933.2]

/-- Complete interval computation for depth 15, residue 1934. -/
theorem bounds_15_1934 : exactInterval 15 1934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1934 : oddCount 1934 15 = 8 ∧ acceleratedOrbit 15 1934 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1934) = 3 ^ 8 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1934.1, data_15_1934.2]

/-- Complete interval computation for depth 15, residue 1935. -/
theorem bounds_15_1935 : exactInterval 15 1935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1935 : oddCount 1935 15 = 8 ∧ acceleratedOrbit 15 1935 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1935) = 3 ^ 8 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1935.1, data_15_1935.2]

/-- Complete interval computation for depth 15, residue 1936. -/
theorem bounds_15_1936 : exactInterval 15 1936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1936 : oddCount 1936 15 = 8 ∧ acceleratedOrbit 15 1936 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1936) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1936.1, data_15_1936.2]

/-- Complete interval computation for depth 15, residue 1937. -/
theorem bounds_15_1937 : exactInterval 15 1937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1937 : oddCount 1937 15 = 7 ∧ acceleratedOrbit 15 1937 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1937) = 3 ^ 7 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1937.1, data_15_1937.2]

/-- Complete interval computation for depth 15, residue 1938. -/
theorem bounds_15_1938 : exactInterval 15 1938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1938 : oddCount 1938 15 = 7 ∧ acceleratedOrbit 15 1938 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1938) = 3 ^ 7 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1938.1, data_15_1938.2]

/-- Complete interval computation for depth 15, residue 1939. -/
theorem bounds_15_1939 : exactInterval 15 1939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1939 : oddCount 1939 15 = 7 ∧ acceleratedOrbit 15 1939 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1939) = 3 ^ 7 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1939.1, data_15_1939.2]

/-- Complete interval computation for depth 15, residue 1940. -/
theorem bounds_15_1940 : exactInterval 15 1940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1940 : oddCount 1940 15 = 8 ∧ acceleratedOrbit 15 1940 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1940) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1940.1, data_15_1940.2]

/-- Complete interval computation for depth 15, residue 1941. -/
theorem bounds_15_1941 : exactInterval 15 1941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1941 : oddCount 1941 15 = 8 ∧ acceleratedOrbit 15 1941 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1941) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1941.1, data_15_1941.2]

/-- Complete interval computation for depth 15, residue 1942. -/
theorem bounds_15_1942 : exactInterval 15 1942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1942 : oddCount 1942 15 = 6 ∧ acceleratedOrbit 15 1942 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1942) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1942.1, data_15_1942.2]

/-- Complete interval computation for depth 15, residue 1943. -/
theorem bounds_15_1943 : exactInterval 15 1943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1943 : oddCount 1943 15 = 6 ∧ acceleratedOrbit 15 1943 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1943) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1943.1, data_15_1943.2]

/-- Complete interval computation for depth 15, residue 1944. -/
theorem bounds_15_1944 : exactInterval 15 1944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1944 : oddCount 1944 15 = 8 ∧ acceleratedOrbit 15 1944 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1944) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1944.1, data_15_1944.2]

/-- Complete interval computation for depth 15, residue 1945. -/
theorem bounds_15_1945 : exactInterval 15 1945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1945 : oddCount 1945 15 = 6 ∧ acceleratedOrbit 15 1945 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1945) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1945.1, data_15_1945.2]

/-- Complete interval computation for depth 15, residue 1946. -/
theorem bounds_15_1946 : exactInterval 15 1946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1946 : oddCount 1946 15 = 8 ∧ acceleratedOrbit 15 1946 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1946) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1946.1, data_15_1946.2]

/-- Complete interval computation for depth 15, residue 1947. -/
theorem bounds_15_1947 : exactInterval 15 1947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1947 : oddCount 1947 15 = 9 ∧ acceleratedOrbit 15 1947 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1947) = 3 ^ 9 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1947.1, data_15_1947.2]

/-- Complete interval computation for depth 15, residue 1948. -/
theorem bounds_15_1948 : exactInterval 15 1948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1948 : oddCount 1948 15 = 9 ∧ acceleratedOrbit 15 1948 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1948) = 3 ^ 9 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1948.1, data_15_1948.2]

/-- Complete interval computation for depth 15, residue 1949. -/
theorem bounds_15_1949 : exactInterval 15 1949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1949 : oddCount 1949 15 = 9 ∧ acceleratedOrbit 15 1949 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1949) = 3 ^ 9 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1949.1, data_15_1949.2]

/-- Complete interval computation for depth 15, residue 1950. -/
theorem bounds_15_1950 : exactInterval 15 1950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1950 : oddCount 1950 15 = 9 ∧ acceleratedOrbit 15 1950 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1950) = 3 ^ 9 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1950.1, data_15_1950.2]

/-- Complete interval computation for depth 15, residue 1951. -/
theorem bounds_15_1951 : exactInterval 15 1951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1951 : oddCount 1951 15 = 11 ∧ acceleratedOrbit 15 1951 = 10556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1951) = 3 ^ 11 * m + 10556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1951.1, data_15_1951.2]

/-- Complete interval computation for depth 15, residue 1952. -/
theorem bounds_15_1952 : exactInterval 15 1952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1952 : oddCount 1952 15 = 4 ∧ acceleratedOrbit 15 1952 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1952) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1952.1, data_15_1952.2]

/-- Complete interval computation for depth 15, residue 1953. -/
theorem bounds_15_1953 : exactInterval 15 1953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1953 : oddCount 1953 15 = 6 ∧ acceleratedOrbit 15 1953 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1953) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1953.1, data_15_1953.2]

/-- Complete interval computation for depth 15, residue 1954. -/
theorem bounds_15_1954 : exactInterval 15 1954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1954 : oddCount 1954 15 = 8 ∧ acceleratedOrbit 15 1954 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1954) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1954.1, data_15_1954.2]

/-- Complete interval computation for depth 15, residue 1955. -/
theorem bounds_15_1955 : exactInterval 15 1955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1955 : oddCount 1955 15 = 8 ∧ acceleratedOrbit 15 1955 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1955) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1955.1, data_15_1955.2]

/-- Complete interval computation for depth 15, residue 1956. -/
theorem bounds_15_1956 : exactInterval 15 1956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1956 : oddCount 1956 15 = 7 ∧ acceleratedOrbit 15 1956 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1956) = 3 ^ 7 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1956.1, data_15_1956.2]

/-- Complete interval computation for depth 15, residue 1957. -/
theorem bounds_15_1957 : exactInterval 15 1957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1957 : oddCount 1957 15 = 7 ∧ acceleratedOrbit 15 1957 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1957) = 3 ^ 7 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1957.1, data_15_1957.2]

/-- Complete interval computation for depth 15, residue 1958. -/
theorem bounds_15_1958 : exactInterval 15 1958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1958 : oddCount 1958 15 = 7 ∧ acceleratedOrbit 15 1958 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1958) = 3 ^ 7 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1958.1, data_15_1958.2]

/-- Complete interval computation for depth 15, residue 1959. -/
theorem bounds_15_1959 : exactInterval 15 1959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1959 : oddCount 1959 15 = 11 ∧ acceleratedOrbit 15 1959 = 10601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1959) = 3 ^ 11 * m + 10601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1959.1, data_15_1959.2]

/-- Complete interval computation for depth 15, residue 1960. -/
theorem bounds_15_1960 : exactInterval 15 1960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1960 : oddCount 1960 15 = 4 ∧ acceleratedOrbit 15 1960 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1960) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1960.1, data_15_1960.2]

/-- Complete interval computation for depth 15, residue 1961. -/
theorem bounds_15_1961 : exactInterval 15 1961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1961 : oddCount 1961 15 = 13 ∧ acceleratedOrbit 15 1961 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1961) = 3 ^ 13 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1961.1, data_15_1961.2]

/-- Complete interval computation for depth 15, residue 1962. -/
theorem bounds_15_1962 : exactInterval 15 1962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1962 : oddCount 1962 15 = 4 ∧ acceleratedOrbit 15 1962 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1962) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1962.1, data_15_1962.2]

/-- Complete interval computation for depth 15, residue 1963. -/
theorem bounds_15_1963 : exactInterval 15 1963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1963 : oddCount 1963 15 = 9 ∧ acceleratedOrbit 15 1963 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1963) = 3 ^ 9 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1963.1, data_15_1963.2]

/-- Complete interval computation for depth 15, residue 1964. -/
theorem bounds_15_1964 : exactInterval 15 1964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1964 : oddCount 1964 15 = 10 ∧ acceleratedOrbit 15 1964 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1964) = 3 ^ 10 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1964.1, data_15_1964.2]

/-- Complete interval computation for depth 15, residue 1965. -/
theorem bounds_15_1965 : exactInterval 15 1965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1965 : oddCount 1965 15 = 10 ∧ acceleratedOrbit 15 1965 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1965) = 3 ^ 10 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1965.1, data_15_1965.2]

end Collatz.Research.PassageAtlas.Batch0060
