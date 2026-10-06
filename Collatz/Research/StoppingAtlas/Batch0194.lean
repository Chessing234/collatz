import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0194

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1940. -/
theorem bounds_11_1940 : exactInterval 11 1940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1940 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1940) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1940 : oddCount 1940 11 = 5 ∧ acceleratedOrbit 11 1940 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1940 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1940) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1940.1, data_11_1940.2]

/-- Complete interval computation for depth 11, residue 1941. -/
theorem bounds_11_1941 : exactInterval 11 1941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1941 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1941) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1941 : oddCount 1941 11 = 5 ∧ acceleratedOrbit 11 1941 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1941 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1941) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1941.1, data_11_1941.2]

/-- Complete interval computation for depth 11, residue 1942. -/
theorem bounds_11_1942 : exactInterval 11 1942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1942 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1942) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1942 : oddCount 1942 11 = 4 ∧ acceleratedOrbit 11 1942 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1942 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1942) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1942.1, data_11_1942.2]

/-- Complete interval computation for depth 11, residue 1943. -/
theorem bounds_11_1943 : exactInterval 11 1943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1943 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1943) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1943 : oddCount 1943 11 = 4 ∧ acceleratedOrbit 11 1943 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1943 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1943) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1943.1, data_11_1943.2]

/-- Complete interval computation for depth 11, residue 1944. -/
theorem bounds_11_1944 : exactInterval 11 1944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1944 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1944) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1944 : oddCount 1944 11 = 5 ∧ acceleratedOrbit 11 1944 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1944 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1944) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1944.1, data_11_1944.2]

/-- Complete interval computation for depth 11, residue 1945. -/
theorem bounds_11_1945 : exactInterval 11 1945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1945 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1945) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1945 : oddCount 1945 11 = 4 ∧ acceleratedOrbit 11 1945 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1945 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1945) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1945.1, data_11_1945.2]

/-- Complete interval computation for depth 11, residue 1946. -/
theorem bounds_11_1946 : exactInterval 11 1946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1946 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1946) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1946 : oddCount 1946 11 = 5 ∧ acceleratedOrbit 11 1946 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1946 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1946) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1946.1, data_11_1946.2]

/-- Complete interval computation for depth 11, residue 1947. -/
theorem bounds_11_1947 : exactInterval 11 1947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1947 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1947) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1947 : oddCount 1947 11 = 7 ∧ acceleratedOrbit 11 1947 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1947 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1947) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1947.1, data_11_1947.2]

/-- Complete interval computation for depth 11, residue 1948. -/
theorem bounds_11_1948 : exactInterval 11 1948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1948 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1948) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1948 : oddCount 1948 11 = 6 ∧ acceleratedOrbit 11 1948 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1948 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1948) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1948.1, data_11_1948.2]

/-- Complete interval computation for depth 11, residue 1949. -/
theorem bounds_11_1949 : exactInterval 11 1949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1949 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1949) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1949 : oddCount 1949 11 = 6 ∧ acceleratedOrbit 11 1949 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1949 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1949) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1949.1, data_11_1949.2]

/-- Complete interval computation for depth 11, residue 1950. -/
theorem bounds_11_1950 : exactInterval 11 1950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1950 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1950) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1950 : oddCount 1950 11 = 6 ∧ acceleratedOrbit 11 1950 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1950 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1950) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1950.1, data_11_1950.2]

/-- Complete interval computation for depth 11, residue 1951. -/
theorem bounds_11_1951 : exactInterval 11 1951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1951 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1951) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1951 : oddCount 1951 11 = 8 ∧ acceleratedOrbit 11 1951 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1951 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1951) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1951.1, data_11_1951.2]

/-- Complete interval computation for depth 11, residue 1952. -/
theorem bounds_11_1952 : exactInterval 11 1952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1952 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1952) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1952 : oddCount 1952 11 = 4 ∧ acceleratedOrbit 11 1952 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1952 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1952) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1952.1, data_11_1952.2]

/-- Complete interval computation for depth 11, residue 1953. -/
theorem bounds_11_1953 : exactInterval 11 1953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1953 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1953) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1953 : oddCount 1953 11 = 5 ∧ acceleratedOrbit 11 1953 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1953 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1953) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1953.1, data_11_1953.2]

/-- Complete interval computation for depth 11, residue 1954. -/
theorem bounds_11_1954 : exactInterval 11 1954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1954 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1954) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1954 : oddCount 1954 11 = 5 ∧ acceleratedOrbit 11 1954 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1954 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1954) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1954.1, data_11_1954.2]

end Collatz.Research.StoppingAtlas.Batch0194
