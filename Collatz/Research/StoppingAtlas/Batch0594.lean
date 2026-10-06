import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0594

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1940. -/
theorem bounds_13_1940 : exactInterval 13 1940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1940 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1940) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1940 : oddCount 1940 13 = 6 ∧ acceleratedOrbit 13 1940 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1940 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1940) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1940.1, data_13_1940.2]

/-- Complete interval computation for depth 13, residue 1941. -/
theorem bounds_13_1941 : exactInterval 13 1941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1941 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1941) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1941 : oddCount 1941 13 = 6 ∧ acceleratedOrbit 13 1941 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1941 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1941) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1941.1, data_13_1941.2]

/-- Complete interval computation for depth 13, residue 1942. -/
theorem bounds_13_1942 : exactInterval 13 1942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1942 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1942) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1942 : oddCount 1942 13 = 5 ∧ acceleratedOrbit 13 1942 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1942 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1942) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1942.1, data_13_1942.2]

/-- Complete interval computation for depth 13, residue 1943. -/
theorem bounds_13_1943 : exactInterval 13 1943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1943 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1943) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1943 : oddCount 1943 13 = 5 ∧ acceleratedOrbit 13 1943 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1943 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1943) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1943.1, data_13_1943.2]

/-- Complete interval computation for depth 13, residue 1944. -/
theorem bounds_13_1944 : exactInterval 13 1944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1944 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1944) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1944 : oddCount 1944 13 = 6 ∧ acceleratedOrbit 13 1944 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1944 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1944) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1944.1, data_13_1944.2]

/-- Complete interval computation for depth 13, residue 1945. -/
theorem bounds_13_1945 : exactInterval 13 1945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1945 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1945) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1945 : oddCount 1945 13 = 5 ∧ acceleratedOrbit 13 1945 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1945 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1945) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1945.1, data_13_1945.2]

/-- Complete interval computation for depth 13, residue 1946. -/
theorem bounds_13_1946 : exactInterval 13 1946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1946 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1946) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1946 : oddCount 1946 13 = 6 ∧ acceleratedOrbit 13 1946 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1946 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1946) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1946.1, data_13_1946.2]

/-- Complete interval computation for depth 13, residue 1947. -/
theorem bounds_13_1947 : exactInterval 13 1947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1947 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1947) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1947 : oddCount 1947 13 = 8 ∧ acceleratedOrbit 13 1947 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1947 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1947) = 3 ^ 8 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1947.1, data_13_1947.2]

/-- Complete interval computation for depth 13, residue 1948. -/
theorem bounds_13_1948 : exactInterval 13 1948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1948 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1948) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1948 : oddCount 1948 13 = 8 ∧ acceleratedOrbit 13 1948 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1948 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1948) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1948.1, data_13_1948.2]

/-- Complete interval computation for depth 13, residue 1949. -/
theorem bounds_13_1949 : exactInterval 13 1949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1949 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1949) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1949 : oddCount 1949 13 = 8 ∧ acceleratedOrbit 13 1949 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1949 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1949) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1949.1, data_13_1949.2]

/-- Complete interval computation for depth 13, residue 1950. -/
theorem bounds_13_1950 : exactInterval 13 1950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1950 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1950) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1950 : oddCount 1950 13 = 8 ∧ acceleratedOrbit 13 1950 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1950 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1950) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1950.1, data_13_1950.2]

/-- Complete interval computation for depth 13, residue 1951. -/
theorem bounds_13_1951 : exactInterval 13 1951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1951 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1951) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1951 : oddCount 1951 13 = 9 ∧ acceleratedOrbit 13 1951 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1951 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1951) = 3 ^ 9 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1951.1, data_13_1951.2]

/-- Complete interval computation for depth 13, residue 1952. -/
theorem bounds_13_1952 : exactInterval 13 1952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1952 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1952) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1952 : oddCount 1952 13 = 4 ∧ acceleratedOrbit 13 1952 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1952 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1952) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1952.1, data_13_1952.2]

/-- Complete interval computation for depth 13, residue 1953. -/
theorem bounds_13_1953 : exactInterval 13 1953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1953 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1953) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1953 : oddCount 1953 13 = 5 ∧ acceleratedOrbit 13 1953 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1953 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1953) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1953.1, data_13_1953.2]

/-- Complete interval computation for depth 13, residue 1954. -/
theorem bounds_13_1954 : exactInterval 13 1954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1954 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1954) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1954 : oddCount 1954 13 = 6 ∧ acceleratedOrbit 13 1954 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1954 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1954) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1954.1, data_13_1954.2]

end Collatz.Research.StoppingAtlas.Batch0594
