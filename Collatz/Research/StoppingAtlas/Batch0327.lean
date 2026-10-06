import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0327

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1935. -/
theorem bounds_12_1935 : exactInterval 12 1935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1935 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1935) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1935 : oddCount 1935 12 = 8 ∧ acceleratedOrbit 12 1935 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1935 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1935) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1935.1, data_12_1935.2]

/-- Complete interval computation for depth 12, residue 1936. -/
theorem bounds_12_1936 : exactInterval 12 1936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1936 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1936) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1936 : oddCount 1936 12 = 6 ∧ acceleratedOrbit 12 1936 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1936 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1936) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1936.1, data_12_1936.2]

/-- Complete interval computation for depth 12, residue 1937. -/
theorem bounds_12_1937 : exactInterval 12 1937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1937 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1937) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1937 : oddCount 1937 12 = 6 ∧ acceleratedOrbit 12 1937 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1937 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1937) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1937.1, data_12_1937.2]

/-- Complete interval computation for depth 12, residue 1938. -/
theorem bounds_12_1938 : exactInterval 12 1938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1938 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1938) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1938 : oddCount 1938 12 = 6 ∧ acceleratedOrbit 12 1938 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1938 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1938) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1938.1, data_12_1938.2]

/-- Complete interval computation for depth 12, residue 1939. -/
theorem bounds_12_1939 : exactInterval 12 1939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1939 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1939) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1939 : oddCount 1939 12 = 6 ∧ acceleratedOrbit 12 1939 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1939 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1939) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1939.1, data_12_1939.2]

/-- Complete interval computation for depth 12, residue 1940. -/
theorem bounds_12_1940 : exactInterval 12 1940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1940 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1940) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1940 : oddCount 1940 12 = 6 ∧ acceleratedOrbit 12 1940 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1940 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1940) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1940.1, data_12_1940.2]

/-- Complete interval computation for depth 12, residue 1941. -/
theorem bounds_12_1941 : exactInterval 12 1941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1941 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1941) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1941 : oddCount 1941 12 = 6 ∧ acceleratedOrbit 12 1941 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1941 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1941) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1941.1, data_12_1941.2]

/-- Complete interval computation for depth 12, residue 1942. -/
theorem bounds_12_1942 : exactInterval 12 1942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1942 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1942) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1942 : oddCount 1942 12 = 5 ∧ acceleratedOrbit 12 1942 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1942 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1942) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1942.1, data_12_1942.2]

/-- Complete interval computation for depth 12, residue 1943. -/
theorem bounds_12_1943 : exactInterval 12 1943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1943 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1943) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1943 : oddCount 1943 12 = 5 ∧ acceleratedOrbit 12 1943 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1943 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1943) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1943.1, data_12_1943.2]

/-- Complete interval computation for depth 12, residue 1944. -/
theorem bounds_12_1944 : exactInterval 12 1944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1944 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1944) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1944 : oddCount 1944 12 = 6 ∧ acceleratedOrbit 12 1944 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1944 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1944) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1944.1, data_12_1944.2]

/-- Complete interval computation for depth 12, residue 1945. -/
theorem bounds_12_1945 : exactInterval 12 1945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1945 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1945) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1945 : oddCount 1945 12 = 5 ∧ acceleratedOrbit 12 1945 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1945 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1945) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1945.1, data_12_1945.2]

/-- Complete interval computation for depth 12, residue 1946. -/
theorem bounds_12_1946 : exactInterval 12 1946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1946 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1946) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1946 : oddCount 1946 12 = 6 ∧ acceleratedOrbit 12 1946 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1946 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1946) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1946.1, data_12_1946.2]

/-- Complete interval computation for depth 12, residue 1947. -/
theorem bounds_12_1947 : exactInterval 12 1947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1947 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1947) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1947 : oddCount 1947 12 = 8 ∧ acceleratedOrbit 12 1947 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1947 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1947) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1947.1, data_12_1947.2]

/-- Complete interval computation for depth 12, residue 1948. -/
theorem bounds_12_1948 : exactInterval 12 1948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1948 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1948) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1948 : oddCount 1948 12 = 7 ∧ acceleratedOrbit 12 1948 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1948 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1948) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1948.1, data_12_1948.2]

/-- Complete interval computation for depth 12, residue 1949. -/
theorem bounds_12_1949 : exactInterval 12 1949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1949 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1949) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1949 : oddCount 1949 12 = 7 ∧ acceleratedOrbit 12 1949 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1949 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1949) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1949.1, data_12_1949.2]

end Collatz.Research.StoppingAtlas.Batch0327
