import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0945

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30932. -/
theorem bounds_15_30932 : exactInterval 15 30932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30932 : oddCount 30932 15 = 3 ∧ acceleratedOrbit 15 30932 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30932) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30932.1, data_15_30932.2]

/-- Complete interval computation for depth 15, residue 30933. -/
theorem bounds_15_30933 : exactInterval 15 30933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30933 : oddCount 30933 15 = 3 ∧ acceleratedOrbit 15 30933 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30933) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30933.1, data_15_30933.2]

/-- Complete interval computation for depth 15, residue 30934. -/
theorem bounds_15_30934 : exactInterval 15 30934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30934 : oddCount 30934 15 = 10 ∧ acceleratedOrbit 15 30934 = 55754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30934) = 3 ^ 10 * m + 55754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30934.1, data_15_30934.2]

/-- Complete interval computation for depth 15, residue 30935. -/
theorem bounds_15_30935 : exactInterval 15 30935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30935 : oddCount 30935 15 = 10 ∧ acceleratedOrbit 15 30935 = 55754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30935) = 3 ^ 10 * m + 55754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30935.1, data_15_30935.2]

/-- Complete interval computation for depth 15, residue 30936. -/
theorem bounds_15_30936 : exactInterval 15 30936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30936 : oddCount 30936 15 = 10 ∧ acceleratedOrbit 15 30936 = 55768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30936) = 3 ^ 10 * m + 55768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30936.1, data_15_30936.2]

/-- Complete interval computation for depth 15, residue 30937. -/
theorem bounds_15_30937 : exactInterval 15 30937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30937 : oddCount 30937 15 = 9 ∧ acceleratedOrbit 15 30937 = 18589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30937) = 3 ^ 9 * m + 18589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30937.1, data_15_30937.2]

/-- Complete interval computation for depth 15, residue 30938. -/
theorem bounds_15_30938 : exactInterval 15 30938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30938 : oddCount 30938 15 = 10 ∧ acceleratedOrbit 15 30938 = 55768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30938) = 3 ^ 10 * m + 55768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30938.1, data_15_30938.2]

/-- Complete interval computation for depth 15, residue 30939. -/
theorem bounds_15_30939 : exactInterval 15 30939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30939 : oddCount 30939 15 = 9 ∧ acceleratedOrbit 15 30939 = 18586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30939) = 3 ^ 9 * m + 18586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30939.1, data_15_30939.2]

/-- Complete interval computation for depth 15, residue 30940. -/
theorem bounds_15_30940 : exactInterval 15 30940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30940 : oddCount 30940 15 = 10 ∧ acceleratedOrbit 15 30940 = 55768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30940) = 3 ^ 10 * m + 55768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30940.1, data_15_30940.2]

/-- Complete interval computation for depth 15, residue 30941. -/
theorem bounds_15_30941 : exactInterval 15 30941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30941 : oddCount 30941 15 = 10 ∧ acceleratedOrbit 15 30941 = 55768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30941) = 3 ^ 10 * m + 55768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30941.1, data_15_30941.2]

/-- Complete interval computation for depth 15, residue 30942. -/
theorem bounds_15_30942 : exactInterval 15 30942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30942 : oddCount 30942 15 = 11 ∧ acceleratedOrbit 15 30942 = 167291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30942) = 3 ^ 11 * m + 167291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30942.1, data_15_30942.2]

/-- Complete interval computation for depth 15, residue 30943. -/
theorem bounds_15_30943 : exactInterval 15 30943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30943 : oddCount 30943 15 = 11 ∧ acceleratedOrbit 15 30943 = 167291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30943) = 3 ^ 11 * m + 167291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30943.1, data_15_30943.2]

/-- Complete interval computation for depth 15, residue 30944. -/
theorem bounds_15_30944 : exactInterval 15 30944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30944 : oddCount 30944 15 = 7 ∧ acceleratedOrbit 15 30944 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30944) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30944.1, data_15_30944.2]

/-- Complete interval computation for depth 15, residue 30945. -/
theorem bounds_15_30945 : exactInterval 15 30945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30945 : oddCount 30945 15 = 12 ∧ acceleratedOrbit 15 30945 = 501916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30945) = 3 ^ 12 * m + 501916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30945.1, data_15_30945.2]

/-- Complete interval computation for depth 15, residue 30946. -/
theorem bounds_15_30946 : exactInterval 15 30946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30946 : oddCount 30946 15 = 3 ∧ acceleratedOrbit 15 30946 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30946) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30946.1, data_15_30946.2]

/-- Complete interval computation for depth 15, residue 30947. -/
theorem bounds_15_30947 : exactInterval 15 30947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30947 : oddCount 30947 15 = 3 ∧ acceleratedOrbit 15 30947 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30947) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30947.1, data_15_30947.2]

/-- Complete interval computation for depth 15, residue 30948. -/
theorem bounds_15_30948 : exactInterval 15 30948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30948 : oddCount 30948 15 = 8 ∧ acceleratedOrbit 15 30948 = 6200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30948) = 3 ^ 8 * m + 6200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30948.1, data_15_30948.2]

/-- Complete interval computation for depth 15, residue 30949. -/
theorem bounds_15_30949 : exactInterval 15 30949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30949 : oddCount 30949 15 = 8 ∧ acceleratedOrbit 15 30949 = 6200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30949) = 3 ^ 8 * m + 6200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30949.1, data_15_30949.2]

/-- Complete interval computation for depth 15, residue 30950. -/
theorem bounds_15_30950 : exactInterval 15 30950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30950 : oddCount 30950 15 = 8 ∧ acceleratedOrbit 15 30950 = 6200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30950) = 3 ^ 8 * m + 6200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30950.1, data_15_30950.2]

/-- Complete interval computation for depth 15, residue 30951. -/
theorem bounds_15_30951 : exactInterval 15 30951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30951 : oddCount 30951 15 = 9 ∧ acceleratedOrbit 15 30951 = 18593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30951) = 3 ^ 9 * m + 18593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30951.1, data_15_30951.2]

/-- Complete interval computation for depth 15, residue 30952. -/
theorem bounds_15_30952 : exactInterval 15 30952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30952 : oddCount 30952 15 = 7 ∧ acceleratedOrbit 15 30952 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30952) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30952.1, data_15_30952.2]

/-- Complete interval computation for depth 15, residue 30953. -/
theorem bounds_15_30953 : exactInterval 15 30953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30953 : oddCount 30953 15 = 7 ∧ acceleratedOrbit 15 30953 = 2066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30953) = 3 ^ 7 * m + 2066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30953.1, data_15_30953.2]

/-- Complete interval computation for depth 15, residue 30954. -/
theorem bounds_15_30954 : exactInterval 15 30954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30954 : oddCount 30954 15 = 7 ∧ acceleratedOrbit 15 30954 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30954) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30954.1, data_15_30954.2]

/-- Complete interval computation for depth 15, residue 30955. -/
theorem bounds_15_30955 : exactInterval 15 30955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30955 : oddCount 30955 15 = 9 ∧ acceleratedOrbit 15 30955 = 18596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30955) = 3 ^ 9 * m + 18596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30955.1, data_15_30955.2]

/-- Complete interval computation for depth 15, residue 30956. -/
theorem bounds_15_30956 : exactInterval 15 30956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30956 : oddCount 30956 15 = 6 ∧ acceleratedOrbit 15 30956 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30956) = 3 ^ 6 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30956.1, data_15_30956.2]

/-- Complete interval computation for depth 15, residue 30957. -/
theorem bounds_15_30957 : exactInterval 15 30957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30957 : oddCount 30957 15 = 6 ∧ acceleratedOrbit 15 30957 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30957) = 3 ^ 6 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30957.1, data_15_30957.2]

/-- Complete interval computation for depth 15, residue 30958. -/
theorem bounds_15_30958 : exactInterval 15 30958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30958 : oddCount 30958 15 = 6 ∧ acceleratedOrbit 15 30958 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30958) = 3 ^ 6 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30958.1, data_15_30958.2]

/-- Complete interval computation for depth 15, residue 30959. -/
theorem bounds_15_30959 : exactInterval 15 30959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30959 : oddCount 30959 15 = 11 ∧ acceleratedOrbit 15 30959 = 167374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30959) = 3 ^ 11 * m + 167374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30959.1, data_15_30959.2]

/-- Complete interval computation for depth 15, residue 30960. -/
theorem bounds_15_30960 : exactInterval 15 30960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30960 : oddCount 30960 15 = 7 ∧ acceleratedOrbit 15 30960 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30960) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30960.1, data_15_30960.2]

/-- Complete interval computation for depth 15, residue 30961. -/
theorem bounds_15_30961 : exactInterval 15 30961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30961 : oddCount 30961 15 = 7 ∧ acceleratedOrbit 15 30961 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30961) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30961.1, data_15_30961.2]

/-- Complete interval computation for depth 15, residue 30962. -/
theorem bounds_15_30962 : exactInterval 15 30962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30962 : oddCount 30962 15 = 9 ∧ acceleratedOrbit 15 30962 = 18602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30962) = 3 ^ 9 * m + 18602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30962.1, data_15_30962.2]

/-- Complete interval computation for depth 15, residue 30963. -/
theorem bounds_15_30963 : exactInterval 15 30963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30963 : oddCount 30963 15 = 9 ∧ acceleratedOrbit 15 30963 = 18602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30963) = 3 ^ 9 * m + 18602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30963.1, data_15_30963.2]

/-- Complete interval computation for depth 15, residue 30964. -/
theorem bounds_15_30964 : exactInterval 15 30964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30964 : oddCount 30964 15 = 7 ∧ acceleratedOrbit 15 30964 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30964) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30964.1, data_15_30964.2]

end Collatz.Research.PassageAtlas.Batch0945
