import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0884

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28934. -/
theorem bounds_15_28934 : exactInterval 15 28934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28934 : oddCount 28934 15 = 7 ∧ acceleratedOrbit 15 28934 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28934) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28934.1, data_15_28934.2]

/-- Complete interval computation for depth 15, residue 28935. -/
theorem bounds_15_28935 : exactInterval 15 28935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28935 : oddCount 28935 15 = 8 ∧ acceleratedOrbit 15 28935 = 5794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28935) = 3 ^ 8 * m + 5794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28935.1, data_15_28935.2]

/-- Complete interval computation for depth 15, residue 28936. -/
theorem bounds_15_28936 : exactInterval 15 28936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28936 : oddCount 28936 15 = 7 ∧ acceleratedOrbit 15 28936 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28936) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28936.1, data_15_28936.2]

/-- Complete interval computation for depth 15, residue 28937. -/
theorem bounds_15_28937 : exactInterval 15 28937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28937 : oddCount 28937 15 = 8 ∧ acceleratedOrbit 15 28937 = 5795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28937) = 3 ^ 8 * m + 5795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28937.1, data_15_28937.2]

/-- Complete interval computation for depth 15, residue 28938. -/
theorem bounds_15_28938 : exactInterval 15 28938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28938 : oddCount 28938 15 = 7 ∧ acceleratedOrbit 15 28938 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28938) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28938.1, data_15_28938.2]

/-- Complete interval computation for depth 15, residue 28939. -/
theorem bounds_15_28939 : exactInterval 15 28939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28939 : oddCount 28939 15 = 6 ∧ acceleratedOrbit 15 28939 = 644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28939) = 3 ^ 6 * m + 644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28939.1, data_15_28939.2]

/-- Complete interval computation for depth 15, residue 28940. -/
theorem bounds_15_28940 : exactInterval 15 28940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28940 : oddCount 28940 15 = 7 ∧ acceleratedOrbit 15 28940 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28940) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28940.1, data_15_28940.2]

/-- Complete interval computation for depth 15, residue 28941. -/
theorem bounds_15_28941 : exactInterval 15 28941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28941 : oddCount 28941 15 = 7 ∧ acceleratedOrbit 15 28941 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28941) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28941.1, data_15_28941.2]

/-- Complete interval computation for depth 15, residue 28942. -/
theorem bounds_15_28942 : exactInterval 15 28942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28942 : oddCount 28942 15 = 6 ∧ acceleratedOrbit 15 28942 = 644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28942) = 3 ^ 6 * m + 644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28942.1, data_15_28942.2]

/-- Complete interval computation for depth 15, residue 28943. -/
theorem bounds_15_28943 : exactInterval 15 28943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28943 : oddCount 28943 15 = 6 ∧ acceleratedOrbit 15 28943 = 644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28943) = 3 ^ 6 * m + 644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28943.1, data_15_28943.2]

/-- Complete interval computation for depth 15, residue 28944. -/
theorem bounds_15_28944 : exactInterval 15 28944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28944 : oddCount 28944 15 = 6 ∧ acceleratedOrbit 15 28944 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28944) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28944.1, data_15_28944.2]

/-- Complete interval computation for depth 15, residue 28945. -/
theorem bounds_15_28945 : exactInterval 15 28945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28945 : oddCount 28945 15 = 7 ∧ acceleratedOrbit 15 28945 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28945) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28945.1, data_15_28945.2]

/-- Complete interval computation for depth 15, residue 28946. -/
theorem bounds_15_28946 : exactInterval 15 28946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28946 : oddCount 28946 15 = 9 ∧ acceleratedOrbit 15 28946 = 17390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28946) = 3 ^ 9 * m + 17390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28946.1, data_15_28946.2]

/-- Complete interval computation for depth 15, residue 28947. -/
theorem bounds_15_28947 : exactInterval 15 28947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28947 : oddCount 28947 15 = 9 ∧ acceleratedOrbit 15 28947 = 17390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28947) = 3 ^ 9 * m + 17390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28947.1, data_15_28947.2]

/-- Complete interval computation for depth 15, residue 28948. -/
theorem bounds_15_28948 : exactInterval 15 28948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28948 : oddCount 28948 15 = 6 ∧ acceleratedOrbit 15 28948 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28948) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28948.1, data_15_28948.2]

/-- Complete interval computation for depth 15, residue 28949. -/
theorem bounds_15_28949 : exactInterval 15 28949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28949 : oddCount 28949 15 = 6 ∧ acceleratedOrbit 15 28949 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28949) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28949.1, data_15_28949.2]

/-- Complete interval computation for depth 15, residue 28950. -/
theorem bounds_15_28950 : exactInterval 15 28950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28950 : oddCount 28950 15 = 8 ∧ acceleratedOrbit 15 28950 = 5798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28950) = 3 ^ 8 * m + 5798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28950.1, data_15_28950.2]

/-- Complete interval computation for depth 15, residue 28951. -/
theorem bounds_15_28951 : exactInterval 15 28951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28951 : oddCount 28951 15 = 8 ∧ acceleratedOrbit 15 28951 = 5798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28951) = 3 ^ 8 * m + 5798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28951.1, data_15_28951.2]

/-- Complete interval computation for depth 15, residue 28952. -/
theorem bounds_15_28952 : exactInterval 15 28952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28952 : oddCount 28952 15 = 6 ∧ acceleratedOrbit 15 28952 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28952) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28952.1, data_15_28952.2]

/-- Complete interval computation for depth 15, residue 28953. -/
theorem bounds_15_28953 : exactInterval 15 28953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28953 : oddCount 28953 15 = 8 ∧ acceleratedOrbit 15 28953 = 5798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28953) = 3 ^ 8 * m + 5798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28953.1, data_15_28953.2]

/-- Complete interval computation for depth 15, residue 28954. -/
theorem bounds_15_28954 : exactInterval 15 28954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28954 : oddCount 28954 15 = 6 ∧ acceleratedOrbit 15 28954 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28954) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28954.1, data_15_28954.2]

/-- Complete interval computation for depth 15, residue 28955. -/
theorem bounds_15_28955 : exactInterval 15 28955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28955 : oddCount 28955 15 = 10 ∧ acceleratedOrbit 15 28955 = 52181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28955) = 3 ^ 10 * m + 52181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28955.1, data_15_28955.2]

/-- Complete interval computation for depth 15, residue 28956. -/
theorem bounds_15_28956 : exactInterval 15 28956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28956 : oddCount 28956 15 = 7 ∧ acceleratedOrbit 15 28956 = 1933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28956) = 3 ^ 7 * m + 1933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28956.1, data_15_28956.2]

/-- Complete interval computation for depth 15, residue 28957. -/
theorem bounds_15_28957 : exactInterval 15 28957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28957 : oddCount 28957 15 = 7 ∧ acceleratedOrbit 15 28957 = 1933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28957) = 3 ^ 7 * m + 1933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28957.1, data_15_28957.2]

/-- Complete interval computation for depth 15, residue 28958. -/
theorem bounds_15_28958 : exactInterval 15 28958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28958 : oddCount 28958 15 = 7 ∧ acceleratedOrbit 15 28958 = 1933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28958) = 3 ^ 7 * m + 1933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28958.1, data_15_28958.2]

/-- Complete interval computation for depth 15, residue 28959. -/
theorem bounds_15_28959 : exactInterval 15 28959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28959 : oddCount 28959 15 = 10 ∧ acceleratedOrbit 15 28959 = 52190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28959) = 3 ^ 10 * m + 52190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28959.1, data_15_28959.2]

/-- Complete interval computation for depth 15, residue 28960. -/
theorem bounds_15_28960 : exactInterval 15 28960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28960 : oddCount 28960 15 = 7 ∧ acceleratedOrbit 15 28960 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28960) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28960.1, data_15_28960.2]

/-- Complete interval computation for depth 15, residue 28961. -/
theorem bounds_15_28961 : exactInterval 15 28961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28961 : oddCount 28961 15 = 7 ∧ acceleratedOrbit 15 28961 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28961) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28961.1, data_15_28961.2]

/-- Complete interval computation for depth 15, residue 28962. -/
theorem bounds_15_28962 : exactInterval 15 28962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28962 : oddCount 28962 15 = 9 ∧ acceleratedOrbit 15 28962 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28962) = 3 ^ 9 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28962.1, data_15_28962.2]

/-- Complete interval computation for depth 15, residue 28963. -/
theorem bounds_15_28963 : exactInterval 15 28963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28963 : oddCount 28963 15 = 9 ∧ acceleratedOrbit 15 28963 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28963) = 3 ^ 9 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28963.1, data_15_28963.2]

/-- Complete interval computation for depth 15, residue 28964. -/
theorem bounds_15_28964 : exactInterval 15 28964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28964 : oddCount 28964 15 = 9 ∧ acceleratedOrbit 15 28964 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28964) = 3 ^ 9 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28964.1, data_15_28964.2]

/-- Complete interval computation for depth 15, residue 28965. -/
theorem bounds_15_28965 : exactInterval 15 28965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28965 : oddCount 28965 15 = 9 ∧ acceleratedOrbit 15 28965 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28965) = 3 ^ 9 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28965.1, data_15_28965.2]

end Collatz.Research.PassageAtlas.Batch0884
