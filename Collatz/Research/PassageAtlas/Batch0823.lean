import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0823

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26935. -/
theorem bounds_15_26935 : exactInterval 15 26935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26935 : oddCount 26935 15 = 9 ∧ acceleratedOrbit 15 26935 = 16181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26935) = 3 ^ 9 * m + 16181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26935.1, data_15_26935.2]

/-- Complete interval computation for depth 15, residue 26936. -/
theorem bounds_15_26936 : exactInterval 15 26936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26936 : oddCount 26936 15 = 7 ∧ acceleratedOrbit 15 26936 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26936) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26936.1, data_15_26936.2]

/-- Complete interval computation for depth 15, residue 26937. -/
theorem bounds_15_26937 : exactInterval 15 26937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26937 : oddCount 26937 15 = 7 ∧ acceleratedOrbit 15 26937 = 1798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26937) = 3 ^ 7 * m + 1798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26937.1, data_15_26937.2]

/-- Complete interval computation for depth 15, residue 26938. -/
theorem bounds_15_26938 : exactInterval 15 26938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26938 : oddCount 26938 15 = 7 ∧ acceleratedOrbit 15 26938 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26938) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26938.1, data_15_26938.2]

/-- Complete interval computation for depth 15, residue 26939. -/
theorem bounds_15_26939 : exactInterval 15 26939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26939 : oddCount 26939 15 = 7 ∧ acceleratedOrbit 15 26939 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26939) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26939.1, data_15_26939.2]

/-- Complete interval computation for depth 15, residue 26940. -/
theorem bounds_15_26940 : exactInterval 15 26940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26940 : oddCount 26940 15 = 7 ∧ acceleratedOrbit 15 26940 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26940) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26940.1, data_15_26940.2]

/-- Complete interval computation for depth 15, residue 26941. -/
theorem bounds_15_26941 : exactInterval 15 26941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26941 : oddCount 26941 15 = 7 ∧ acceleratedOrbit 15 26941 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26941) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26941.1, data_15_26941.2]

/-- Complete interval computation for depth 15, residue 26942. -/
theorem bounds_15_26942 : exactInterval 15 26942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26942 : oddCount 26942 15 = 11 ∧ acceleratedOrbit 15 26942 = 145664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26942) = 3 ^ 11 * m + 145664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26942.1, data_15_26942.2]

/-- Complete interval computation for depth 15, residue 26943. -/
theorem bounds_15_26943 : exactInterval 15 26943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26943 : oddCount 26943 15 = 11 ∧ acceleratedOrbit 15 26943 = 145664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26943) = 3 ^ 11 * m + 145664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26943.1, data_15_26943.2]

/-- Complete interval computation for depth 15, residue 26944. -/
theorem bounds_15_26944 : exactInterval 15 26944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26944 : oddCount 26944 15 = 5 ∧ acceleratedOrbit 15 26944 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26944) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26944.1, data_15_26944.2]

/-- Complete interval computation for depth 15, residue 26945. -/
theorem bounds_15_26945 : exactInterval 15 26945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26945 : oddCount 26945 15 = 5 ∧ acceleratedOrbit 15 26945 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26945) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26945.1, data_15_26945.2]

/-- Complete interval computation for depth 15, residue 26946. -/
theorem bounds_15_26946 : exactInterval 15 26946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26946 : oddCount 26946 15 = 9 ∧ acceleratedOrbit 15 26946 = 16190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26946) = 3 ^ 9 * m + 16190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26946.1, data_15_26946.2]

/-- Complete interval computation for depth 15, residue 26947. -/
theorem bounds_15_26947 : exactInterval 15 26947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26947 : oddCount 26947 15 = 9 ∧ acceleratedOrbit 15 26947 = 16190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26947) = 3 ^ 9 * m + 16190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26947.1, data_15_26947.2]

/-- Complete interval computation for depth 15, residue 26948. -/
theorem bounds_15_26948 : exactInterval 15 26948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26948 : oddCount 26948 15 = 9 ∧ acceleratedOrbit 15 26948 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26948) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26948.1, data_15_26948.2]

/-- Complete interval computation for depth 15, residue 26949. -/
theorem bounds_15_26949 : exactInterval 15 26949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26949 : oddCount 26949 15 = 9 ∧ acceleratedOrbit 15 26949 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26949) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26949.1, data_15_26949.2]

/-- Complete interval computation for depth 15, residue 26950. -/
theorem bounds_15_26950 : exactInterval 15 26950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26950 : oddCount 26950 15 = 9 ∧ acceleratedOrbit 15 26950 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26950) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26950.1, data_15_26950.2]

/-- Complete interval computation for depth 15, residue 26951. -/
theorem bounds_15_26951 : exactInterval 15 26951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26951 : oddCount 26951 15 = 11 ∧ acceleratedOrbit 15 26951 = 145709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26951) = 3 ^ 11 * m + 145709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26951.1, data_15_26951.2]

/-- Complete interval computation for depth 15, residue 26952. -/
theorem bounds_15_26952 : exactInterval 15 26952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26952 : oddCount 26952 15 = 9 ∧ acceleratedOrbit 15 26952 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26952) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26952.1, data_15_26952.2]

/-- Complete interval computation for depth 15, residue 26953. -/
theorem bounds_15_26953 : exactInterval 15 26953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26953 : oddCount 26953 15 = 9 ∧ acceleratedOrbit 15 26953 = 16193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26953) = 3 ^ 9 * m + 16193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26953.1, data_15_26953.2]

/-- Complete interval computation for depth 15, residue 26954. -/
theorem bounds_15_26954 : exactInterval 15 26954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26954 : oddCount 26954 15 = 9 ∧ acceleratedOrbit 15 26954 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26954) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26954.1, data_15_26954.2]

/-- Complete interval computation for depth 15, residue 26955. -/
theorem bounds_15_26955 : exactInterval 15 26955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26955 : oddCount 26955 15 = 9 ∧ acceleratedOrbit 15 26955 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26955) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26955.1, data_15_26955.2]

/-- Complete interval computation for depth 15, residue 26956. -/
theorem bounds_15_26956 : exactInterval 15 26956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26956 : oddCount 26956 15 = 9 ∧ acceleratedOrbit 15 26956 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26956) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26956.1, data_15_26956.2]

/-- Complete interval computation for depth 15, residue 26957. -/
theorem bounds_15_26957 : exactInterval 15 26957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26957 : oddCount 26957 15 = 9 ∧ acceleratedOrbit 15 26957 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26957) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26957.1, data_15_26957.2]

/-- Complete interval computation for depth 15, residue 26958. -/
theorem bounds_15_26958 : exactInterval 15 26958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26958 : oddCount 26958 15 = 9 ∧ acceleratedOrbit 15 26958 = 16195 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26958) = 3 ^ 9 * m + 16195 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26958.1, data_15_26958.2]

/-- Complete interval computation for depth 15, residue 26959. -/
theorem bounds_15_26959 : exactInterval 15 26959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26959 : oddCount 26959 15 = 9 ∧ acceleratedOrbit 15 26959 = 16195 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26959) = 3 ^ 9 * m + 16195 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26959.1, data_15_26959.2]

/-- Complete interval computation for depth 15, residue 26960. -/
theorem bounds_15_26960 : exactInterval 15 26960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26960 : oddCount 26960 15 = 5 ∧ acceleratedOrbit 15 26960 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26960) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26960.1, data_15_26960.2]

/-- Complete interval computation for depth 15, residue 26961. -/
theorem bounds_15_26961 : exactInterval 15 26961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26961 : oddCount 26961 15 = 10 ∧ acceleratedOrbit 15 26961 = 48593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26961) = 3 ^ 10 * m + 48593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26961.1, data_15_26961.2]

/-- Complete interval computation for depth 15, residue 26962. -/
theorem bounds_15_26962 : exactInterval 15 26962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26962 : oddCount 26962 15 = 10 ∧ acceleratedOrbit 15 26962 = 48593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26962) = 3 ^ 10 * m + 48593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26962.1, data_15_26962.2]

/-- Complete interval computation for depth 15, residue 26963. -/
theorem bounds_15_26963 : exactInterval 15 26963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26963 : oddCount 26963 15 = 10 ∧ acceleratedOrbit 15 26963 = 48593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26963) = 3 ^ 10 * m + 48593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26963.1, data_15_26963.2]

/-- Complete interval computation for depth 15, residue 26964. -/
theorem bounds_15_26964 : exactInterval 15 26964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26964 : oddCount 26964 15 = 5 ∧ acceleratedOrbit 15 26964 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26964) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26964.1, data_15_26964.2]

/-- Complete interval computation for depth 15, residue 26965. -/
theorem bounds_15_26965 : exactInterval 15 26965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26965 : oddCount 26965 15 = 5 ∧ acceleratedOrbit 15 26965 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26965) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26965.1, data_15_26965.2]

/-- Complete interval computation for depth 15, residue 26966. -/
theorem bounds_15_26966 : exactInterval 15 26966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26966 : oddCount 26966 15 = 5 ∧ acceleratedOrbit 15 26966 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26966) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26966.1, data_15_26966.2]

/-- Complete interval computation for depth 15, residue 26967. -/
theorem bounds_15_26967 : exactInterval 15 26967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26967 : oddCount 26967 15 = 5 ∧ acceleratedOrbit 15 26967 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26967) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26967.1, data_15_26967.2]

end Collatz.Research.PassageAtlas.Batch0823
