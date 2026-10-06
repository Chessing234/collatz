import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0579

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18939. -/
theorem bounds_15_18939 : exactInterval 15 18939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18939 : oddCount 18939 15 = 8 ∧ acceleratedOrbit 15 18939 = 3793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18939) = 3 ^ 8 * m + 3793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18939.1, data_15_18939.2]

/-- Complete interval computation for depth 15, residue 18940. -/
theorem bounds_15_18940 : exactInterval 15 18940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18940 : oddCount 18940 15 = 10 ∧ acceleratedOrbit 15 18940 = 34138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18940) = 3 ^ 10 * m + 34138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18940.1, data_15_18940.2]

/-- Complete interval computation for depth 15, residue 18941. -/
theorem bounds_15_18941 : exactInterval 15 18941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18941 : oddCount 18941 15 = 10 ∧ acceleratedOrbit 15 18941 = 34138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18941) = 3 ^ 10 * m + 34138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18941.1, data_15_18941.2]

/-- Complete interval computation for depth 15, residue 18942. -/
theorem bounds_15_18942 : exactInterval 15 18942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18942 : oddCount 18942 15 = 10 ∧ acceleratedOrbit 15 18942 = 34138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18942) = 3 ^ 10 * m + 34138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18942.1, data_15_18942.2]

/-- Complete interval computation for depth 15, residue 18943. -/
theorem bounds_15_18943 : exactInterval 15 18943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18943 : oddCount 18943 15 = 13 ∧ acceleratedOrbit 15 18943 = 921719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18943) = 3 ^ 13 * m + 921719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18943.1, data_15_18943.2]

/-- Complete interval computation for depth 15, residue 18944. -/
theorem bounds_15_18944 : exactInterval 15 18944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18944 : oddCount 18944 15 = 3 ∧ acceleratedOrbit 15 18944 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18944) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18944.1, data_15_18944.2]

/-- Complete interval computation for depth 15, residue 18945. -/
theorem bounds_15_18945 : exactInterval 15 18945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18945 : oddCount 18945 15 = 9 ∧ acceleratedOrbit 15 18945 = 11384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18945) = 3 ^ 9 * m + 11384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18945.1, data_15_18945.2]

/-- Complete interval computation for depth 15, residue 18946. -/
theorem bounds_15_18946 : exactInterval 15 18946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18946 : oddCount 18946 15 = 8 ∧ acceleratedOrbit 15 18946 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18946) = 3 ^ 8 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18946.1, data_15_18946.2]

/-- Complete interval computation for depth 15, residue 18947. -/
theorem bounds_15_18947 : exactInterval 15 18947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18947 : oddCount 18947 15 = 8 ∧ acceleratedOrbit 15 18947 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18947) = 3 ^ 8 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18947.1, data_15_18947.2]

/-- Complete interval computation for depth 15, residue 18948. -/
theorem bounds_15_18948 : exactInterval 15 18948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18948 : oddCount 18948 15 = 8 ∧ acceleratedOrbit 15 18948 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18948) = 3 ^ 8 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18948.1, data_15_18948.2]

/-- Complete interval computation for depth 15, residue 18949. -/
theorem bounds_15_18949 : exactInterval 15 18949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18949 : oddCount 18949 15 = 8 ∧ acceleratedOrbit 15 18949 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18949) = 3 ^ 8 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18949.1, data_15_18949.2]

/-- Complete interval computation for depth 15, residue 18950. -/
theorem bounds_15_18950 : exactInterval 15 18950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18950 : oddCount 18950 15 = 8 ∧ acceleratedOrbit 15 18950 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18950) = 3 ^ 8 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18950.1, data_15_18950.2]

/-- Complete interval computation for depth 15, residue 18951. -/
theorem bounds_15_18951 : exactInterval 15 18951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18951 : oddCount 18951 15 = 7 ∧ acceleratedOrbit 15 18951 = 1265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18951) = 3 ^ 7 * m + 1265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18951.1, data_15_18951.2]

/-- Complete interval computation for depth 15, residue 18952. -/
theorem bounds_15_18952 : exactInterval 15 18952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18952 : oddCount 18952 15 = 4 ∧ acceleratedOrbit 15 18952 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18952) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18952.1, data_15_18952.2]

/-- Complete interval computation for depth 15, residue 18953. -/
theorem bounds_15_18953 : exactInterval 15 18953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18953 : oddCount 18953 15 = 8 ∧ acceleratedOrbit 15 18953 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18953) = 3 ^ 8 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18953.1, data_15_18953.2]

/-- Complete interval computation for depth 15, residue 18954. -/
theorem bounds_15_18954 : exactInterval 15 18954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18954 : oddCount 18954 15 = 4 ∧ acceleratedOrbit 15 18954 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18954) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18954.1, data_15_18954.2]

/-- Complete interval computation for depth 15, residue 18955. -/
theorem bounds_15_18955 : exactInterval 15 18955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18955 : oddCount 18955 15 = 8 ∧ acceleratedOrbit 15 18955 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18955) = 3 ^ 8 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18955.1, data_15_18955.2]

/-- Complete interval computation for depth 15, residue 18956. -/
theorem bounds_15_18956 : exactInterval 15 18956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18956 : oddCount 18956 15 = 4 ∧ acceleratedOrbit 15 18956 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18956) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18956.1, data_15_18956.2]

/-- Complete interval computation for depth 15, residue 18957. -/
theorem bounds_15_18957 : exactInterval 15 18957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18957 : oddCount 18957 15 = 4 ∧ acceleratedOrbit 15 18957 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18957) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18957.1, data_15_18957.2]

/-- Complete interval computation for depth 15, residue 18958. -/
theorem bounds_15_18958 : exactInterval 15 18958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18958 : oddCount 18958 15 = 10 ∧ acceleratedOrbit 15 18958 = 34172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18958) = 3 ^ 10 * m + 34172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18958.1, data_15_18958.2]

/-- Complete interval computation for depth 15, residue 18959. -/
theorem bounds_15_18959 : exactInterval 15 18959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18959 : oddCount 18959 15 = 10 ∧ acceleratedOrbit 15 18959 = 34172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18959) = 3 ^ 10 * m + 34172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18959.1, data_15_18959.2]

/-- Complete interval computation for depth 15, residue 18960. -/
theorem bounds_15_18960 : exactInterval 15 18960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18960 : oddCount 18960 15 = 8 ∧ acceleratedOrbit 15 18960 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18960) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18960.1, data_15_18960.2]

/-- Complete interval computation for depth 15, residue 18961. -/
theorem bounds_15_18961 : exactInterval 15 18961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18961 : oddCount 18961 15 = 4 ∧ acceleratedOrbit 15 18961 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18961) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18961.1, data_15_18961.2]

/-- Complete interval computation for depth 15, residue 18962. -/
theorem bounds_15_18962 : exactInterval 15 18962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18962 : oddCount 18962 15 = 10 ∧ acceleratedOrbit 15 18962 = 34181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18962) = 3 ^ 10 * m + 34181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18962.1, data_15_18962.2]

/-- Complete interval computation for depth 15, residue 18963. -/
theorem bounds_15_18963 : exactInterval 15 18963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18963 : oddCount 18963 15 = 10 ∧ acceleratedOrbit 15 18963 = 34181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18963) = 3 ^ 10 * m + 34181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18963.1, data_15_18963.2]

/-- Complete interval computation for depth 15, residue 18964. -/
theorem bounds_15_18964 : exactInterval 15 18964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18964 : oddCount 18964 15 = 8 ∧ acceleratedOrbit 15 18964 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18964) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18964.1, data_15_18964.2]

/-- Complete interval computation for depth 15, residue 18965. -/
theorem bounds_15_18965 : exactInterval 15 18965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18965 : oddCount 18965 15 = 8 ∧ acceleratedOrbit 15 18965 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18965) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18965.1, data_15_18965.2]

/-- Complete interval computation for depth 15, residue 18966. -/
theorem bounds_15_18966 : exactInterval 15 18966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18966 : oddCount 18966 15 = 8 ∧ acceleratedOrbit 15 18966 = 3800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18966) = 3 ^ 8 * m + 3800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18966.1, data_15_18966.2]

/-- Complete interval computation for depth 15, residue 18967. -/
theorem bounds_15_18967 : exactInterval 15 18967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18967 : oddCount 18967 15 = 8 ∧ acceleratedOrbit 15 18967 = 3800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18967) = 3 ^ 8 * m + 3800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18967.1, data_15_18967.2]

/-- Complete interval computation for depth 15, residue 18968. -/
theorem bounds_15_18968 : exactInterval 15 18968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18968 : oddCount 18968 15 = 8 ∧ acceleratedOrbit 15 18968 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18968) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18968.1, data_15_18968.2]

/-- Complete interval computation for depth 15, residue 18969. -/
theorem bounds_15_18969 : exactInterval 15 18969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18969 : oddCount 18969 15 = 8 ∧ acceleratedOrbit 15 18969 = 3800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18969) = 3 ^ 8 * m + 3800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18969.1, data_15_18969.2]

/-- Complete interval computation for depth 15, residue 18970. -/
theorem bounds_15_18970 : exactInterval 15 18970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18970 : oddCount 18970 15 = 8 ∧ acceleratedOrbit 15 18970 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18970) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18970.1, data_15_18970.2]

/-- Complete interval computation for depth 15, residue 18971. -/
theorem bounds_15_18971 : exactInterval 15 18971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18971 : oddCount 18971 15 = 8 ∧ acceleratedOrbit 15 18971 = 3799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18971) = 3 ^ 8 * m + 3799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18971.1, data_15_18971.2]

end Collatz.Research.PassageAtlas.Batch0579
