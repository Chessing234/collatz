import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0976

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31948. -/
theorem bounds_15_31948 : exactInterval 15 31948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31948 : oddCount 31948 15 = 4 ∧ acceleratedOrbit 15 31948 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31948) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31948.1, data_15_31948.2]

/-- Complete interval computation for depth 15, residue 31949. -/
theorem bounds_15_31949 : exactInterval 15 31949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31949 : oddCount 31949 15 = 4 ∧ acceleratedOrbit 15 31949 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31949) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31949.1, data_15_31949.2]

/-- Complete interval computation for depth 15, residue 31950. -/
theorem bounds_15_31950 : exactInterval 15 31950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31950 : oddCount 31950 15 = 10 ∧ acceleratedOrbit 15 31950 = 57581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31950) = 3 ^ 10 * m + 57581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31950.1, data_15_31950.2]

/-- Complete interval computation for depth 15, residue 31951. -/
theorem bounds_15_31951 : exactInterval 15 31951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31951 : oddCount 31951 15 = 10 ∧ acceleratedOrbit 15 31951 = 57581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31951) = 3 ^ 10 * m + 57581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31951.1, data_15_31951.2]

/-- Complete interval computation for depth 15, residue 31952. -/
theorem bounds_15_31952 : exactInterval 15 31952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31952 : oddCount 31952 15 = 5 ∧ acceleratedOrbit 15 31952 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31952) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31952.1, data_15_31952.2]

/-- Complete interval computation for depth 15, residue 31953. -/
theorem bounds_15_31953 : exactInterval 15 31953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31953 : oddCount 31953 15 = 11 ∧ acceleratedOrbit 15 31953 = 172772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31953) = 3 ^ 11 * m + 172772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31953.1, data_15_31953.2]

/-- Complete interval computation for depth 15, residue 31954. -/
theorem bounds_15_31954 : exactInterval 15 31954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31954 : oddCount 31954 15 = 11 ∧ acceleratedOrbit 15 31954 = 172772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31954) = 3 ^ 11 * m + 172772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31954.1, data_15_31954.2]

/-- Complete interval computation for depth 15, residue 31955. -/
theorem bounds_15_31955 : exactInterval 15 31955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31955 : oddCount 31955 15 = 11 ∧ acceleratedOrbit 15 31955 = 172772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31955) = 3 ^ 11 * m + 172772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31955.1, data_15_31955.2]

/-- Complete interval computation for depth 15, residue 31956. -/
theorem bounds_15_31956 : exactInterval 15 31956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31956 : oddCount 31956 15 = 5 ∧ acceleratedOrbit 15 31956 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31956) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31956.1, data_15_31956.2]

/-- Complete interval computation for depth 15, residue 31957. -/
theorem bounds_15_31957 : exactInterval 15 31957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31957 : oddCount 31957 15 = 5 ∧ acceleratedOrbit 15 31957 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31957) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31957.1, data_15_31957.2]

/-- Complete interval computation for depth 15, residue 31958. -/
theorem bounds_15_31958 : exactInterval 15 31958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31958 : oddCount 31958 15 = 8 ∧ acceleratedOrbit 15 31958 = 6400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31958) = 3 ^ 8 * m + 6400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31958.1, data_15_31958.2]

/-- Complete interval computation for depth 15, residue 31959. -/
theorem bounds_15_31959 : exactInterval 15 31959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31959 : oddCount 31959 15 = 8 ∧ acceleratedOrbit 15 31959 = 6400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31959) = 3 ^ 8 * m + 6400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31959.1, data_15_31959.2]

/-- Complete interval computation for depth 15, residue 31960. -/
theorem bounds_15_31960 : exactInterval 15 31960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31960 : oddCount 31960 15 = 7 ∧ acceleratedOrbit 15 31960 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31960) = 3 ^ 7 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31960.1, data_15_31960.2]

/-- Complete interval computation for depth 15, residue 31961. -/
theorem bounds_15_31961 : exactInterval 15 31961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31961 : oddCount 31961 15 = 7 ∧ acceleratedOrbit 15 31961 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31961) = 3 ^ 7 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31961.1, data_15_31961.2]

/-- Complete interval computation for depth 15, residue 31962. -/
theorem bounds_15_31962 : exactInterval 15 31962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31962 : oddCount 31962 15 = 7 ∧ acceleratedOrbit 15 31962 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31962) = 3 ^ 7 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31962.1, data_15_31962.2]

/-- Complete interval computation for depth 15, residue 31963. -/
theorem bounds_15_31963 : exactInterval 15 31963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31963 : oddCount 31963 15 = 8 ∧ acceleratedOrbit 15 31963 = 6401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31963) = 3 ^ 8 * m + 6401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31963.1, data_15_31963.2]

/-- Complete interval computation for depth 15, residue 31964. -/
theorem bounds_15_31964 : exactInterval 15 31964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31964 : oddCount 31964 15 = 7 ∧ acceleratedOrbit 15 31964 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31964) = 3 ^ 7 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31964.1, data_15_31964.2]

/-- Complete interval computation for depth 15, residue 31965. -/
theorem bounds_15_31965 : exactInterval 15 31965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31965 : oddCount 31965 15 = 7 ∧ acceleratedOrbit 15 31965 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31965) = 3 ^ 7 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31965.1, data_15_31965.2]

/-- Complete interval computation for depth 15, residue 31966. -/
theorem bounds_15_31966 : exactInterval 15 31966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31966 : oddCount 31966 15 = 8 ∧ acceleratedOrbit 15 31966 = 6401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31966) = 3 ^ 8 * m + 6401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31966.1, data_15_31966.2]

/-- Complete interval computation for depth 15, residue 31967. -/
theorem bounds_15_31967 : exactInterval 15 31967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31967 : oddCount 31967 15 = 8 ∧ acceleratedOrbit 15 31967 = 6401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31967) = 3 ^ 8 * m + 6401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31967.1, data_15_31967.2]

/-- Complete interval computation for depth 15, residue 31968. -/
theorem bounds_15_31968 : exactInterval 15 31968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31968 : oddCount 31968 15 = 6 ∧ acceleratedOrbit 15 31968 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31968) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31968.1, data_15_31968.2]

/-- Complete interval computation for depth 15, residue 31969. -/
theorem bounds_15_31969 : exactInterval 15 31969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31969 : oddCount 31969 15 = 9 ∧ acceleratedOrbit 15 31969 = 19205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31969) = 3 ^ 9 * m + 19205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31969.1, data_15_31969.2]

/-- Complete interval computation for depth 15, residue 31970. -/
theorem bounds_15_31970 : exactInterval 15 31970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31970 : oddCount 31970 15 = 5 ∧ acceleratedOrbit 15 31970 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31970) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31970.1, data_15_31970.2]

/-- Complete interval computation for depth 15, residue 31971. -/
theorem bounds_15_31971 : exactInterval 15 31971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31971 : oddCount 31971 15 = 5 ∧ acceleratedOrbit 15 31971 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31971) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31971.1, data_15_31971.2]

/-- Complete interval computation for depth 15, residue 31972. -/
theorem bounds_15_31972 : exactInterval 15 31972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31972 : oddCount 31972 15 = 7 ∧ acceleratedOrbit 15 31972 = 2135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31972) = 3 ^ 7 * m + 2135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31972.1, data_15_31972.2]

/-- Complete interval computation for depth 15, residue 31973. -/
theorem bounds_15_31973 : exactInterval 15 31973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31973 : oddCount 31973 15 = 7 ∧ acceleratedOrbit 15 31973 = 2135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31973) = 3 ^ 7 * m + 2135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31973.1, data_15_31973.2]

/-- Complete interval computation for depth 15, residue 31974. -/
theorem bounds_15_31974 : exactInterval 15 31974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31974 : oddCount 31974 15 = 7 ∧ acceleratedOrbit 15 31974 = 2135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31974) = 3 ^ 7 * m + 2135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31974.1, data_15_31974.2]

/-- Complete interval computation for depth 15, residue 31975. -/
theorem bounds_15_31975 : exactInterval 15 31975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31975 : oddCount 31975 15 = 9 ∧ acceleratedOrbit 15 31975 = 19208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31975) = 3 ^ 9 * m + 19208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31975.1, data_15_31975.2]

/-- Complete interval computation for depth 15, residue 31976. -/
theorem bounds_15_31976 : exactInterval 15 31976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31976 : oddCount 31976 15 = 6 ∧ acceleratedOrbit 15 31976 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31976) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31976.1, data_15_31976.2]

/-- Complete interval computation for depth 15, residue 31977. -/
theorem bounds_15_31977 : exactInterval 15 31977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31977 : oddCount 31977 15 = 9 ∧ acceleratedOrbit 15 31977 = 19210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31977) = 3 ^ 9 * m + 19210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31977.1, data_15_31977.2]

/-- Complete interval computation for depth 15, residue 31978. -/
theorem bounds_15_31978 : exactInterval 15 31978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31978 : oddCount 31978 15 = 6 ∧ acceleratedOrbit 15 31978 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31978) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31978.1, data_15_31978.2]

/-- Complete interval computation for depth 15, residue 31979. -/
theorem bounds_15_31979 : exactInterval 15 31979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31979 : oddCount 31979 15 = 11 ∧ acceleratedOrbit 15 31979 = 172894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31979) = 3 ^ 11 * m + 172894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31979.1, data_15_31979.2]

/-- Complete interval computation for depth 15, residue 31980. -/
theorem bounds_15_31980 : exactInterval 15 31980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31980 : oddCount 31980 15 = 6 ∧ acceleratedOrbit 15 31980 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31980) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31980.1, data_15_31980.2]

end Collatz.Research.PassageAtlas.Batch0976
