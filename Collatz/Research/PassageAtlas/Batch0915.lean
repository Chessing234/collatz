import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0915

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29949. -/
theorem bounds_15_29949 : exactInterval 15 29949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29949 : oddCount 29949 15 = 9 ∧ acceleratedOrbit 15 29949 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29949) = 3 ^ 9 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29949.1, data_15_29949.2]

/-- Complete interval computation for depth 15, residue 29950. -/
theorem bounds_15_29950 : exactInterval 15 29950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29950 : oddCount 29950 15 = 10 ∧ acceleratedOrbit 15 29950 = 53975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29950) = 3 ^ 10 * m + 53975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29950.1, data_15_29950.2]

/-- Complete interval computation for depth 15, residue 29951. -/
theorem bounds_15_29951 : exactInterval 15 29951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29951 : oddCount 29951 15 = 10 ∧ acceleratedOrbit 15 29951 = 53975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29951) = 3 ^ 10 * m + 53975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29951.1, data_15_29951.2]

/-- Complete interval computation for depth 15, residue 29952. -/
theorem bounds_15_29952 : exactInterval 15 29952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29952 : oddCount 29952 15 = 3 ∧ acceleratedOrbit 15 29952 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29952) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29952.1, data_15_29952.2]

/-- Complete interval computation for depth 15, residue 29953. -/
theorem bounds_15_29953 : exactInterval 15 29953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29953 : oddCount 29953 15 = 7 ∧ acceleratedOrbit 15 29953 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29953) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29953.1, data_15_29953.2]

/-- Complete interval computation for depth 15, residue 29954. -/
theorem bounds_15_29954 : exactInterval 15 29954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29954 : oddCount 29954 15 = 8 ∧ acceleratedOrbit 15 29954 = 5999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29954) = 3 ^ 8 * m + 5999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29954.1, data_15_29954.2]

/-- Complete interval computation for depth 15, residue 29955. -/
theorem bounds_15_29955 : exactInterval 15 29955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29955 : oddCount 29955 15 = 8 ∧ acceleratedOrbit 15 29955 = 5999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29955) = 3 ^ 8 * m + 5999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29955.1, data_15_29955.2]

/-- Complete interval computation for depth 15, residue 29956. -/
theorem bounds_15_29956 : exactInterval 15 29956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29956 : oddCount 29956 15 = 6 ∧ acceleratedOrbit 15 29956 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29956) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29956.1, data_15_29956.2]

/-- Complete interval computation for depth 15, residue 29957. -/
theorem bounds_15_29957 : exactInterval 15 29957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29957 : oddCount 29957 15 = 6 ∧ acceleratedOrbit 15 29957 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29957) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29957.1, data_15_29957.2]

/-- Complete interval computation for depth 15, residue 29958. -/
theorem bounds_15_29958 : exactInterval 15 29958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29958 : oddCount 29958 15 = 6 ∧ acceleratedOrbit 15 29958 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29958) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29958.1, data_15_29958.2]

/-- Complete interval computation for depth 15, residue 29959. -/
theorem bounds_15_29959 : exactInterval 15 29959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29959 : oddCount 29959 15 = 8 ∧ acceleratedOrbit 15 29959 = 5999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29959) = 3 ^ 8 * m + 5999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29959.1, data_15_29959.2]

/-- Complete interval computation for depth 15, residue 29960. -/
theorem bounds_15_29960 : exactInterval 15 29960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29960 : oddCount 29960 15 = 6 ∧ acceleratedOrbit 15 29960 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29960) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29960.1, data_15_29960.2]

/-- Complete interval computation for depth 15, residue 29961. -/
theorem bounds_15_29961 : exactInterval 15 29961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29961 : oddCount 29961 15 = 9 ∧ acceleratedOrbit 15 29961 = 17999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29961) = 3 ^ 9 * m + 17999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29961.1, data_15_29961.2]

/-- Complete interval computation for depth 15, residue 29962. -/
theorem bounds_15_29962 : exactInterval 15 29962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29962 : oddCount 29962 15 = 6 ∧ acceleratedOrbit 15 29962 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29962) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29962.1, data_15_29962.2]

/-- Complete interval computation for depth 15, residue 29963. -/
theorem bounds_15_29963 : exactInterval 15 29963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29963 : oddCount 29963 15 = 9 ∧ acceleratedOrbit 15 29963 = 18002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29963) = 3 ^ 9 * m + 18002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29963.1, data_15_29963.2]

/-- Complete interval computation for depth 15, residue 29964. -/
theorem bounds_15_29964 : exactInterval 15 29964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29964 : oddCount 29964 15 = 6 ∧ acceleratedOrbit 15 29964 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29964) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29964.1, data_15_29964.2]

/-- Complete interval computation for depth 15, residue 29965. -/
theorem bounds_15_29965 : exactInterval 15 29965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29965 : oddCount 29965 15 = 6 ∧ acceleratedOrbit 15 29965 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29965) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29965.1, data_15_29965.2]

/-- Complete interval computation for depth 15, residue 29966. -/
theorem bounds_15_29966 : exactInterval 15 29966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29966 : oddCount 29966 15 = 6 ∧ acceleratedOrbit 15 29966 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29966) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29966.1, data_15_29966.2]

/-- Complete interval computation for depth 15, residue 29967. -/
theorem bounds_15_29967 : exactInterval 15 29967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29967 : oddCount 29967 15 = 6 ∧ acceleratedOrbit 15 29967 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29967) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29967.1, data_15_29967.2]

/-- Complete interval computation for depth 15, residue 29968. -/
theorem bounds_15_29968 : exactInterval 15 29968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29968 : oddCount 29968 15 = 6 ∧ acceleratedOrbit 15 29968 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29968) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29968.1, data_15_29968.2]

/-- Complete interval computation for depth 15, residue 29969. -/
theorem bounds_15_29969 : exactInterval 15 29969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29969 : oddCount 29969 15 = 6 ∧ acceleratedOrbit 15 29969 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29969) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29969.1, data_15_29969.2]

/-- Complete interval computation for depth 15, residue 29970. -/
theorem bounds_15_29970 : exactInterval 15 29970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29970 : oddCount 29970 15 = 8 ∧ acceleratedOrbit 15 29970 = 6002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29970) = 3 ^ 8 * m + 6002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29970.1, data_15_29970.2]

/-- Complete interval computation for depth 15, residue 29971. -/
theorem bounds_15_29971 : exactInterval 15 29971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29971 : oddCount 29971 15 = 8 ∧ acceleratedOrbit 15 29971 = 6002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29971) = 3 ^ 8 * m + 6002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29971.1, data_15_29971.2]

/-- Complete interval computation for depth 15, residue 29972. -/
theorem bounds_15_29972 : exactInterval 15 29972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29972 : oddCount 29972 15 = 6 ∧ acceleratedOrbit 15 29972 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29972) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29972.1, data_15_29972.2]

/-- Complete interval computation for depth 15, residue 29973. -/
theorem bounds_15_29973 : exactInterval 15 29973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29973 : oddCount 29973 15 = 6 ∧ acceleratedOrbit 15 29973 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29973) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29973.1, data_15_29973.2]

/-- Complete interval computation for depth 15, residue 29974. -/
theorem bounds_15_29974 : exactInterval 15 29974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29974 : oddCount 29974 15 = 6 ∧ acceleratedOrbit 15 29974 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29974) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29974.1, data_15_29974.2]

/-- Complete interval computation for depth 15, residue 29975. -/
theorem bounds_15_29975 : exactInterval 15 29975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29975 : oddCount 29975 15 = 6 ∧ acceleratedOrbit 15 29975 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29975) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29975.1, data_15_29975.2]

/-- Complete interval computation for depth 15, residue 29976. -/
theorem bounds_15_29976 : exactInterval 15 29976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29976 : oddCount 29976 15 = 6 ∧ acceleratedOrbit 15 29976 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29976) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29976.1, data_15_29976.2]

/-- Complete interval computation for depth 15, residue 29977. -/
theorem bounds_15_29977 : exactInterval 15 29977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29977 : oddCount 29977 15 = 11 ∧ acceleratedOrbit 15 29977 = 162080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29977) = 3 ^ 11 * m + 162080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29977.1, data_15_29977.2]

/-- Complete interval computation for depth 15, residue 29978. -/
theorem bounds_15_29978 : exactInterval 15 29978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29978 : oddCount 29978 15 = 6 ∧ acceleratedOrbit 15 29978 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29978) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29978.1, data_15_29978.2]

/-- Complete interval computation for depth 15, residue 29979. -/
theorem bounds_15_29979 : exactInterval 15 29979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29979 : oddCount 29979 15 = 12 ∧ acceleratedOrbit 15 29979 = 486233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29979) = 3 ^ 12 * m + 486233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29979.1, data_15_29979.2]

/-- Complete interval computation for depth 15, residue 29980. -/
theorem bounds_15_29980 : exactInterval 15 29980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29980 : oddCount 29980 15 = 8 ∧ acceleratedOrbit 15 29980 = 6004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29980) = 3 ^ 8 * m + 6004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29980.1, data_15_29980.2]

/-- Complete interval computation for depth 15, residue 29981. -/
theorem bounds_15_29981 : exactInterval 15 29981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29981 : oddCount 29981 15 = 8 ∧ acceleratedOrbit 15 29981 = 6004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29981) = 3 ^ 8 * m + 6004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29981.1, data_15_29981.2]

end Collatz.Research.PassageAtlas.Batch0915
