import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0213

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6946. -/
theorem bounds_15_6946 : exactInterval 15 6946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6946 : oddCount 6946 15 = 6 ∧ acceleratedOrbit 15 6946 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6946) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6946.1, data_15_6946.2]

/-- Complete interval computation for depth 15, residue 6947. -/
theorem bounds_15_6947 : exactInterval 15 6947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6947 : oddCount 6947 15 = 6 ∧ acceleratedOrbit 15 6947 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6947) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6947.1, data_15_6947.2]

/-- Complete interval computation for depth 15, residue 6948. -/
theorem bounds_15_6948 : exactInterval 15 6948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6948 : oddCount 6948 15 = 6 ∧ acceleratedOrbit 15 6948 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6948) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6948.1, data_15_6948.2]

/-- Complete interval computation for depth 15, residue 6949. -/
theorem bounds_15_6949 : exactInterval 15 6949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6949 : oddCount 6949 15 = 6 ∧ acceleratedOrbit 15 6949 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6949) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6949.1, data_15_6949.2]

/-- Complete interval computation for depth 15, residue 6950. -/
theorem bounds_15_6950 : exactInterval 15 6950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6950 : oddCount 6950 15 = 6 ∧ acceleratedOrbit 15 6950 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6950) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6950.1, data_15_6950.2]

/-- Complete interval computation for depth 15, residue 6951. -/
theorem bounds_15_6951 : exactInterval 15 6951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6951 : oddCount 6951 15 = 10 ∧ acceleratedOrbit 15 6951 = 12530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6951) = 3 ^ 10 * m + 12530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6951.1, data_15_6951.2]

/-- Complete interval computation for depth 15, residue 6952. -/
theorem bounds_15_6952 : exactInterval 15 6952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6952 : oddCount 6952 15 = 5 ∧ acceleratedOrbit 15 6952 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6952) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6952.1, data_15_6952.2]

/-- Complete interval computation for depth 15, residue 6953. -/
theorem bounds_15_6953 : exactInterval 15 6953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6953 : oddCount 6953 15 = 9 ∧ acceleratedOrbit 15 6953 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6953) = 3 ^ 9 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6953.1, data_15_6953.2]

/-- Complete interval computation for depth 15, residue 6954. -/
theorem bounds_15_6954 : exactInterval 15 6954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6954 : oddCount 6954 15 = 5 ∧ acceleratedOrbit 15 6954 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6954) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6954.1, data_15_6954.2]

/-- Complete interval computation for depth 15, residue 6955. -/
theorem bounds_15_6955 : exactInterval 15 6955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6955 : oddCount 6955 15 = 8 ∧ acceleratedOrbit 15 6955 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6955) = 3 ^ 8 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6955.1, data_15_6955.2]

/-- Complete interval computation for depth 15, residue 6956. -/
theorem bounds_15_6956 : exactInterval 15 6956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6956 : oddCount 6956 15 = 8 ∧ acceleratedOrbit 15 6956 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6956) = 3 ^ 8 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6956.1, data_15_6956.2]

/-- Complete interval computation for depth 15, residue 6957. -/
theorem bounds_15_6957 : exactInterval 15 6957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6957 : oddCount 6957 15 = 8 ∧ acceleratedOrbit 15 6957 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6957) = 3 ^ 8 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6957.1, data_15_6957.2]

/-- Complete interval computation for depth 15, residue 6958. -/
theorem bounds_15_6958 : exactInterval 15 6958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6958 : oddCount 6958 15 = 8 ∧ acceleratedOrbit 15 6958 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6958) = 3 ^ 8 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6958.1, data_15_6958.2]

/-- Complete interval computation for depth 15, residue 6959. -/
theorem bounds_15_6959 : exactInterval 15 6959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6959 : oddCount 6959 15 = 10 ∧ acceleratedOrbit 15 6959 = 12545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6959) = 3 ^ 10 * m + 12545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6959.1, data_15_6959.2]

/-- Complete interval computation for depth 15, residue 6960. -/
theorem bounds_15_6960 : exactInterval 15 6960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6960 : oddCount 6960 15 = 5 ∧ acceleratedOrbit 15 6960 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6960) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6960.1, data_15_6960.2]

/-- Complete interval computation for depth 15, residue 6961. -/
theorem bounds_15_6961 : exactInterval 15 6961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6961 : oddCount 6961 15 = 8 ∧ acceleratedOrbit 15 6961 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6961) = 3 ^ 8 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6961.1, data_15_6961.2]

/-- Complete interval computation for depth 15, residue 6962. -/
theorem bounds_15_6962 : exactInterval 15 6962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6962 : oddCount 6962 15 = 8 ∧ acceleratedOrbit 15 6962 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6962) = 3 ^ 8 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6962.1, data_15_6962.2]

/-- Complete interval computation for depth 15, residue 6963. -/
theorem bounds_15_6963 : exactInterval 15 6963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6963 : oddCount 6963 15 = 8 ∧ acceleratedOrbit 15 6963 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6963) = 3 ^ 8 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6963.1, data_15_6963.2]

/-- Complete interval computation for depth 15, residue 6964. -/
theorem bounds_15_6964 : exactInterval 15 6964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6964 : oddCount 6964 15 = 5 ∧ acceleratedOrbit 15 6964 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6964) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6964.1, data_15_6964.2]

/-- Complete interval computation for depth 15, residue 6965. -/
theorem bounds_15_6965 : exactInterval 15 6965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6965 : oddCount 6965 15 = 5 ∧ acceleratedOrbit 15 6965 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6965) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6965.1, data_15_6965.2]

/-- Complete interval computation for depth 15, residue 6966. -/
theorem bounds_15_6966 : exactInterval 15 6966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6966 : oddCount 6966 15 = 9 ∧ acceleratedOrbit 15 6966 = 4187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6966) = 3 ^ 9 * m + 4187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6966.1, data_15_6966.2]

/-- Complete interval computation for depth 15, residue 6967. -/
theorem bounds_15_6967 : exactInterval 15 6967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6967 : oddCount 6967 15 = 9 ∧ acceleratedOrbit 15 6967 = 4187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6967) = 3 ^ 9 * m + 4187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6967.1, data_15_6967.2]

/-- Complete interval computation for depth 15, residue 6968. -/
theorem bounds_15_6968 : exactInterval 15 6968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6968 : oddCount 6968 15 = 10 ∧ acceleratedOrbit 15 6968 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6968) = 3 ^ 10 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6968.1, data_15_6968.2]

/-- Complete interval computation for depth 15, residue 6969. -/
theorem bounds_15_6969 : exactInterval 15 6969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6969 : oddCount 6969 15 = 8 ∧ acceleratedOrbit 15 6969 = 1396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6969) = 3 ^ 8 * m + 1396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6969.1, data_15_6969.2]

/-- Complete interval computation for depth 15, residue 6970. -/
theorem bounds_15_6970 : exactInterval 15 6970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6970 : oddCount 6970 15 = 10 ∧ acceleratedOrbit 15 6970 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6970) = 3 ^ 10 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6970.1, data_15_6970.2]

/-- Complete interval computation for depth 15, residue 6971. -/
theorem bounds_15_6971 : exactInterval 15 6971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6971 : oddCount 6971 15 = 8 ∧ acceleratedOrbit 15 6971 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6971) = 3 ^ 8 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6971.1, data_15_6971.2]

/-- Complete interval computation for depth 15, residue 6972. -/
theorem bounds_15_6972 : exactInterval 15 6972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6972 : oddCount 6972 15 = 10 ∧ acceleratedOrbit 15 6972 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6972) = 3 ^ 10 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6972.1, data_15_6972.2]

/-- Complete interval computation for depth 15, residue 6973. -/
theorem bounds_15_6973 : exactInterval 15 6973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6973 : oddCount 6973 15 = 10 ∧ acceleratedOrbit 15 6973 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6973) = 3 ^ 10 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6973.1, data_15_6973.2]

/-- Complete interval computation for depth 15, residue 6974. -/
theorem bounds_15_6974 : exactInterval 15 6974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6974 : oddCount 6974 15 = 10 ∧ acceleratedOrbit 15 6974 = 12572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6974) = 3 ^ 10 * m + 12572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6974.1, data_15_6974.2]

/-- Complete interval computation for depth 15, residue 6975. -/
theorem bounds_15_6975 : exactInterval 15 6975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6975 : oddCount 6975 15 = 10 ∧ acceleratedOrbit 15 6975 = 12572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6975) = 3 ^ 10 * m + 12572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6975.1, data_15_6975.2]

/-- Complete interval computation for depth 15, residue 6976. -/
theorem bounds_15_6976 : exactInterval 15 6976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6976 : oddCount 6976 15 = 6 ∧ acceleratedOrbit 15 6976 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6976) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6976.1, data_15_6976.2]

/-- Complete interval computation for depth 15, residue 6977. -/
theorem bounds_15_6977 : exactInterval 15 6977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6977 : oddCount 6977 15 = 5 ∧ acceleratedOrbit 15 6977 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6977) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6977.1, data_15_6977.2]

/-- Complete interval computation for depth 15, residue 6978. -/
theorem bounds_15_6978 : exactInterval 15 6978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6978 : oddCount 6978 15 = 8 ∧ acceleratedOrbit 15 6978 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6978) = 3 ^ 8 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6978.1, data_15_6978.2]

end Collatz.Research.PassageAtlas.Batch0213
