import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0152

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4947. -/
theorem bounds_15_4947 : exactInterval 15 4947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4947 : oddCount 4947 15 = 8 ∧ acceleratedOrbit 15 4947 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4947) = 3 ^ 8 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4947.1, data_15_4947.2]

/-- Complete interval computation for depth 15, residue 4948. -/
theorem bounds_15_4948 : exactInterval 15 4948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4948 : oddCount 4948 15 = 4 ∧ acceleratedOrbit 15 4948 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4948) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4948.1, data_15_4948.2]

/-- Complete interval computation for depth 15, residue 4949. -/
theorem bounds_15_4949 : exactInterval 15 4949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4949 : oddCount 4949 15 = 4 ∧ acceleratedOrbit 15 4949 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4949) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4949.1, data_15_4949.2]

/-- Complete interval computation for depth 15, residue 4950. -/
theorem bounds_15_4950 : exactInterval 15 4950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4950 : oddCount 4950 15 = 10 ∧ acceleratedOrbit 15 4950 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4950) = 3 ^ 10 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4950.1, data_15_4950.2]

/-- Complete interval computation for depth 15, residue 4951. -/
theorem bounds_15_4951 : exactInterval 15 4951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4951 : oddCount 4951 15 = 10 ∧ acceleratedOrbit 15 4951 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4951) = 3 ^ 10 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4951.1, data_15_4951.2]

/-- Complete interval computation for depth 15, residue 4952. -/
theorem bounds_15_4952 : exactInterval 15 4952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4952 : oddCount 4952 15 = 7 ∧ acceleratedOrbit 15 4952 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4952) = 3 ^ 7 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4952.1, data_15_4952.2]

/-- Complete interval computation for depth 15, residue 4953. -/
theorem bounds_15_4953 : exactInterval 15 4953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4953 : oddCount 4953 15 = 5 ∧ acceleratedOrbit 15 4953 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4953) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4953.1, data_15_4953.2]

/-- Complete interval computation for depth 15, residue 4954. -/
theorem bounds_15_4954 : exactInterval 15 4954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4954 : oddCount 4954 15 = 7 ∧ acceleratedOrbit 15 4954 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4954) = 3 ^ 7 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4954.1, data_15_4954.2]

/-- Complete interval computation for depth 15, residue 4955. -/
theorem bounds_15_4955 : exactInterval 15 4955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4955 : oddCount 4955 15 = 9 ∧ acceleratedOrbit 15 4955 = 2978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4955) = 3 ^ 9 * m + 2978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4955.1, data_15_4955.2]

/-- Complete interval computation for depth 15, residue 4956. -/
theorem bounds_15_4956 : exactInterval 15 4956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4956 : oddCount 4956 15 = 7 ∧ acceleratedOrbit 15 4956 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4956) = 3 ^ 7 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4956.1, data_15_4956.2]

/-- Complete interval computation for depth 15, residue 4957. -/
theorem bounds_15_4957 : exactInterval 15 4957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4957 : oddCount 4957 15 = 7 ∧ acceleratedOrbit 15 4957 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4957) = 3 ^ 7 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4957.1, data_15_4957.2]

/-- Complete interval computation for depth 15, residue 4958. -/
theorem bounds_15_4958 : exactInterval 15 4958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4958 : oddCount 4958 15 = 8 ∧ acceleratedOrbit 15 4958 = 994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4958) = 3 ^ 8 * m + 994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4958.1, data_15_4958.2]

/-- Complete interval computation for depth 15, residue 4959. -/
theorem bounds_15_4959 : exactInterval 15 4959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4959 : oddCount 4959 15 = 8 ∧ acceleratedOrbit 15 4959 = 994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4959) = 3 ^ 8 * m + 994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4959.1, data_15_4959.2]

/-- Complete interval computation for depth 15, residue 4960. -/
theorem bounds_15_4960 : exactInterval 15 4960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4960 : oddCount 4960 15 = 7 ∧ acceleratedOrbit 15 4960 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4960) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4960.1, data_15_4960.2]

/-- Complete interval computation for depth 15, residue 4961. -/
theorem bounds_15_4961 : exactInterval 15 4961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4961 : oddCount 4961 15 = 11 ∧ acceleratedOrbit 15 4961 = 26837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4961) = 3 ^ 11 * m + 26837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4961.1, data_15_4961.2]

/-- Complete interval computation for depth 15, residue 4962. -/
theorem bounds_15_4962 : exactInterval 15 4962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4962 : oddCount 4962 15 = 5 ∧ acceleratedOrbit 15 4962 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4962) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4962.1, data_15_4962.2]

/-- Complete interval computation for depth 15, residue 4963. -/
theorem bounds_15_4963 : exactInterval 15 4963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4963 : oddCount 4963 15 = 5 ∧ acceleratedOrbit 15 4963 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4963) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4963.1, data_15_4963.2]

/-- Complete interval computation for depth 15, residue 4964. -/
theorem bounds_15_4964 : exactInterval 15 4964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4964 : oddCount 4964 15 = 5 ∧ acceleratedOrbit 15 4964 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4964) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4964.1, data_15_4964.2]

/-- Complete interval computation for depth 15, residue 4965. -/
theorem bounds_15_4965 : exactInterval 15 4965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4965 : oddCount 4965 15 = 5 ∧ acceleratedOrbit 15 4965 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4965) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4965.1, data_15_4965.2]

/-- Complete interval computation for depth 15, residue 4966. -/
theorem bounds_15_4966 : exactInterval 15 4966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4966 : oddCount 4966 15 = 5 ∧ acceleratedOrbit 15 4966 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4966) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4966.1, data_15_4966.2]

/-- Complete interval computation for depth 15, residue 4967. -/
theorem bounds_15_4967 : exactInterval 15 4967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4967 : oddCount 4967 15 = 10 ∧ acceleratedOrbit 15 4967 = 8953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4967) = 3 ^ 10 * m + 8953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4967.1, data_15_4967.2]

/-- Complete interval computation for depth 15, residue 4968. -/
theorem bounds_15_4968 : exactInterval 15 4968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4968 : oddCount 4968 15 = 7 ∧ acceleratedOrbit 15 4968 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4968) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4968.1, data_15_4968.2]

/-- Complete interval computation for depth 15, residue 4969. -/
theorem bounds_15_4969 : exactInterval 15 4969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4969 : oddCount 4969 15 = 9 ∧ acceleratedOrbit 15 4969 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4969) = 3 ^ 9 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4969.1, data_15_4969.2]

/-- Complete interval computation for depth 15, residue 4970. -/
theorem bounds_15_4970 : exactInterval 15 4970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4970 : oddCount 4970 15 = 7 ∧ acceleratedOrbit 15 4970 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4970) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4970.1, data_15_4970.2]

/-- Complete interval computation for depth 15, residue 4971. -/
theorem bounds_15_4971 : exactInterval 15 4971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4971 : oddCount 4971 15 = 8 ∧ acceleratedOrbit 15 4971 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4971) = 3 ^ 8 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4971.1, data_15_4971.2]

/-- Complete interval computation for depth 15, residue 4972. -/
theorem bounds_15_4972 : exactInterval 15 4972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4972 : oddCount 4972 15 = 8 ∧ acceleratedOrbit 15 4972 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4972) = 3 ^ 8 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4972.1, data_15_4972.2]

/-- Complete interval computation for depth 15, residue 4973. -/
theorem bounds_15_4973 : exactInterval 15 4973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4973 : oddCount 4973 15 = 8 ∧ acceleratedOrbit 15 4973 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4973) = 3 ^ 8 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4973.1, data_15_4973.2]

/-- Complete interval computation for depth 15, residue 4974. -/
theorem bounds_15_4974 : exactInterval 15 4974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4974 : oddCount 4974 15 = 8 ∧ acceleratedOrbit 15 4974 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4974) = 3 ^ 8 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4974.1, data_15_4974.2]

/-- Complete interval computation for depth 15, residue 4975. -/
theorem bounds_15_4975 : exactInterval 15 4975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4975 : oddCount 4975 15 = 9 ∧ acceleratedOrbit 15 4975 = 2990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4975) = 3 ^ 9 * m + 2990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4975.1, data_15_4975.2]

/-- Complete interval computation for depth 15, residue 4976. -/
theorem bounds_15_4976 : exactInterval 15 4976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4976 : oddCount 4976 15 = 7 ∧ acceleratedOrbit 15 4976 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4976) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4976.1, data_15_4976.2]

/-- Complete interval computation for depth 15, residue 4977. -/
theorem bounds_15_4977 : exactInterval 15 4977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4977 : oddCount 4977 15 = 7 ∧ acceleratedOrbit 15 4977 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4977) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4977.1, data_15_4977.2]

/-- Complete interval computation for depth 15, residue 4978. -/
theorem bounds_15_4978 : exactInterval 15 4978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4978 : oddCount 4978 15 = 5 ∧ acceleratedOrbit 15 4978 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4978) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4978.1, data_15_4978.2]

/-- Complete interval computation for depth 15, residue 4979. -/
theorem bounds_15_4979 : exactInterval 15 4979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4979 : oddCount 4979 15 = 5 ∧ acceleratedOrbit 15 4979 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4979) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4979.1, data_15_4979.2]

end Collatz.Research.PassageAtlas.Batch0152
