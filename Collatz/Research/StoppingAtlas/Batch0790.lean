import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0790

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4951. -/
theorem bounds_13_4951 : exactInterval 13 4951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4951 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4951) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4951 : oddCount 4951 13 = 9 ∧ acceleratedOrbit 13 4951 = 11906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4951 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4951) = 3 ^ 9 * m + 11906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4951.1, data_13_4951.2]

/-- Complete interval computation for depth 13, residue 4952. -/
theorem bounds_13_4952 : exactInterval 13 4952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4952 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4952) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4952 : oddCount 4952 13 = 6 ∧ acceleratedOrbit 13 4952 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4952 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4952) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4952.1, data_13_4952.2]

/-- Complete interval computation for depth 13, residue 4953. -/
theorem bounds_13_4953 : exactInterval 13 4953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4953 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4953) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4953 : oddCount 4953 13 = 4 ∧ acceleratedOrbit 13 4953 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4953 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4953) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4953.1, data_13_4953.2]

/-- Complete interval computation for depth 13, residue 4954. -/
theorem bounds_13_4954 : exactInterval 13 4954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4954 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4954) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4954 : oddCount 4954 13 = 6 ∧ acceleratedOrbit 13 4954 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4954 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4954) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4954.1, data_13_4954.2]

/-- Complete interval computation for depth 13, residue 4955. -/
theorem bounds_13_4955 : exactInterval 13 4955 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4955 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4955) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4955 : oddCount 4955 13 = 8 ∧ acceleratedOrbit 13 4955 = 3970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4955 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4955) = 3 ^ 8 * m + 3970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4955.1, data_13_4955.2]

/-- Complete interval computation for depth 13, residue 4956. -/
theorem bounds_13_4956 : exactInterval 13 4956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4956 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4956) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4956 : oddCount 4956 13 = 6 ∧ acceleratedOrbit 13 4956 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4956 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4956) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4956.1, data_13_4956.2]

/-- Complete interval computation for depth 13, residue 4957. -/
theorem bounds_13_4957 : exactInterval 13 4957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4957 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4957) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4957 : oddCount 4957 13 = 6 ∧ acceleratedOrbit 13 4957 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4957 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4957) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4957.1, data_13_4957.2]

/-- Complete interval computation for depth 13, residue 4958. -/
theorem bounds_13_4958 : exactInterval 13 4958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4958 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4958) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4958 : oddCount 4958 13 = 7 ∧ acceleratedOrbit 13 4958 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4958 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4958) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4958.1, data_13_4958.2]

/-- Complete interval computation for depth 13, residue 4959. -/
theorem bounds_13_4959 : exactInterval 13 4959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4959 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4959) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4959 : oddCount 4959 13 = 7 ∧ acceleratedOrbit 13 4959 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4959 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4959) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4959.1, data_13_4959.2]

/-- Complete interval computation for depth 13, residue 4960. -/
theorem bounds_13_4960 : exactInterval 13 4960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4960 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4960) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4960 : oddCount 4960 13 = 6 ∧ acceleratedOrbit 13 4960 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4960 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4960) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4960.1, data_13_4960.2]

/-- Complete interval computation for depth 13, residue 4961. -/
theorem bounds_13_4961 : exactInterval 13 4961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4961 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4961) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4961 : oddCount 4961 13 = 9 ∧ acceleratedOrbit 13 4961 = 11927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4961 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4961) = 3 ^ 9 * m + 11927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4961.1, data_13_4961.2]

/-- Complete interval computation for depth 13, residue 4962. -/
theorem bounds_13_4962 : exactInterval 13 4962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4962 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4962) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4962 : oddCount 4962 13 = 5 ∧ acceleratedOrbit 13 4962 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4962 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4962) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4962.1, data_13_4962.2]

/-- Complete interval computation for depth 13, residue 4963. -/
theorem bounds_13_4963 : exactInterval 13 4963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4963 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4963) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4963 : oddCount 4963 13 = 5 ∧ acceleratedOrbit 13 4963 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4963 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4963) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4963.1, data_13_4963.2]

/-- Complete interval computation for depth 13, residue 4964. -/
theorem bounds_13_4964 : exactInterval 13 4964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4964 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4964) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4964 : oddCount 4964 13 = 5 ∧ acceleratedOrbit 13 4964 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4964 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4964) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4964.1, data_13_4964.2]

/-- Complete interval computation for depth 13, residue 4965. -/
theorem bounds_13_4965 : exactInterval 13 4965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4965 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4965) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4965 : oddCount 4965 13 = 5 ∧ acceleratedOrbit 13 4965 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4965 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4965) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4965.1, data_13_4965.2]

end Collatz.Research.StoppingAtlas.Batch0790
