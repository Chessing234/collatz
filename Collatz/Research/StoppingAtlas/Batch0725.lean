import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0725

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3952. -/
theorem bounds_13_3952 : exactInterval 13 3952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3952 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3952) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3952 : oddCount 3952 13 = 5 ∧ acceleratedOrbit 13 3952 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3952 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3952) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3952.1, data_13_3952.2]

/-- Complete interval computation for depth 13, residue 3953. -/
theorem bounds_13_3953 : exactInterval 13 3953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3953 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3953) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3953 : oddCount 3953 13 = 5 ∧ acceleratedOrbit 13 3953 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3953 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3953) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3953.1, data_13_3953.2]

/-- Complete interval computation for depth 13, residue 3954. -/
theorem bounds_13_3954 : exactInterval 13 3954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3954 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3954) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3954 : oddCount 3954 13 = 6 ∧ acceleratedOrbit 13 3954 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3954 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3954) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3954.1, data_13_3954.2]

/-- Complete interval computation for depth 13, residue 3955. -/
theorem bounds_13_3955 : exactInterval 13 3955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3955 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3955) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3955 : oddCount 3955 13 = 6 ∧ acceleratedOrbit 13 3955 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3955 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3955) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3955.1, data_13_3955.2]

/-- Complete interval computation for depth 13, residue 3956. -/
theorem bounds_13_3956 : exactInterval 13 3956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3956 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3956) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3956 : oddCount 3956 13 = 5 ∧ acceleratedOrbit 13 3956 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3956 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3956) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3956.1, data_13_3956.2]

/-- Complete interval computation for depth 13, residue 3957. -/
theorem bounds_13_3957 : exactInterval 13 3957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3957 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3957) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3957 : oddCount 3957 13 = 5 ∧ acceleratedOrbit 13 3957 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3957 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3957) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3957.1, data_13_3957.2]

/-- Complete interval computation for depth 13, residue 3958. -/
theorem bounds_13_3958 : exactInterval 13 3958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3958 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3958) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3958 : oddCount 3958 13 = 6 ∧ acceleratedOrbit 13 3958 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3958 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3958) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3958.1, data_13_3958.2]

/-- Complete interval computation for depth 13, residue 3959. -/
theorem bounds_13_3959 : exactInterval 13 3959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3959 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3959) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3959 : oddCount 3959 13 = 6 ∧ acceleratedOrbit 13 3959 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3959 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3959) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3959.1, data_13_3959.2]

/-- Complete interval computation for depth 13, residue 3960. -/
theorem bounds_13_3960 : exactInterval 13 3960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3960 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3960) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3960 : oddCount 3960 13 = 8 ∧ acceleratedOrbit 13 3960 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3960 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3960) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3960.1, data_13_3960.2]

/-- Complete interval computation for depth 13, residue 3961. -/
theorem bounds_13_3961 : exactInterval 13 3961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3961 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3961) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3961 : oddCount 3961 13 = 7 ∧ acceleratedOrbit 13 3961 = 1058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3961 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3961) = 3 ^ 7 * m + 1058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3961.1, data_13_3961.2]

/-- Complete interval computation for depth 13, residue 3962. -/
theorem bounds_13_3962 : exactInterval 13 3962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3962 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3962) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3962 : oddCount 3962 13 = 8 ∧ acceleratedOrbit 13 3962 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3962 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3962) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3962.1, data_13_3962.2]

/-- Complete interval computation for depth 13, residue 3963. -/
theorem bounds_13_3963 : exactInterval 13 3963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3963 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3963) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3963 : oddCount 3963 13 = 8 ∧ acceleratedOrbit 13 3963 = 3176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3963 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3963) = 3 ^ 8 * m + 3176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3963.1, data_13_3963.2]

/-- Complete interval computation for depth 13, residue 3964. -/
theorem bounds_13_3964 : exactInterval 13 3964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3964 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3964) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3964 : oddCount 3964 13 = 8 ∧ acceleratedOrbit 13 3964 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3964 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3964) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3964.1, data_13_3964.2]

/-- Complete interval computation for depth 13, residue 3965. -/
theorem bounds_13_3965 : exactInterval 13 3965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3965 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3965) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3965 : oddCount 3965 13 = 8 ∧ acceleratedOrbit 13 3965 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3965 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3965) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3965.1, data_13_3965.2]

/-- Complete interval computation for depth 13, residue 3966. -/
theorem bounds_13_3966 : exactInterval 13 3966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3966 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3966) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3966 : oddCount 3966 13 = 8 ∧ acceleratedOrbit 13 3966 = 3178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3966 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3966) = 3 ^ 8 * m + 3178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3966.1, data_13_3966.2]

/-- Complete interval computation for depth 13, residue 3967. -/
theorem bounds_13_3967 : exactInterval 13 3967 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3967 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3967) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3967 : oddCount 3967 13 = 8 ∧ acceleratedOrbit 13 3967 = 3178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3967 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3967) = 3 ^ 8 * m + 3178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3967.1, data_13_3967.2]

end Collatz.Research.StoppingAtlas.Batch0725
