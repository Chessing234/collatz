import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0986

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7961. -/
theorem bounds_13_7961 : exactInterval 13 7961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7961 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7961) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7961 : oddCount 7961 13 = 9 ∧ acceleratedOrbit 13 7961 = 19136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7961 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7961) = 3 ^ 9 * m + 19136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7961.1, data_13_7961.2]

/-- Complete interval computation for depth 13, residue 7962. -/
theorem bounds_13_7962 : exactInterval 13 7962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7962 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7962) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7962 : oddCount 7962 13 = 4 ∧ acceleratedOrbit 13 7962 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7962 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7962) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7962.1, data_13_7962.2]

/-- Complete interval computation for depth 13, residue 7963. -/
theorem bounds_13_7963 : exactInterval 13 7963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7963 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7963) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7963 : oddCount 7963 13 = 11 ∧ acceleratedOrbit 13 7963 = 172226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7963 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7963) = 3 ^ 11 * m + 172226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7963.1, data_13_7963.2]

/-- Complete interval computation for depth 13, residue 7964. -/
theorem bounds_13_7964 : exactInterval 13 7964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7964 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7964) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7964 : oddCount 7964 13 = 7 ∧ acceleratedOrbit 13 7964 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7964 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7964) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7964.1, data_13_7964.2]

/-- Complete interval computation for depth 13, residue 7965. -/
theorem bounds_13_7965 : exactInterval 13 7965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7965 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7965) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7965 : oddCount 7965 13 = 7 ∧ acceleratedOrbit 13 7965 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7965 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7965) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7965.1, data_13_7965.2]

/-- Complete interval computation for depth 13, residue 7966. -/
theorem bounds_13_7966 : exactInterval 13 7966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7966 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7966) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7966 : oddCount 7966 13 = 7 ∧ acceleratedOrbit 13 7966 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7966 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7966) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7966.1, data_13_7966.2]

/-- Complete interval computation for depth 13, residue 7967. -/
theorem bounds_13_7967 : exactInterval 13 7967 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7967 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7967) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7967 : oddCount 7967 13 = 8 ∧ acceleratedOrbit 13 7967 = 6382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7967 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7967) = 3 ^ 8 * m + 6382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7967.1, data_13_7967.2]

/-- Complete interval computation for depth 13, residue 7968. -/
theorem bounds_13_7968 : exactInterval 13 7968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7968 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7968) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7968 : oddCount 7968 13 = 5 ∧ acceleratedOrbit 13 7968 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7968 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7968) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7968.1, data_13_7968.2]

/-- Complete interval computation for depth 13, residue 7969. -/
theorem bounds_13_7969 : exactInterval 13 7969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7969 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7969) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7969 : oddCount 7969 13 = 6 ∧ acceleratedOrbit 13 7969 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7969 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7969) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7969.1, data_13_7969.2]

/-- Complete interval computation for depth 13, residue 7970. -/
theorem bounds_13_7970 : exactInterval 13 7970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7970 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7970) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7970 : oddCount 7970 13 = 7 ∧ acceleratedOrbit 13 7970 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7970 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7970) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7970.1, data_13_7970.2]

/-- Complete interval computation for depth 13, residue 7971. -/
theorem bounds_13_7971 : exactInterval 13 7971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7971 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7971) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7971 : oddCount 7971 13 = 7 ∧ acceleratedOrbit 13 7971 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7971 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7971) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7971.1, data_13_7971.2]

/-- Complete interval computation for depth 13, residue 7972. -/
theorem bounds_13_7972 : exactInterval 13 7972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7972 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7972) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7972 : oddCount 7972 13 = 7 ∧ acceleratedOrbit 13 7972 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7972 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7972) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7972.1, data_13_7972.2]

/-- Complete interval computation for depth 13, residue 7973. -/
theorem bounds_13_7973 : exactInterval 13 7973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7973 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7973) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7973 : oddCount 7973 13 = 7 ∧ acceleratedOrbit 13 7973 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7973 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7973) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7973.1, data_13_7973.2]

/-- Complete interval computation for depth 13, residue 7974. -/
theorem bounds_13_7974 : exactInterval 13 7974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7974 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7974) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7974 : oddCount 7974 13 = 7 ∧ acceleratedOrbit 13 7974 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7974 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7974) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7974.1, data_13_7974.2]

/-- Complete interval computation for depth 13, residue 7975. -/
theorem bounds_13_7975 : exactInterval 13 7975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7975 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7975) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7975 : oddCount 7975 13 = 8 ∧ acceleratedOrbit 13 7975 = 6389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7975 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7975) = 3 ^ 8 * m + 6389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7975.1, data_13_7975.2]

end Collatz.Research.StoppingAtlas.Batch0986
