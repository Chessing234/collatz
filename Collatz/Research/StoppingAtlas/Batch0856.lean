import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0856

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5964. -/
theorem bounds_13_5964 : exactInterval 13 5964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5964 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5964) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5964 : oddCount 5964 13 = 7 ∧ acceleratedOrbit 13 5964 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5964 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5964) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5964.1, data_13_5964.2]

/-- Complete interval computation for depth 13, residue 5965. -/
theorem bounds_13_5965 : exactInterval 13 5965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5965 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5965) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5965 : oddCount 5965 13 = 7 ∧ acceleratedOrbit 13 5965 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5965 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5965) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5965.1, data_13_5965.2]

/-- Complete interval computation for depth 13, residue 5966. -/
theorem bounds_13_5966 : exactInterval 13 5966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5966 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5966) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5966 : oddCount 5966 13 = 8 ∧ acceleratedOrbit 13 5966 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5966 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5966) = 3 ^ 8 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5966.1, data_13_5966.2]

/-- Complete interval computation for depth 13, residue 5967. -/
theorem bounds_13_5967 : exactInterval 13 5967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5967 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5967) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5967 : oddCount 5967 13 = 8 ∧ acceleratedOrbit 13 5967 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5967 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5967) = 3 ^ 8 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5967.1, data_13_5967.2]

/-- Complete interval computation for depth 13, residue 5968. -/
theorem bounds_13_5968 : exactInterval 13 5968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5968 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5968) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5968 : oddCount 5968 13 = 3 ∧ acceleratedOrbit 13 5968 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5968 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5968) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5968.1, data_13_5968.2]

/-- Complete interval computation for depth 13, residue 5969. -/
theorem bounds_13_5969 : exactInterval 13 5969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5969 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5969) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5969 : oddCount 5969 13 = 7 ∧ acceleratedOrbit 13 5969 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5969 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5969) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5969.1, data_13_5969.2]

/-- Complete interval computation for depth 13, residue 5970. -/
theorem bounds_13_5970 : exactInterval 13 5970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5970 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5970) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5970 : oddCount 5970 13 = 8 ∧ acceleratedOrbit 13 5970 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5970 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5970) = 3 ^ 8 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5970.1, data_13_5970.2]

/-- Complete interval computation for depth 13, residue 5971. -/
theorem bounds_13_5971 : exactInterval 13 5971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5971 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5971) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5971 : oddCount 5971 13 = 8 ∧ acceleratedOrbit 13 5971 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5971 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5971) = 3 ^ 8 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5971.1, data_13_5971.2]

/-- Complete interval computation for depth 13, residue 5972. -/
theorem bounds_13_5972 : exactInterval 13 5972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5972 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5972) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5972 : oddCount 5972 13 = 3 ∧ acceleratedOrbit 13 5972 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5972 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5972) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5972.1, data_13_5972.2]

/-- Complete interval computation for depth 13, residue 5973. -/
theorem bounds_13_5973 : exactInterval 13 5973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5973 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5973) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5973 : oddCount 5973 13 = 3 ∧ acceleratedOrbit 13 5973 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5973 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5973) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5973.1, data_13_5973.2]

/-- Complete interval computation for depth 13, residue 5974. -/
theorem bounds_13_5974 : exactInterval 13 5974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5974 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5974) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5974 : oddCount 5974 13 = 6 ∧ acceleratedOrbit 13 5974 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5974 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5974) = 3 ^ 6 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5974.1, data_13_5974.2]

/-- Complete interval computation for depth 13, residue 5975. -/
theorem bounds_13_5975 : exactInterval 13 5975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5975 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5975) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5975 : oddCount 5975 13 = 6 ∧ acceleratedOrbit 13 5975 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5975 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5975) = 3 ^ 6 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5975.1, data_13_5975.2]

/-- Complete interval computation for depth 13, residue 5976. -/
theorem bounds_13_5976 : exactInterval 13 5976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5976 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5976) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5976 : oddCount 5976 13 = 6 ∧ acceleratedOrbit 13 5976 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5976 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5976) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5976.1, data_13_5976.2]

/-- Complete interval computation for depth 13, residue 5977. -/
theorem bounds_13_5977 : exactInterval 13 5977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5977 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5977) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5977 : oddCount 5977 13 = 6 ∧ acceleratedOrbit 13 5977 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5977 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5977) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5977.1, data_13_5977.2]

/-- Complete interval computation for depth 13, residue 5978. -/
theorem bounds_13_5978 : exactInterval 13 5978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5978 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5978) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5978 : oddCount 5978 13 = 6 ∧ acceleratedOrbit 13 5978 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5978 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5978) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5978.1, data_13_5978.2]

/-- Complete interval computation for depth 13, residue 5979. -/
theorem bounds_13_5979 : exactInterval 13 5979 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5979 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5979) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5979 : oddCount 5979 13 = 8 ∧ acceleratedOrbit 13 5979 = 4790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5979 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5979) = 3 ^ 8 * m + 4790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5979.1, data_13_5979.2]

end Collatz.Research.StoppingAtlas.Batch0856
