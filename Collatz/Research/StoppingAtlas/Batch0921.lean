import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0921

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6963. -/
theorem bounds_13_6963 : exactInterval 13 6963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6963 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6963) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6963 : oddCount 6963 13 = 7 ∧ acceleratedOrbit 13 6963 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6963 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6963) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6963.1, data_13_6963.2]

/-- Complete interval computation for depth 13, residue 6964. -/
theorem bounds_13_6964 : exactInterval 13 6964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6964 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6964) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6964 : oddCount 6964 13 = 3 ∧ acceleratedOrbit 13 6964 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6964 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6964) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6964.1, data_13_6964.2]

/-- Complete interval computation for depth 13, residue 6965. -/
theorem bounds_13_6965 : exactInterval 13 6965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6965 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6965) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6965 : oddCount 6965 13 = 3 ∧ acceleratedOrbit 13 6965 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6965 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6965) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6965.1, data_13_6965.2]

/-- Complete interval computation for depth 13, residue 6966. -/
theorem bounds_13_6966 : exactInterval 13 6966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6966 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6966) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6966 : oddCount 6966 13 = 8 ∧ acceleratedOrbit 13 6966 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6966 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6966) = 3 ^ 8 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6966.1, data_13_6966.2]

/-- Complete interval computation for depth 13, residue 6967. -/
theorem bounds_13_6967 : exactInterval 13 6967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6967 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6967) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6967 : oddCount 6967 13 = 8 ∧ acceleratedOrbit 13 6967 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6967 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6967) = 3 ^ 8 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6967.1, data_13_6967.2]

/-- Complete interval computation for depth 13, residue 6968. -/
theorem bounds_13_6968 : exactInterval 13 6968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6968 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6968) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6968 : oddCount 6968 13 = 9 ∧ acceleratedOrbit 13 6968 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6968 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6968) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6968.1, data_13_6968.2]

/-- Complete interval computation for depth 13, residue 6969. -/
theorem bounds_13_6969 : exactInterval 13 6969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6969 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6969) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6969 : oddCount 6969 13 = 8 ∧ acceleratedOrbit 13 6969 = 5584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6969 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6969) = 3 ^ 8 * m + 5584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6969.1, data_13_6969.2]

/-- Complete interval computation for depth 13, residue 6970. -/
theorem bounds_13_6970 : exactInterval 13 6970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6970 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6970) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6970 : oddCount 6970 13 = 9 ∧ acceleratedOrbit 13 6970 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6970 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6970) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6970.1, data_13_6970.2]

/-- Complete interval computation for depth 13, residue 6971. -/
theorem bounds_13_6971 : exactInterval 13 6971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6971 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6971) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6971 : oddCount 6971 13 = 8 ∧ acceleratedOrbit 13 6971 = 5588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6971 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6971) = 3 ^ 8 * m + 5588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6971.1, data_13_6971.2]

/-- Complete interval computation for depth 13, residue 6972. -/
theorem bounds_13_6972 : exactInterval 13 6972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6972 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6972) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6972 : oddCount 6972 13 = 9 ∧ acceleratedOrbit 13 6972 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6972 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6972) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6972.1, data_13_6972.2]

/-- Complete interval computation for depth 13, residue 6973. -/
theorem bounds_13_6973 : exactInterval 13 6973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6973 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6973) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6973 : oddCount 6973 13 = 9 ∧ acceleratedOrbit 13 6973 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6973 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6973) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6973.1, data_13_6973.2]

/-- Complete interval computation for depth 13, residue 6974. -/
theorem bounds_13_6974 : exactInterval 13 6974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6974 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6974) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6974 : oddCount 6974 13 = 9 ∧ acceleratedOrbit 13 6974 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6974 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6974) = 3 ^ 9 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6974.1, data_13_6974.2]

/-- Complete interval computation for depth 13, residue 6975. -/
theorem bounds_13_6975 : exactInterval 13 6975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6975 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6975) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6975 : oddCount 6975 13 = 9 ∧ acceleratedOrbit 13 6975 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6975 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6975) = 3 ^ 9 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6975.1, data_13_6975.2]

/-- Complete interval computation for depth 13, residue 6976. -/
theorem bounds_13_6976 : exactInterval 13 6976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6976 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6976) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6976 : oddCount 6976 13 = 4 ∧ acceleratedOrbit 13 6976 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6976 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6976) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6976.1, data_13_6976.2]

/-- Complete interval computation for depth 13, residue 6977. -/
theorem bounds_13_6977 : exactInterval 13 6977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6977 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6977) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6977 : oddCount 6977 13 = 3 ∧ acceleratedOrbit 13 6977 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6977 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6977) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6977.1, data_13_6977.2]

end Collatz.Research.StoppingAtlas.Batch0921
