import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0726

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3968. -/
theorem bounds_13_3968 : exactInterval 13 3968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3968 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3968) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3968 : oddCount 3968 13 = 5 ∧ acceleratedOrbit 13 3968 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3968 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3968) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3968.1, data_13_3968.2]

/-- Complete interval computation for depth 13, residue 3969. -/
theorem bounds_13_3969 : exactInterval 13 3969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3969 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3969) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3969 : oddCount 3969 13 = 7 ∧ acceleratedOrbit 13 3969 = 1061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3969 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3969) = 3 ^ 7 * m + 1061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3969.1, data_13_3969.2]

/-- Complete interval computation for depth 13, residue 3970. -/
theorem bounds_13_3970 : exactInterval 13 3970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3970 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3970) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3970 : oddCount 3970 13 = 5 ∧ acceleratedOrbit 13 3970 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3970 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3970) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3970.1, data_13_3970.2]

/-- Complete interval computation for depth 13, residue 3971. -/
theorem bounds_13_3971 : exactInterval 13 3971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3971 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3971) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3971 : oddCount 3971 13 = 5 ∧ acceleratedOrbit 13 3971 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3971 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3971) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3971.1, data_13_3971.2]

/-- Complete interval computation for depth 13, residue 3972. -/
theorem bounds_13_3972 : exactInterval 13 3972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3972 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3972) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3972 : oddCount 3972 13 = 7 ∧ acceleratedOrbit 13 3972 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3972 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3972) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3972.1, data_13_3972.2]

/-- Complete interval computation for depth 13, residue 3973. -/
theorem bounds_13_3973 : exactInterval 13 3973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3973 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3973) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3973 : oddCount 3973 13 = 7 ∧ acceleratedOrbit 13 3973 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3973 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3973) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3973.1, data_13_3973.2]

/-- Complete interval computation for depth 13, residue 3974. -/
theorem bounds_13_3974 : exactInterval 13 3974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3974 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3974) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3974 : oddCount 3974 13 = 7 ∧ acceleratedOrbit 13 3974 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3974 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3974) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3974.1, data_13_3974.2]

/-- Complete interval computation for depth 13, residue 3975. -/
theorem bounds_13_3975 : exactInterval 13 3975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3975 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3975) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3975 : oddCount 3975 13 = 5 ∧ acceleratedOrbit 13 3975 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3975 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3975) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3975.1, data_13_3975.2]

/-- Complete interval computation for depth 13, residue 3976. -/
theorem bounds_13_3976 : exactInterval 13 3976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3976 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3976) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3976 : oddCount 3976 13 = 4 ∧ acceleratedOrbit 13 3976 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3976 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3976) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3976.1, data_13_3976.2]

/-- Complete interval computation for depth 13, residue 3977. -/
theorem bounds_13_3977 : exactInterval 13 3977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3977 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3977) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3977 : oddCount 3977 13 = 8 ∧ acceleratedOrbit 13 3977 = 3187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3977 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3977) = 3 ^ 8 * m + 3187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3977.1, data_13_3977.2]

/-- Complete interval computation for depth 13, residue 3978. -/
theorem bounds_13_3978 : exactInterval 13 3978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3978 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3978) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3978 : oddCount 3978 13 = 4 ∧ acceleratedOrbit 13 3978 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3978 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3978) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3978.1, data_13_3978.2]

/-- Complete interval computation for depth 13, residue 3979. -/
theorem bounds_13_3979 : exactInterval 13 3979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3979 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3979) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3979 : oddCount 3979 13 = 7 ∧ acceleratedOrbit 13 3979 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3979 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3979) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3979.1, data_13_3979.2]

/-- Complete interval computation for depth 13, residue 3980. -/
theorem bounds_13_3980 : exactInterval 13 3980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3980 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3980) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3980 : oddCount 3980 13 = 4 ∧ acceleratedOrbit 13 3980 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3980 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3980) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3980.1, data_13_3980.2]

/-- Complete interval computation for depth 13, residue 3981. -/
theorem bounds_13_3981 : exactInterval 13 3981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3981 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3981) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3981 : oddCount 3981 13 = 4 ∧ acceleratedOrbit 13 3981 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3981 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3981) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3981.1, data_13_3981.2]

/-- Complete interval computation for depth 13, residue 3982. -/
theorem bounds_13_3982 : exactInterval 13 3982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3982 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3982) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3982 : oddCount 3982 13 = 7 ∧ acceleratedOrbit 13 3982 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3982 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3982) = 3 ^ 7 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3982.1, data_13_3982.2]

end Collatz.Research.StoppingAtlas.Batch0726
