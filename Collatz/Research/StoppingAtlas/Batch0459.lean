import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0459

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3962. -/
theorem bounds_12_3962 : exactInterval 12 3962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3962 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3962) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3962 : oddCount 3962 12 = 7 ∧ acceleratedOrbit 12 3962 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3962 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3962) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3962.1, data_12_3962.2]

/-- Complete interval computation for depth 12, residue 3963. -/
theorem bounds_12_3963 : exactInterval 12 3963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3963 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3963) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3963 : oddCount 3963 12 = 7 ∧ acceleratedOrbit 12 3963 = 2117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3963 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3963) = 3 ^ 7 * m + 2117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3963.1, data_12_3963.2]

/-- Complete interval computation for depth 12, residue 3964. -/
theorem bounds_12_3964 : exactInterval 12 3964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3964 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3964) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3964 : oddCount 3964 12 = 7 ∧ acceleratedOrbit 12 3964 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3964 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3964) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3964.1, data_12_3964.2]

/-- Complete interval computation for depth 12, residue 3965. -/
theorem bounds_12_3965 : exactInterval 12 3965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3965 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3965) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3965 : oddCount 3965 12 = 7 ∧ acceleratedOrbit 12 3965 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3965 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3965) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3965.1, data_12_3965.2]

/-- Complete interval computation for depth 12, residue 3966. -/
theorem bounds_12_3966 : exactInterval 12 3966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3966 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3966) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3966 : oddCount 3966 12 = 8 ∧ acceleratedOrbit 12 3966 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3966 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3966) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3966.1, data_12_3966.2]

/-- Complete interval computation for depth 12, residue 3967. -/
theorem bounds_12_3967 : exactInterval 12 3967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3967 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3967) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3967 : oddCount 3967 12 = 8 ∧ acceleratedOrbit 12 3967 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3967 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3967) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3967.1, data_12_3967.2]

/-- Complete interval computation for depth 12, residue 3968. -/
theorem bounds_12_3968 : exactInterval 12 3968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3968 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3968) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3968 : oddCount 3968 12 = 5 ∧ acceleratedOrbit 12 3968 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3968 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3968) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3968.1, data_12_3968.2]

/-- Complete interval computation for depth 12, residue 3969. -/
theorem bounds_12_3969 : exactInterval 12 3969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3969 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3969) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3969 : oddCount 3969 12 = 6 ∧ acceleratedOrbit 12 3969 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3969 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3969) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3969.1, data_12_3969.2]

/-- Complete interval computation for depth 12, residue 3970. -/
theorem bounds_12_3970 : exactInterval 12 3970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3970 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3970) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3970 : oddCount 3970 12 = 5 ∧ acceleratedOrbit 12 3970 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3970 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3970) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3970.1, data_12_3970.2]

/-- Complete interval computation for depth 12, residue 3971. -/
theorem bounds_12_3971 : exactInterval 12 3971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3971 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3971) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3971 : oddCount 3971 12 = 5 ∧ acceleratedOrbit 12 3971 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3971 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3971) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3971.1, data_12_3971.2]

/-- Complete interval computation for depth 12, residue 3972. -/
theorem bounds_12_3972 : exactInterval 12 3972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3972 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3972) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3972 : oddCount 3972 12 = 7 ∧ acceleratedOrbit 12 3972 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3972 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3972) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3972.1, data_12_3972.2]

/-- Complete interval computation for depth 12, residue 3973. -/
theorem bounds_12_3973 : exactInterval 12 3973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3973 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3973) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3973 : oddCount 3973 12 = 7 ∧ acceleratedOrbit 12 3973 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3973 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3973) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3973.1, data_12_3973.2]

/-- Complete interval computation for depth 12, residue 3974. -/
theorem bounds_12_3974 : exactInterval 12 3974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3974 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3974) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3974 : oddCount 3974 12 = 7 ∧ acceleratedOrbit 12 3974 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3974 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3974) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3974.1, data_12_3974.2]

/-- Complete interval computation for depth 12, residue 3975. -/
theorem bounds_12_3975 : exactInterval 12 3975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3975 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3975) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3975 : oddCount 3975 12 = 5 ∧ acceleratedOrbit 12 3975 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3975 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3975) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3975.1, data_12_3975.2]

/-- Complete interval computation for depth 12, residue 3976. -/
theorem bounds_12_3976 : exactInterval 12 3976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3976 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3976) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3976 : oddCount 3976 12 = 4 ∧ acceleratedOrbit 12 3976 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3976 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3976) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3976.1, data_12_3976.2]

/-- Complete interval computation for depth 12, residue 3977. -/
theorem bounds_12_3977 : exactInterval 12 3977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3977 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3977) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3977 : oddCount 3977 12 = 8 ∧ acceleratedOrbit 12 3977 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3977 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3977) = 3 ^ 8 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3977.1, data_12_3977.2]

end Collatz.Research.StoppingAtlas.Batch0459
