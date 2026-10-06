import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0122

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3964. -/
theorem bounds_15_3964 : exactInterval 15 3964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3964 : oddCount 3964 15 = 10 ∧ acceleratedOrbit 15 3964 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3964) = 3 ^ 10 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3964.1, data_15_3964.2]

/-- Complete interval computation for depth 15, residue 3965. -/
theorem bounds_15_3965 : exactInterval 15 3965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3965 : oddCount 3965 15 = 10 ∧ acceleratedOrbit 15 3965 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3965) = 3 ^ 10 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3965.1, data_15_3965.2]

/-- Complete interval computation for depth 15, residue 3966. -/
theorem bounds_15_3966 : exactInterval 15 3966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3966 : oddCount 3966 15 = 9 ∧ acceleratedOrbit 15 3966 = 2384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3966) = 3 ^ 9 * m + 2384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3966.1, data_15_3966.2]

/-- Complete interval computation for depth 15, residue 3967. -/
theorem bounds_15_3967 : exactInterval 15 3967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3967 : oddCount 3967 15 = 9 ∧ acceleratedOrbit 15 3967 = 2384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3967) = 3 ^ 9 * m + 2384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3967.1, data_15_3967.2]

/-- Complete interval computation for depth 15, residue 3968. -/
theorem bounds_15_3968 : exactInterval 15 3968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3968 : oddCount 3968 15 = 6 ∧ acceleratedOrbit 15 3968 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3968) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3968.1, data_15_3968.2]

/-- Complete interval computation for depth 15, residue 3969. -/
theorem bounds_15_3969 : exactInterval 15 3969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3969 : oddCount 3969 15 = 8 ∧ acceleratedOrbit 15 3969 = 796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3969) = 3 ^ 8 * m + 796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3969.1, data_15_3969.2]

/-- Complete interval computation for depth 15, residue 3970. -/
theorem bounds_15_3970 : exactInterval 15 3970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3970 : oddCount 3970 15 = 6 ∧ acceleratedOrbit 15 3970 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3970) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3970.1, data_15_3970.2]

/-- Complete interval computation for depth 15, residue 3971. -/
theorem bounds_15_3971 : exactInterval 15 3971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3971 : oddCount 3971 15 = 6 ∧ acceleratedOrbit 15 3971 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3971) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3971.1, data_15_3971.2]

/-- Complete interval computation for depth 15, residue 3972. -/
theorem bounds_15_3972 : exactInterval 15 3972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3972 : oddCount 3972 15 = 9 ∧ acceleratedOrbit 15 3972 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3972) = 3 ^ 9 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3972.1, data_15_3972.2]

/-- Complete interval computation for depth 15, residue 3973. -/
theorem bounds_15_3973 : exactInterval 15 3973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3973 : oddCount 3973 15 = 9 ∧ acceleratedOrbit 15 3973 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3973) = 3 ^ 9 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3973.1, data_15_3973.2]

/-- Complete interval computation for depth 15, residue 3974. -/
theorem bounds_15_3974 : exactInterval 15 3974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3974 : oddCount 3974 15 = 9 ∧ acceleratedOrbit 15 3974 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3974) = 3 ^ 9 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3974.1, data_15_3974.2]

/-- Complete interval computation for depth 15, residue 3975. -/
theorem bounds_15_3975 : exactInterval 15 3975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3975 : oddCount 3975 15 = 6 ∧ acceleratedOrbit 15 3975 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3975) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3975.1, data_15_3975.2]

/-- Complete interval computation for depth 15, residue 3976. -/
theorem bounds_15_3976 : exactInterval 15 3976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3976 : oddCount 3976 15 = 4 ∧ acceleratedOrbit 15 3976 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3976) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3976.1, data_15_3976.2]

/-- Complete interval computation for depth 15, residue 3977. -/
theorem bounds_15_3977 : exactInterval 15 3977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3977 : oddCount 3977 15 = 10 ∧ acceleratedOrbit 15 3977 = 7172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3977) = 3 ^ 10 * m + 7172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3977.1, data_15_3977.2]

/-- Complete interval computation for depth 15, residue 3978. -/
theorem bounds_15_3978 : exactInterval 15 3978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3978 : oddCount 3978 15 = 4 ∧ acceleratedOrbit 15 3978 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3978) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3978.1, data_15_3978.2]

/-- Complete interval computation for depth 15, residue 3979. -/
theorem bounds_15_3979 : exactInterval 15 3979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3979 : oddCount 3979 15 = 9 ∧ acceleratedOrbit 15 3979 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3979) = 3 ^ 9 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3979.1, data_15_3979.2]

/-- Complete interval computation for depth 15, residue 3980. -/
theorem bounds_15_3980 : exactInterval 15 3980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3980 : oddCount 3980 15 = 4 ∧ acceleratedOrbit 15 3980 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3980) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3980.1, data_15_3980.2]

/-- Complete interval computation for depth 15, residue 3981. -/
theorem bounds_15_3981 : exactInterval 15 3981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3981 : oddCount 3981 15 = 4 ∧ acceleratedOrbit 15 3981 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3981) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3981.1, data_15_3981.2]

/-- Complete interval computation for depth 15, residue 3982. -/
theorem bounds_15_3982 : exactInterval 15 3982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3982 : oddCount 3982 15 = 7 ∧ acceleratedOrbit 15 3982 = 266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3982) = 3 ^ 7 * m + 266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3982.1, data_15_3982.2]

/-- Complete interval computation for depth 15, residue 3983. -/
theorem bounds_15_3983 : exactInterval 15 3983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3983 : oddCount 3983 15 = 7 ∧ acceleratedOrbit 15 3983 = 266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3983) = 3 ^ 7 * m + 266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3983.1, data_15_3983.2]

/-- Complete interval computation for depth 15, residue 3984. -/
theorem bounds_15_3984 : exactInterval 15 3984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3984 : oddCount 3984 15 = 7 ∧ acceleratedOrbit 15 3984 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3984) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3984.1, data_15_3984.2]

/-- Complete interval computation for depth 15, residue 3985. -/
theorem bounds_15_3985 : exactInterval 15 3985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3985 : oddCount 3985 15 = 8 ∧ acceleratedOrbit 15 3985 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3985) = 3 ^ 8 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3985.1, data_15_3985.2]

/-- Complete interval computation for depth 15, residue 3986. -/
theorem bounds_15_3986 : exactInterval 15 3986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3986 : oddCount 3986 15 = 8 ∧ acceleratedOrbit 15 3986 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3986) = 3 ^ 8 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3986.1, data_15_3986.2]

/-- Complete interval computation for depth 15, residue 3987. -/
theorem bounds_15_3987 : exactInterval 15 3987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3987 : oddCount 3987 15 = 8 ∧ acceleratedOrbit 15 3987 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3987) = 3 ^ 8 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3987.1, data_15_3987.2]

/-- Complete interval computation for depth 15, residue 3988. -/
theorem bounds_15_3988 : exactInterval 15 3988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3988 : oddCount 3988 15 = 7 ∧ acceleratedOrbit 15 3988 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3988) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3988.1, data_15_3988.2]

/-- Complete interval computation for depth 15, residue 3989. -/
theorem bounds_15_3989 : exactInterval 15 3989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3989 : oddCount 3989 15 = 7 ∧ acceleratedOrbit 15 3989 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3989) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3989.1, data_15_3989.2]

/-- Complete interval computation for depth 15, residue 3990. -/
theorem bounds_15_3990 : exactInterval 15 3990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3990 : oddCount 3990 15 = 7 ∧ acceleratedOrbit 15 3990 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3990) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3990.1, data_15_3990.2]

/-- Complete interval computation for depth 15, residue 3991. -/
theorem bounds_15_3991 : exactInterval 15 3991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3991 : oddCount 3991 15 = 7 ∧ acceleratedOrbit 15 3991 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3991) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3991.1, data_15_3991.2]

/-- Complete interval computation for depth 15, residue 3992. -/
theorem bounds_15_3992 : exactInterval 15 3992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3992 : oddCount 3992 15 = 7 ∧ acceleratedOrbit 15 3992 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3992) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3992.1, data_15_3992.2]

/-- Complete interval computation for depth 15, residue 3993. -/
theorem bounds_15_3993 : exactInterval 15 3993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3993 : oddCount 3993 15 = 7 ∧ acceleratedOrbit 15 3993 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3993) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3993.1, data_15_3993.2]

/-- Complete interval computation for depth 15, residue 3994. -/
theorem bounds_15_3994 : exactInterval 15 3994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3994 : oddCount 3994 15 = 7 ∧ acceleratedOrbit 15 3994 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3994) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3994.1, data_15_3994.2]

/-- Complete interval computation for depth 15, residue 3995. -/
theorem bounds_15_3995 : exactInterval 15 3995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3995 : oddCount 3995 15 = 9 ∧ acceleratedOrbit 15 3995 = 2402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3995) = 3 ^ 9 * m + 2402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3995.1, data_15_3995.2]

/-- Complete interval computation for depth 15, residue 3996. -/
theorem bounds_15_3996 : exactInterval 15 3996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3996 : oddCount 3996 15 = 6 ∧ acceleratedOrbit 15 3996 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3996) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3996.1, data_15_3996.2]

end Collatz.Research.PassageAtlas.Batch0122
