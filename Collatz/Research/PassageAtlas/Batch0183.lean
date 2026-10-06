import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0183

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5963. -/
theorem bounds_15_5963 : exactInterval 15 5963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5963 : oddCount 5963 15 = 6 ∧ acceleratedOrbit 15 5963 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5963) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5963.1, data_15_5963.2]

/-- Complete interval computation for depth 15, residue 5964. -/
theorem bounds_15_5964 : exactInterval 15 5964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5964 : oddCount 5964 15 = 9 ∧ acceleratedOrbit 15 5964 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5964) = 3 ^ 9 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5964.1, data_15_5964.2]

/-- Complete interval computation for depth 15, residue 5965. -/
theorem bounds_15_5965 : exactInterval 15 5965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5965 : oddCount 5965 15 = 9 ∧ acceleratedOrbit 15 5965 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5965) = 3 ^ 9 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5965.1, data_15_5965.2]

/-- Complete interval computation for depth 15, residue 5966. -/
theorem bounds_15_5966 : exactInterval 15 5966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5966 : oddCount 5966 15 = 9 ∧ acceleratedOrbit 15 5966 = 3586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5966) = 3 ^ 9 * m + 3586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5966.1, data_15_5966.2]

/-- Complete interval computation for depth 15, residue 5967. -/
theorem bounds_15_5967 : exactInterval 15 5967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5967 : oddCount 5967 15 = 9 ∧ acceleratedOrbit 15 5967 = 3586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5967) = 3 ^ 9 * m + 3586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5967.1, data_15_5967.2]

/-- Complete interval computation for depth 15, residue 5968. -/
theorem bounds_15_5968 : exactInterval 15 5968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5968 : oddCount 5968 15 = 3 ∧ acceleratedOrbit 15 5968 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5968) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5968.1, data_15_5968.2]

/-- Complete interval computation for depth 15, residue 5969. -/
theorem bounds_15_5969 : exactInterval 15 5969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5969 : oddCount 5969 15 = 9 ∧ acceleratedOrbit 15 5969 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5969) = 3 ^ 9 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5969.1, data_15_5969.2]

/-- Complete interval computation for depth 15, residue 5970. -/
theorem bounds_15_5970 : exactInterval 15 5970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5970 : oddCount 5970 15 = 8 ∧ acceleratedOrbit 15 5970 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5970) = 3 ^ 8 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5970.1, data_15_5970.2]

/-- Complete interval computation for depth 15, residue 5971. -/
theorem bounds_15_5971 : exactInterval 15 5971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5971 : oddCount 5971 15 = 8 ∧ acceleratedOrbit 15 5971 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5971) = 3 ^ 8 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5971.1, data_15_5971.2]

/-- Complete interval computation for depth 15, residue 5972. -/
theorem bounds_15_5972 : exactInterval 15 5972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5972 : oddCount 5972 15 = 3 ∧ acceleratedOrbit 15 5972 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5972) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5972.1, data_15_5972.2]

/-- Complete interval computation for depth 15, residue 5973. -/
theorem bounds_15_5973 : exactInterval 15 5973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5973 : oddCount 5973 15 = 3 ∧ acceleratedOrbit 15 5973 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5973) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5973.1, data_15_5973.2]

/-- Complete interval computation for depth 15, residue 5974. -/
theorem bounds_15_5974 : exactInterval 15 5974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5974 : oddCount 5974 15 = 6 ∧ acceleratedOrbit 15 5974 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5974) = 3 ^ 6 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5974.1, data_15_5974.2]

/-- Complete interval computation for depth 15, residue 5975. -/
theorem bounds_15_5975 : exactInterval 15 5975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5975 : oddCount 5975 15 = 6 ∧ acceleratedOrbit 15 5975 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5975) = 3 ^ 6 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5975.1, data_15_5975.2]

/-- Complete interval computation for depth 15, residue 5976. -/
theorem bounds_15_5976 : exactInterval 15 5976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5976 : oddCount 5976 15 = 7 ∧ acceleratedOrbit 15 5976 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5976) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5976.1, data_15_5976.2]

/-- Complete interval computation for depth 15, residue 5977. -/
theorem bounds_15_5977 : exactInterval 15 5977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5977 : oddCount 5977 15 = 7 ∧ acceleratedOrbit 15 5977 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5977) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5977.1, data_15_5977.2]

/-- Complete interval computation for depth 15, residue 5978. -/
theorem bounds_15_5978 : exactInterval 15 5978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5978 : oddCount 5978 15 = 7 ∧ acceleratedOrbit 15 5978 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5978) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5978.1, data_15_5978.2]

/-- Complete interval computation for depth 15, residue 5979. -/
theorem bounds_15_5979 : exactInterval 15 5979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5979 : oddCount 5979 15 = 9 ∧ acceleratedOrbit 15 5979 = 3593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5979) = 3 ^ 9 * m + 3593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5979.1, data_15_5979.2]

/-- Complete interval computation for depth 15, residue 5980. -/
theorem bounds_15_5980 : exactInterval 15 5980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5980 : oddCount 5980 15 = 7 ∧ acceleratedOrbit 15 5980 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5980) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5980.1, data_15_5980.2]

/-- Complete interval computation for depth 15, residue 5981. -/
theorem bounds_15_5981 : exactInterval 15 5981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5981 : oddCount 5981 15 = 7 ∧ acceleratedOrbit 15 5981 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5981) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5981.1, data_15_5981.2]

/-- Complete interval computation for depth 15, residue 5982. -/
theorem bounds_15_5982 : exactInterval 15 5982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5982 : oddCount 5982 15 = 7 ∧ acceleratedOrbit 15 5982 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5982) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5982.1, data_15_5982.2]

/-- Complete interval computation for depth 15, residue 5983. -/
theorem bounds_15_5983 : exactInterval 15 5983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5983 : oddCount 5983 15 = 7 ∧ acceleratedOrbit 15 5983 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5983) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5983.1, data_15_5983.2]

/-- Complete interval computation for depth 15, residue 5984. -/
theorem bounds_15_5984 : exactInterval 15 5984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5984 : oddCount 5984 15 = 7 ∧ acceleratedOrbit 15 5984 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5984) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5984.1, data_15_5984.2]

/-- Complete interval computation for depth 15, residue 5985. -/
theorem bounds_15_5985 : exactInterval 15 5985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5985 : oddCount 5985 15 = 8 ∧ acceleratedOrbit 15 5985 = 1199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5985) = 3 ^ 8 * m + 1199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5985.1, data_15_5985.2]

/-- Complete interval computation for depth 15, residue 5986. -/
theorem bounds_15_5986 : exactInterval 15 5986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5986 : oddCount 5986 15 = 7 ∧ acceleratedOrbit 15 5986 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5986) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5986.1, data_15_5986.2]

/-- Complete interval computation for depth 15, residue 5987. -/
theorem bounds_15_5987 : exactInterval 15 5987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5987 : oddCount 5987 15 = 7 ∧ acceleratedOrbit 15 5987 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5987) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5987.1, data_15_5987.2]

/-- Complete interval computation for depth 15, residue 5988. -/
theorem bounds_15_5988 : exactInterval 15 5988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5988 : oddCount 5988 15 = 7 ∧ acceleratedOrbit 15 5988 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5988) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5988.1, data_15_5988.2]

/-- Complete interval computation for depth 15, residue 5989. -/
theorem bounds_15_5989 : exactInterval 15 5989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5989 : oddCount 5989 15 = 7 ∧ acceleratedOrbit 15 5989 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5989) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5989.1, data_15_5989.2]

/-- Complete interval computation for depth 15, residue 5990. -/
theorem bounds_15_5990 : exactInterval 15 5990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5990 : oddCount 5990 15 = 7 ∧ acceleratedOrbit 15 5990 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5990) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5990.1, data_15_5990.2]

/-- Complete interval computation for depth 15, residue 5991. -/
theorem bounds_15_5991 : exactInterval 15 5991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5991 : oddCount 5991 15 = 11 ∧ acceleratedOrbit 15 5991 = 32395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5991) = 3 ^ 11 * m + 32395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5991.1, data_15_5991.2]

/-- Complete interval computation for depth 15, residue 5992. -/
theorem bounds_15_5992 : exactInterval 15 5992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5992 : oddCount 5992 15 = 7 ∧ acceleratedOrbit 15 5992 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5992) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5992.1, data_15_5992.2]

/-- Complete interval computation for depth 15, residue 5993. -/
theorem bounds_15_5993 : exactInterval 15 5993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5993 : oddCount 5993 15 = 8 ∧ acceleratedOrbit 15 5993 = 1201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5993) = 3 ^ 8 * m + 1201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5993.1, data_15_5993.2]

/-- Complete interval computation for depth 15, residue 5994. -/
theorem bounds_15_5994 : exactInterval 15 5994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5994 : oddCount 5994 15 = 7 ∧ acceleratedOrbit 15 5994 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5994) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5994.1, data_15_5994.2]

/-- Complete interval computation for depth 15, residue 5995. -/
theorem bounds_15_5995 : exactInterval 15 5995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5995 : oddCount 5995 15 = 9 ∧ acceleratedOrbit 15 5995 = 3604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5995) = 3 ^ 9 * m + 3604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5995.1, data_15_5995.2]

end Collatz.Research.PassageAtlas.Batch0183
