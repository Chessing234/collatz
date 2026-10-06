import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0885

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28966. -/
theorem bounds_15_28966 : exactInterval 15 28966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28966 : oddCount 28966 15 = 9 ∧ acceleratedOrbit 15 28966 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28966) = 3 ^ 9 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28966.1, data_15_28966.2]

/-- Complete interval computation for depth 15, residue 28967. -/
theorem bounds_15_28967 : exactInterval 15 28967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28967 : oddCount 28967 15 = 10 ∧ acceleratedOrbit 15 28967 = 52204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28967) = 3 ^ 10 * m + 52204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28967.1, data_15_28967.2]

/-- Complete interval computation for depth 15, residue 28968. -/
theorem bounds_15_28968 : exactInterval 15 28968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28968 : oddCount 28968 15 = 7 ∧ acceleratedOrbit 15 28968 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28968) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28968.1, data_15_28968.2]

/-- Complete interval computation for depth 15, residue 28969. -/
theorem bounds_15_28969 : exactInterval 15 28969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28969 : oddCount 28969 15 = 10 ∧ acceleratedOrbit 15 28969 = 52208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28969) = 3 ^ 10 * m + 52208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28969.1, data_15_28969.2]

/-- Complete interval computation for depth 15, residue 28970. -/
theorem bounds_15_28970 : exactInterval 15 28970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28970 : oddCount 28970 15 = 7 ∧ acceleratedOrbit 15 28970 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28970) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28970.1, data_15_28970.2]

/-- Complete interval computation for depth 15, residue 28971. -/
theorem bounds_15_28971 : exactInterval 15 28971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28971 : oddCount 28971 15 = 9 ∧ acceleratedOrbit 15 28971 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28971) = 3 ^ 9 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28971.1, data_15_28971.2]

/-- Complete interval computation for depth 15, residue 28972. -/
theorem bounds_15_28972 : exactInterval 15 28972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28972 : oddCount 28972 15 = 6 ∧ acceleratedOrbit 15 28972 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28972) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28972.1, data_15_28972.2]

/-- Complete interval computation for depth 15, residue 28973. -/
theorem bounds_15_28973 : exactInterval 15 28973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28973 : oddCount 28973 15 = 6 ∧ acceleratedOrbit 15 28973 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28973) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28973.1, data_15_28973.2]

/-- Complete interval computation for depth 15, residue 28974. -/
theorem bounds_15_28974 : exactInterval 15 28974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28974 : oddCount 28974 15 = 6 ∧ acceleratedOrbit 15 28974 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28974) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28974.1, data_15_28974.2]

/-- Complete interval computation for depth 15, residue 28975. -/
theorem bounds_15_28975 : exactInterval 15 28975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28975 : oddCount 28975 15 = 11 ∧ acceleratedOrbit 15 28975 = 156653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28975) = 3 ^ 11 * m + 156653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28975.1, data_15_28975.2]

/-- Complete interval computation for depth 15, residue 28976. -/
theorem bounds_15_28976 : exactInterval 15 28976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28976 : oddCount 28976 15 = 7 ∧ acceleratedOrbit 15 28976 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28976) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28976.1, data_15_28976.2]

/-- Complete interval computation for depth 15, residue 28977. -/
theorem bounds_15_28977 : exactInterval 15 28977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28977 : oddCount 28977 15 = 9 ∧ acceleratedOrbit 15 28977 = 17414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28977) = 3 ^ 9 * m + 17414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28977.1, data_15_28977.2]

/-- Complete interval computation for depth 15, residue 28978. -/
theorem bounds_15_28978 : exactInterval 15 28978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28978 : oddCount 28978 15 = 9 ∧ acceleratedOrbit 15 28978 = 17414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28978) = 3 ^ 9 * m + 17414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28978.1, data_15_28978.2]

/-- Complete interval computation for depth 15, residue 28979. -/
theorem bounds_15_28979 : exactInterval 15 28979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28979 : oddCount 28979 15 = 9 ∧ acceleratedOrbit 15 28979 = 17414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28979) = 3 ^ 9 * m + 17414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28979.1, data_15_28979.2]

/-- Complete interval computation for depth 15, residue 28980. -/
theorem bounds_15_28980 : exactInterval 15 28980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28980 : oddCount 28980 15 = 7 ∧ acceleratedOrbit 15 28980 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28980) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28980.1, data_15_28980.2]

/-- Complete interval computation for depth 15, residue 28981. -/
theorem bounds_15_28981 : exactInterval 15 28981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28981 : oddCount 28981 15 = 7 ∧ acceleratedOrbit 15 28981 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28981) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28981.1, data_15_28981.2]

/-- Complete interval computation for depth 15, residue 28982. -/
theorem bounds_15_28982 : exactInterval 15 28982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28982 : oddCount 28982 15 = 8 ∧ acceleratedOrbit 15 28982 = 5804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28982) = 3 ^ 8 * m + 5804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28982.1, data_15_28982.2]

/-- Complete interval computation for depth 15, residue 28983. -/
theorem bounds_15_28983 : exactInterval 15 28983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28983 : oddCount 28983 15 = 8 ∧ acceleratedOrbit 15 28983 = 5804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28983) = 3 ^ 8 * m + 5804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28983.1, data_15_28983.2]

/-- Complete interval computation for depth 15, residue 28984. -/
theorem bounds_15_28984 : exactInterval 15 28984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28984 : oddCount 28984 15 = 5 ∧ acceleratedOrbit 15 28984 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28984) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28984.1, data_15_28984.2]

/-- Complete interval computation for depth 15, residue 28985. -/
theorem bounds_15_28985 : exactInterval 15 28985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28985 : oddCount 28985 15 = 10 ∧ acceleratedOrbit 15 28985 = 52238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28985) = 3 ^ 10 * m + 52238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28985.1, data_15_28985.2]

/-- Complete interval computation for depth 15, residue 28986. -/
theorem bounds_15_28986 : exactInterval 15 28986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28986 : oddCount 28986 15 = 5 ∧ acceleratedOrbit 15 28986 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28986) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28986.1, data_15_28986.2]

/-- Complete interval computation for depth 15, residue 28987. -/
theorem bounds_15_28987 : exactInterval 15 28987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28987 : oddCount 28987 15 = 5 ∧ acceleratedOrbit 15 28987 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28987) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28987.1, data_15_28987.2]

/-- Complete interval computation for depth 15, residue 28988. -/
theorem bounds_15_28988 : exactInterval 15 28988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28988 : oddCount 28988 15 = 5 ∧ acceleratedOrbit 15 28988 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28988) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28988.1, data_15_28988.2]

/-- Complete interval computation for depth 15, residue 28989. -/
theorem bounds_15_28989 : exactInterval 15 28989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28989 : oddCount 28989 15 = 5 ∧ acceleratedOrbit 15 28989 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28989) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28989.1, data_15_28989.2]

/-- Complete interval computation for depth 15, residue 28990. -/
theorem bounds_15_28990 : exactInterval 15 28990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28990 : oddCount 28990 15 = 13 ∧ acceleratedOrbit 15 28990 = 1410614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28990) = 3 ^ 13 * m + 1410614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28990.1, data_15_28990.2]

/-- Complete interval computation for depth 15, residue 28991. -/
theorem bounds_15_28991 : exactInterval 15 28991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28991 : oddCount 28991 15 = 13 ∧ acceleratedOrbit 15 28991 = 1410614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28991) = 3 ^ 13 * m + 1410614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28991.1, data_15_28991.2]

/-- Complete interval computation for depth 15, residue 28992. -/
theorem bounds_15_28992 : exactInterval 15 28992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28992 : oddCount 28992 15 = 2 ∧ acceleratedOrbit 15 28992 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28992) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28992.1, data_15_28992.2]

/-- Complete interval computation for depth 15, residue 28993. -/
theorem bounds_15_28993 : exactInterval 15 28993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28993 : oddCount 28993 15 = 7 ∧ acceleratedOrbit 15 28993 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28993) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28993.1, data_15_28993.2]

/-- Complete interval computation for depth 15, residue 28994. -/
theorem bounds_15_28994 : exactInterval 15 28994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28994 : oddCount 28994 15 = 8 ∧ acceleratedOrbit 15 28994 = 5807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28994) = 3 ^ 8 * m + 5807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28994.1, data_15_28994.2]

/-- Complete interval computation for depth 15, residue 28995. -/
theorem bounds_15_28995 : exactInterval 15 28995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28995 : oddCount 28995 15 = 8 ∧ acceleratedOrbit 15 28995 = 5807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28995) = 3 ^ 8 * m + 5807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28995.1, data_15_28995.2]

/-- Complete interval computation for depth 15, residue 28996. -/
theorem bounds_15_28996 : exactInterval 15 28996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28996 : oddCount 28996 15 = 7 ∧ acceleratedOrbit 15 28996 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28996) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28996.1, data_15_28996.2]

/-- Complete interval computation for depth 15, residue 28997. -/
theorem bounds_15_28997 : exactInterval 15 28997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28997 : oddCount 28997 15 = 7 ∧ acceleratedOrbit 15 28997 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28997) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28997.1, data_15_28997.2]

/-- Complete interval computation for depth 15, residue 28998. -/
theorem bounds_15_28998 : exactInterval 15 28998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28998 : oddCount 28998 15 = 7 ∧ acceleratedOrbit 15 28998 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28998) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28998.1, data_15_28998.2]

end Collatz.Research.PassageAtlas.Batch0885
