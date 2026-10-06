import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0824

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26968. -/
theorem bounds_15_26968 : exactInterval 15 26968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26968 : oddCount 26968 15 = 7 ∧ acceleratedOrbit 15 26968 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26968) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26968.1, data_15_26968.2]

/-- Complete interval computation for depth 15, residue 26969. -/
theorem bounds_15_26969 : exactInterval 15 26969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26969 : oddCount 26969 15 = 8 ∧ acceleratedOrbit 15 26969 = 5402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26969) = 3 ^ 8 * m + 5402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26969.1, data_15_26969.2]

/-- Complete interval computation for depth 15, residue 26970. -/
theorem bounds_15_26970 : exactInterval 15 26970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26970 : oddCount 26970 15 = 7 ∧ acceleratedOrbit 15 26970 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26970) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26970.1, data_15_26970.2]

/-- Complete interval computation for depth 15, residue 26971. -/
theorem bounds_15_26971 : exactInterval 15 26971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26971 : oddCount 26971 15 = 8 ∧ acceleratedOrbit 15 26971 = 5401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26971) = 3 ^ 8 * m + 5401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26971.1, data_15_26971.2]

/-- Complete interval computation for depth 15, residue 26972. -/
theorem bounds_15_26972 : exactInterval 15 26972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26972 : oddCount 26972 15 = 7 ∧ acceleratedOrbit 15 26972 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26972) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26972.1, data_15_26972.2]

/-- Complete interval computation for depth 15, residue 26973. -/
theorem bounds_15_26973 : exactInterval 15 26973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26973 : oddCount 26973 15 = 7 ∧ acceleratedOrbit 15 26973 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26973) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26973.1, data_15_26973.2]

/-- Complete interval computation for depth 15, residue 26974. -/
theorem bounds_15_26974 : exactInterval 15 26974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26974 : oddCount 26974 15 = 8 ∧ acceleratedOrbit 15 26974 = 5402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26974) = 3 ^ 8 * m + 5402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26974.1, data_15_26974.2]

/-- Complete interval computation for depth 15, residue 26975. -/
theorem bounds_15_26975 : exactInterval 15 26975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26975 : oddCount 26975 15 = 8 ∧ acceleratedOrbit 15 26975 = 5402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26975) = 3 ^ 8 * m + 5402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26975.1, data_15_26975.2]

/-- Complete interval computation for depth 15, residue 26976. -/
theorem bounds_15_26976 : exactInterval 15 26976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26976 : oddCount 26976 15 = 4 ∧ acceleratedOrbit 15 26976 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26976) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26976.1, data_15_26976.2]

/-- Complete interval computation for depth 15, residue 26977. -/
theorem bounds_15_26977 : exactInterval 15 26977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26977 : oddCount 26977 15 = 10 ∧ acceleratedOrbit 15 26977 = 48620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26977) = 3 ^ 10 * m + 48620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26977.1, data_15_26977.2]

/-- Complete interval computation for depth 15, residue 26978. -/
theorem bounds_15_26978 : exactInterval 15 26978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26978 : oddCount 26978 15 = 7 ∧ acceleratedOrbit 15 26978 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26978) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26978.1, data_15_26978.2]

/-- Complete interval computation for depth 15, residue 26979. -/
theorem bounds_15_26979 : exactInterval 15 26979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26979 : oddCount 26979 15 = 7 ∧ acceleratedOrbit 15 26979 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26979) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26979.1, data_15_26979.2]

/-- Complete interval computation for depth 15, residue 26980. -/
theorem bounds_15_26980 : exactInterval 15 26980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26980 : oddCount 26980 15 = 7 ∧ acceleratedOrbit 15 26980 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26980) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26980.1, data_15_26980.2]

/-- Complete interval computation for depth 15, residue 26981. -/
theorem bounds_15_26981 : exactInterval 15 26981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26981 : oddCount 26981 15 = 7 ∧ acceleratedOrbit 15 26981 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26981) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26981.1, data_15_26981.2]

/-- Complete interval computation for depth 15, residue 26982. -/
theorem bounds_15_26982 : exactInterval 15 26982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26982 : oddCount 26982 15 = 7 ∧ acceleratedOrbit 15 26982 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26982) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26982.1, data_15_26982.2]

/-- Complete interval computation for depth 15, residue 26983. -/
theorem bounds_15_26983 : exactInterval 15 26983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26983 : oddCount 26983 15 = 12 ∧ acceleratedOrbit 15 26983 = 437642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26983) = 3 ^ 12 * m + 437642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26983.1, data_15_26983.2]

/-- Complete interval computation for depth 15, residue 26984. -/
theorem bounds_15_26984 : exactInterval 15 26984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26984 : oddCount 26984 15 = 4 ∧ acceleratedOrbit 15 26984 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26984) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26984.1, data_15_26984.2]

/-- Complete interval computation for depth 15, residue 26985. -/
theorem bounds_15_26985 : exactInterval 15 26985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26985 : oddCount 26985 15 = 7 ∧ acceleratedOrbit 15 26985 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26985) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26985.1, data_15_26985.2]

/-- Complete interval computation for depth 15, residue 26986. -/
theorem bounds_15_26986 : exactInterval 15 26986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26986 : oddCount 26986 15 = 4 ∧ acceleratedOrbit 15 26986 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26986) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26986.1, data_15_26986.2]

/-- Complete interval computation for depth 15, residue 26987. -/
theorem bounds_15_26987 : exactInterval 15 26987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26987 : oddCount 26987 15 = 9 ∧ acceleratedOrbit 15 26987 = 16213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26987) = 3 ^ 9 * m + 16213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26987.1, data_15_26987.2]

/-- Complete interval computation for depth 15, residue 26988. -/
theorem bounds_15_26988 : exactInterval 15 26988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26988 : oddCount 26988 15 = 8 ∧ acceleratedOrbit 15 26988 = 5405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26988) = 3 ^ 8 * m + 5405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26988.1, data_15_26988.2]

/-- Complete interval computation for depth 15, residue 26989. -/
theorem bounds_15_26989 : exactInterval 15 26989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26989 : oddCount 26989 15 = 8 ∧ acceleratedOrbit 15 26989 = 5405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26989) = 3 ^ 8 * m + 5405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26989.1, data_15_26989.2]

/-- Complete interval computation for depth 15, residue 26990. -/
theorem bounds_15_26990 : exactInterval 15 26990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26990 : oddCount 26990 15 = 8 ∧ acceleratedOrbit 15 26990 = 5405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26990) = 3 ^ 8 * m + 5405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26990.1, data_15_26990.2]

/-- Complete interval computation for depth 15, residue 26991. -/
theorem bounds_15_26991 : exactInterval 15 26991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26991 : oddCount 26991 15 = 7 ∧ acceleratedOrbit 15 26991 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26991) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26991.1, data_15_26991.2]

/-- Complete interval computation for depth 15, residue 26992. -/
theorem bounds_15_26992 : exactInterval 15 26992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26992 : oddCount 26992 15 = 4 ∧ acceleratedOrbit 15 26992 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26992) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26992.1, data_15_26992.2]

/-- Complete interval computation for depth 15, residue 26993. -/
theorem bounds_15_26993 : exactInterval 15 26993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26993 : oddCount 26993 15 = 4 ∧ acceleratedOrbit 15 26993 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26993) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26993.1, data_15_26993.2]

/-- Complete interval computation for depth 15, residue 26994. -/
theorem bounds_15_26994 : exactInterval 15 26994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26994 : oddCount 26994 15 = 9 ∧ acceleratedOrbit 15 26994 = 16220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26994) = 3 ^ 9 * m + 16220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26994.1, data_15_26994.2]

/-- Complete interval computation for depth 15, residue 26995. -/
theorem bounds_15_26995 : exactInterval 15 26995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26995 : oddCount 26995 15 = 9 ∧ acceleratedOrbit 15 26995 = 16220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26995) = 3 ^ 9 * m + 16220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26995.1, data_15_26995.2]

/-- Complete interval computation for depth 15, residue 26996. -/
theorem bounds_15_26996 : exactInterval 15 26996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26996 : oddCount 26996 15 = 4 ∧ acceleratedOrbit 15 26996 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26996) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26996.1, data_15_26996.2]

/-- Complete interval computation for depth 15, residue 26997. -/
theorem bounds_15_26997 : exactInterval 15 26997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26997 : oddCount 26997 15 = 4 ∧ acceleratedOrbit 15 26997 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26997) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26997.1, data_15_26997.2]

/-- Complete interval computation for depth 15, residue 26998. -/
theorem bounds_15_26998 : exactInterval 15 26998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26998 : oddCount 26998 15 = 9 ∧ acceleratedOrbit 15 26998 = 16220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26998) = 3 ^ 9 * m + 16220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26998.1, data_15_26998.2]

/-- Complete interval computation for depth 15, residue 26999. -/
theorem bounds_15_26999 : exactInterval 15 26999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26999 : oddCount 26999 15 = 9 ∧ acceleratedOrbit 15 26999 = 16220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26999) = 3 ^ 9 * m + 16220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26999.1, data_15_26999.2]

end Collatz.Research.PassageAtlas.Batch0824
