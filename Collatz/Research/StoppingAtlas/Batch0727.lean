import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0727

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3983. -/
theorem bounds_13_3983 : exactInterval 13 3983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3983 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3983) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3983 : oddCount 3983 13 = 7 ∧ acceleratedOrbit 13 3983 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3983 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3983) = 3 ^ 7 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3983.1, data_13_3983.2]

/-- Complete interval computation for depth 13, residue 3984. -/
theorem bounds_13_3984 : exactInterval 13 3984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3984 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3984) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3984 : oddCount 3984 13 = 5 ∧ acceleratedOrbit 13 3984 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3984 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3984) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3984.1, data_13_3984.2]

/-- Complete interval computation for depth 13, residue 3985. -/
theorem bounds_13_3985 : exactInterval 13 3985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3985 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3985) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3985 : oddCount 3985 13 = 7 ∧ acceleratedOrbit 13 3985 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3985 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3985) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3985.1, data_13_3985.2]

/-- Complete interval computation for depth 13, residue 3986. -/
theorem bounds_13_3986 : exactInterval 13 3986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3986 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3986) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3986 : oddCount 3986 13 = 7 ∧ acceleratedOrbit 13 3986 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3986 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3986) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3986.1, data_13_3986.2]

/-- Complete interval computation for depth 13, residue 3987. -/
theorem bounds_13_3987 : exactInterval 13 3987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3987 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3987) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3987 : oddCount 3987 13 = 7 ∧ acceleratedOrbit 13 3987 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3987 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3987) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3987.1, data_13_3987.2]

/-- Complete interval computation for depth 13, residue 3988. -/
theorem bounds_13_3988 : exactInterval 13 3988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3988 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3988) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3988 : oddCount 3988 13 = 5 ∧ acceleratedOrbit 13 3988 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3988 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3988) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3988.1, data_13_3988.2]

/-- Complete interval computation for depth 13, residue 3989. -/
theorem bounds_13_3989 : exactInterval 13 3989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3989 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3989) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3989 : oddCount 3989 13 = 5 ∧ acceleratedOrbit 13 3989 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3989 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3989) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3989.1, data_13_3989.2]

/-- Complete interval computation for depth 13, residue 3990. -/
theorem bounds_13_3990 : exactInterval 13 3990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3990 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3990) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3990 : oddCount 3990 13 = 5 ∧ acceleratedOrbit 13 3990 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3990 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3990) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3990.1, data_13_3990.2]

/-- Complete interval computation for depth 13, residue 3991. -/
theorem bounds_13_3991 : exactInterval 13 3991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3991 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3991) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3991 : oddCount 3991 13 = 5 ∧ acceleratedOrbit 13 3991 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3991 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3991) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3991.1, data_13_3991.2]

/-- Complete interval computation for depth 13, residue 3992. -/
theorem bounds_13_3992 : exactInterval 13 3992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3992 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3992) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3992 : oddCount 3992 13 = 5 ∧ acceleratedOrbit 13 3992 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3992 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3992) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3992.1, data_13_3992.2]

/-- Complete interval computation for depth 13, residue 3993. -/
theorem bounds_13_3993 : exactInterval 13 3993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3993 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3993) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3993 : oddCount 3993 13 = 5 ∧ acceleratedOrbit 13 3993 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3993 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3993) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3993.1, data_13_3993.2]

/-- Complete interval computation for depth 13, residue 3994. -/
theorem bounds_13_3994 : exactInterval 13 3994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3994 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3994) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3994 : oddCount 3994 13 = 5 ∧ acceleratedOrbit 13 3994 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3994 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3994) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3994.1, data_13_3994.2]

/-- Complete interval computation for depth 13, residue 3995. -/
theorem bounds_13_3995 : exactInterval 13 3995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3995 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3995) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3995 : oddCount 3995 13 = 7 ∧ acceleratedOrbit 13 3995 = 1067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3995 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3995) = 3 ^ 7 * m + 1067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3995.1, data_13_3995.2]

/-- Complete interval computation for depth 13, residue 3996. -/
theorem bounds_13_3996 : exactInterval 13 3996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3996 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3996) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3996 : oddCount 3996 13 = 6 ∧ acceleratedOrbit 13 3996 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3996 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3996) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3996.1, data_13_3996.2]

/-- Complete interval computation for depth 13, residue 3997. -/
theorem bounds_13_3997 : exactInterval 13 3997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3997 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3997) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3997 : oddCount 3997 13 = 6 ∧ acceleratedOrbit 13 3997 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3997 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3997) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3997.1, data_13_3997.2]

end Collatz.Research.StoppingAtlas.Batch0727
