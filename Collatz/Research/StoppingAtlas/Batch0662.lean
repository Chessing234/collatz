import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0662

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2984. -/
theorem bounds_13_2984 : exactInterval 13 2984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2984 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2984) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2984 : oddCount 2984 13 = 3 ∧ acceleratedOrbit 13 2984 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2984 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2984) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2984.1, data_13_2984.2]

/-- Complete interval computation for depth 13, residue 2985. -/
theorem bounds_13_2985 : exactInterval 13 2985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2985 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2985) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2985 : oddCount 2985 13 = 8 ∧ acceleratedOrbit 13 2985 = 2392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2985 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2985) = 3 ^ 8 * m + 2392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2985.1, data_13_2985.2]

/-- Complete interval computation for depth 13, residue 2986. -/
theorem bounds_13_2986 : exactInterval 13 2986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2986 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2986) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2986 : oddCount 2986 13 = 3 ∧ acceleratedOrbit 13 2986 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2986 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2986) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2986.1, data_13_2986.2]

/-- Complete interval computation for depth 13, residue 2987. -/
theorem bounds_13_2987 : exactInterval 13 2987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2987 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2987) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2987 : oddCount 2987 13 = 6 ∧ acceleratedOrbit 13 2987 = 266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2987 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2987) = 3 ^ 6 * m + 266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2987.1, data_13_2987.2]

/-- Complete interval computation for depth 13, residue 2988. -/
theorem bounds_13_2988 : exactInterval 13 2988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2988 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2988) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2988 : oddCount 2988 13 = 7 ∧ acceleratedOrbit 13 2988 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2988 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2988) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2988.1, data_13_2988.2]

/-- Complete interval computation for depth 13, residue 2989. -/
theorem bounds_13_2989 : exactInterval 13 2989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2989 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2989) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2989 : oddCount 2989 13 = 7 ∧ acceleratedOrbit 13 2989 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2989 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2989) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2989.1, data_13_2989.2]

/-- Complete interval computation for depth 13, residue 2990. -/
theorem bounds_13_2990 : exactInterval 13 2990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2990 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2990) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2990 : oddCount 2990 13 = 7 ∧ acceleratedOrbit 13 2990 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2990 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2990) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2990.1, data_13_2990.2]

/-- Complete interval computation for depth 13, residue 2991. -/
theorem bounds_13_2991 : exactInterval 13 2991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2991 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2991) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2991 : oddCount 2991 13 = 7 ∧ acceleratedOrbit 13 2991 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2991 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2991) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2991.1, data_13_2991.2]

/-- Complete interval computation for depth 13, residue 2992. -/
theorem bounds_13_2992 : exactInterval 13 2992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2992 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2992) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2992 : oddCount 2992 13 = 6 ∧ acceleratedOrbit 13 2992 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2992 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2992) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2992.1, data_13_2992.2]

/-- Complete interval computation for depth 13, residue 2993. -/
theorem bounds_13_2993 : exactInterval 13 2993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2993 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2993) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2993 : oddCount 2993 13 = 6 ∧ acceleratedOrbit 13 2993 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2993 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2993) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2993.1, data_13_2993.2]

/-- Complete interval computation for depth 13, residue 2994. -/
theorem bounds_13_2994 : exactInterval 13 2994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2994 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2994) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2994 : oddCount 2994 13 = 6 ∧ acceleratedOrbit 13 2994 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2994 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2994) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2994.1, data_13_2994.2]

/-- Complete interval computation for depth 13, residue 2995. -/
theorem bounds_13_2995 : exactInterval 13 2995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2995 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2995) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2995 : oddCount 2995 13 = 6 ∧ acceleratedOrbit 13 2995 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2995 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2995) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2995.1, data_13_2995.2]

/-- Complete interval computation for depth 13, residue 2996. -/
theorem bounds_13_2996 : exactInterval 13 2996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2996 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2996) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2996 : oddCount 2996 13 = 6 ∧ acceleratedOrbit 13 2996 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2996 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2996) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2996.1, data_13_2996.2]

/-- Complete interval computation for depth 13, residue 2997. -/
theorem bounds_13_2997 : exactInterval 13 2997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2997 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2997) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2997 : oddCount 2997 13 = 6 ∧ acceleratedOrbit 13 2997 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2997 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2997) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2997.1, data_13_2997.2]

/-- Complete interval computation for depth 13, residue 2998. -/
theorem bounds_13_2998 : exactInterval 13 2998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2998 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2998) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2998 : oddCount 2998 13 = 5 ∧ acceleratedOrbit 13 2998 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2998 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2998) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2998.1, data_13_2998.2]

/-- Complete interval computation for depth 13, residue 2999. -/
theorem bounds_13_2999 : exactInterval 13 2999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2999 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2999) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2999 : oddCount 2999 13 = 5 ∧ acceleratedOrbit 13 2999 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2999 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2999) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2999.1, data_13_2999.2]

end Collatz.Research.StoppingAtlas.Batch0662
