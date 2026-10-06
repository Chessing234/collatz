import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0395

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2979. -/
theorem bounds_12_2979 : exactInterval 12 2979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2979 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2979) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2979 : oddCount 2979 12 = 4 ∧ acceleratedOrbit 12 2979 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2979 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2979) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2979.1, data_12_2979.2]

/-- Complete interval computation for depth 12, residue 2980. -/
theorem bounds_12_2980 : exactInterval 12 2980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2980 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2980) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2980 : oddCount 2980 12 = 7 ∧ acceleratedOrbit 12 2980 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2980 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2980) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2980.1, data_12_2980.2]

/-- Complete interval computation for depth 12, residue 2981. -/
theorem bounds_12_2981 : exactInterval 12 2981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2981 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2981) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2981 : oddCount 2981 12 = 7 ∧ acceleratedOrbit 12 2981 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2981 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2981) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2981.1, data_12_2981.2]

/-- Complete interval computation for depth 12, residue 2982. -/
theorem bounds_12_2982 : exactInterval 12 2982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2982 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2982) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2982 : oddCount 2982 12 = 7 ∧ acceleratedOrbit 12 2982 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2982 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2982) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2982.1, data_12_2982.2]

/-- Complete interval computation for depth 12, residue 2983. -/
theorem bounds_12_2983 : exactInterval 12 2983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2983 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2983) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2983 : oddCount 2983 12 = 8 ∧ acceleratedOrbit 12 2983 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2983 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2983) = 3 ^ 8 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2983.1, data_12_2983.2]

/-- Complete interval computation for depth 12, residue 2984. -/
theorem bounds_12_2984 : exactInterval 12 2984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2984 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2984) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2984 : oddCount 2984 12 = 3 ∧ acceleratedOrbit 12 2984 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2984 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2984) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2984.1, data_12_2984.2]

/-- Complete interval computation for depth 12, residue 2985. -/
theorem bounds_12_2985 : exactInterval 12 2985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2985 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2985) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2985 : oddCount 2985 12 = 8 ∧ acceleratedOrbit 12 2985 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2985 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2985) = 3 ^ 8 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2985.1, data_12_2985.2]

/-- Complete interval computation for depth 12, residue 2986. -/
theorem bounds_12_2986 : exactInterval 12 2986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2986 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2986) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2986 : oddCount 2986 12 = 3 ∧ acceleratedOrbit 12 2986 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2986 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2986) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2986.1, data_12_2986.2]

/-- Complete interval computation for depth 12, residue 2987. -/
theorem bounds_12_2987 : exactInterval 12 2987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2987 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2987) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2987 : oddCount 2987 12 = 6 ∧ acceleratedOrbit 12 2987 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2987 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2987) = 3 ^ 6 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2987.1, data_12_2987.2]

/-- Complete interval computation for depth 12, residue 2988. -/
theorem bounds_12_2988 : exactInterval 12 2988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2988 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2988) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2988 : oddCount 2988 12 = 6 ∧ acceleratedOrbit 12 2988 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2988 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2988) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2988.1, data_12_2988.2]

/-- Complete interval computation for depth 12, residue 2989. -/
theorem bounds_12_2989 : exactInterval 12 2989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2989 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2989) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2989 : oddCount 2989 12 = 6 ∧ acceleratedOrbit 12 2989 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2989 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2989) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2989.1, data_12_2989.2]

/-- Complete interval computation for depth 12, residue 2990. -/
theorem bounds_12_2990 : exactInterval 12 2990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2990 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2990) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2990 : oddCount 2990 12 = 6 ∧ acceleratedOrbit 12 2990 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2990 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2990) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2990.1, data_12_2990.2]

/-- Complete interval computation for depth 12, residue 2991. -/
theorem bounds_12_2991 : exactInterval 12 2991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2991 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2991) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2991 : oddCount 2991 12 = 6 ∧ acceleratedOrbit 12 2991 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2991 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2991) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2991.1, data_12_2991.2]

/-- Complete interval computation for depth 12, residue 2992. -/
theorem bounds_12_2992 : exactInterval 12 2992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2992 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2992) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2992 : oddCount 2992 12 = 5 ∧ acceleratedOrbit 12 2992 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2992 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2992) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2992.1, data_12_2992.2]

/-- Complete interval computation for depth 12, residue 2993. -/
theorem bounds_12_2993 : exactInterval 12 2993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2993 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2993) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2993 : oddCount 2993 12 = 5 ∧ acceleratedOrbit 12 2993 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2993 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2993) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2993.1, data_12_2993.2]

/-- Complete interval computation for depth 12, residue 2994. -/
theorem bounds_12_2994 : exactInterval 12 2994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2994 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2994) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2994 : oddCount 2994 12 = 5 ∧ acceleratedOrbit 12 2994 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2994 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2994) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2994.1, data_12_2994.2]

end Collatz.Research.StoppingAtlas.Batch0395
