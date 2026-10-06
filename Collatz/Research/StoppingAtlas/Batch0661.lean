import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0661

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2969. -/
theorem bounds_13_2969 : exactInterval 13 2969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2969 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2969) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2969 : oddCount 2969 13 = 6 ∧ acceleratedOrbit 13 2969 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2969 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2969) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2969.1, data_13_2969.2]

/-- Complete interval computation for depth 13, residue 2970. -/
theorem bounds_13_2970 : exactInterval 13 2970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2970 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2970) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2970 : oddCount 2970 13 = 5 ∧ acceleratedOrbit 13 2970 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2970 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2970) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2970.1, data_13_2970.2]

/-- Complete interval computation for depth 13, residue 2971. -/
theorem bounds_13_2971 : exactInterval 13 2971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2971 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2971) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2971 : oddCount 2971 13 = 7 ∧ acceleratedOrbit 13 2971 = 794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2971 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2971) = 3 ^ 7 * m + 794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2971.1, data_13_2971.2]

/-- Complete interval computation for depth 13, residue 2972. -/
theorem bounds_13_2972 : exactInterval 13 2972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2972 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2972) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2972 : oddCount 2972 13 = 9 ∧ acceleratedOrbit 13 2972 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2972 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2972) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2972.1, data_13_2972.2]

/-- Complete interval computation for depth 13, residue 2973. -/
theorem bounds_13_2973 : exactInterval 13 2973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2973 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2973) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2973 : oddCount 2973 13 = 9 ∧ acceleratedOrbit 13 2973 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2973 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2973) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2973.1, data_13_2973.2]

/-- Complete interval computation for depth 13, residue 2974. -/
theorem bounds_13_2974 : exactInterval 13 2974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2974 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2974) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2974 : oddCount 2974 13 = 9 ∧ acceleratedOrbit 13 2974 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2974 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2974) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2974.1, data_13_2974.2]

/-- Complete interval computation for depth 13, residue 2975. -/
theorem bounds_13_2975 : exactInterval 13 2975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2975 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2975) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2975 : oddCount 2975 13 = 8 ∧ acceleratedOrbit 13 2975 = 2384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2975 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2975) = 3 ^ 8 * m + 2384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2975.1, data_13_2975.2]

/-- Complete interval computation for depth 13, residue 2976. -/
theorem bounds_13_2976 : exactInterval 13 2976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2976 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2976) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2976 : oddCount 2976 13 = 3 ∧ acceleratedOrbit 13 2976 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2976 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2976) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2976.1, data_13_2976.2]

/-- Complete interval computation for depth 13, residue 2977. -/
theorem bounds_13_2977 : exactInterval 13 2977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2977 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2977) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2977 : oddCount 2977 13 = 7 ∧ acceleratedOrbit 13 2977 = 796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2977 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2977) = 3 ^ 7 * m + 796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2977.1, data_13_2977.2]

/-- Complete interval computation for depth 13, residue 2978. -/
theorem bounds_13_2978 : exactInterval 13 2978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2978 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2978) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2978 : oddCount 2978 13 = 5 ∧ acceleratedOrbit 13 2978 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2978 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2978) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2978.1, data_13_2978.2]

/-- Complete interval computation for depth 13, residue 2979. -/
theorem bounds_13_2979 : exactInterval 13 2979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2979 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2979) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2979 : oddCount 2979 13 = 5 ∧ acceleratedOrbit 13 2979 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2979 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2979) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2979.1, data_13_2979.2]

/-- Complete interval computation for depth 13, residue 2980. -/
theorem bounds_13_2980 : exactInterval 13 2980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2980 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2980) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2980 : oddCount 2980 13 = 8 ∧ acceleratedOrbit 13 2980 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2980 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2980) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2980.1, data_13_2980.2]

/-- Complete interval computation for depth 13, residue 2981. -/
theorem bounds_13_2981 : exactInterval 13 2981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2981 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2981) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2981 : oddCount 2981 13 = 8 ∧ acceleratedOrbit 13 2981 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2981 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2981) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2981.1, data_13_2981.2]

/-- Complete interval computation for depth 13, residue 2982. -/
theorem bounds_13_2982 : exactInterval 13 2982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2982 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2982) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2982 : oddCount 2982 13 = 8 ∧ acceleratedOrbit 13 2982 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2982 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2982) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2982.1, data_13_2982.2]

/-- Complete interval computation for depth 13, residue 2983. -/
theorem bounds_13_2983 : exactInterval 13 2983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2983 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2983) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2983 : oddCount 2983 13 = 9 ∧ acceleratedOrbit 13 2983 = 7172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2983 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2983) = 3 ^ 9 * m + 7172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2983.1, data_13_2983.2]

end Collatz.Research.StoppingAtlas.Batch0661
