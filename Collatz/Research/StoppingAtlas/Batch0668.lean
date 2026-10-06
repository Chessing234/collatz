import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0668

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3077. -/
theorem bounds_13_3077 : exactInterval 13 3077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3077 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3077) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3077 : oddCount 3077 13 = 5 ∧ acceleratedOrbit 13 3077 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3077 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3077) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3077.1, data_13_3077.2]

/-- Complete interval computation for depth 13, residue 3078. -/
theorem bounds_13_3078 : exactInterval 13 3078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3078 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3078) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3078 : oddCount 3078 13 = 5 ∧ acceleratedOrbit 13 3078 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3078 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3078) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3078.1, data_13_3078.2]

/-- Complete interval computation for depth 13, residue 3079. -/
theorem bounds_13_3079 : exactInterval 13 3079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3079 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3079) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3079 : oddCount 3079 13 = 7 ∧ acceleratedOrbit 13 3079 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3079 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3079) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3079.1, data_13_3079.2]

/-- Complete interval computation for depth 13, residue 3080. -/
theorem bounds_13_3080 : exactInterval 13 3080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3080 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3080) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3080 : oddCount 3080 13 = 5 ∧ acceleratedOrbit 13 3080 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3080 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3080) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3080.1, data_13_3080.2]

/-- Complete interval computation for depth 13, residue 3081. -/
theorem bounds_13_3081 : exactInterval 13 3081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3081 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3081) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3081 : oddCount 3081 13 = 8 ∧ acceleratedOrbit 13 3081 = 2470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3081 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3081) = 3 ^ 8 * m + 2470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3081.1, data_13_3081.2]

/-- Complete interval computation for depth 13, residue 3082. -/
theorem bounds_13_3082 : exactInterval 13 3082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3082 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3082) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3082 : oddCount 3082 13 = 5 ∧ acceleratedOrbit 13 3082 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3082 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3082) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3082.1, data_13_3082.2]

/-- Complete interval computation for depth 13, residue 3083. -/
theorem bounds_13_3083 : exactInterval 13 3083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3083 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3083) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3083 : oddCount 3083 13 = 5 ∧ acceleratedOrbit 13 3083 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3083 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3083) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3083.1, data_13_3083.2]

/-- Complete interval computation for depth 13, residue 3084. -/
theorem bounds_13_3084 : exactInterval 13 3084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3084 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3084) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3084 : oddCount 3084 13 = 5 ∧ acceleratedOrbit 13 3084 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3084 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3084) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3084.1, data_13_3084.2]

/-- Complete interval computation for depth 13, residue 3085. -/
theorem bounds_13_3085 : exactInterval 13 3085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3085 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3085) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3085 : oddCount 3085 13 = 5 ∧ acceleratedOrbit 13 3085 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3085 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3085) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3085.1, data_13_3085.2]

/-- Complete interval computation for depth 13, residue 3086. -/
theorem bounds_13_3086 : exactInterval 13 3086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3086 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3086) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3086 : oddCount 3086 13 = 6 ∧ acceleratedOrbit 13 3086 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3086 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3086) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3086.1, data_13_3086.2]

/-- Complete interval computation for depth 13, residue 3087. -/
theorem bounds_13_3087 : exactInterval 13 3087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3087 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3087) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3087 : oddCount 3087 13 = 6 ∧ acceleratedOrbit 13 3087 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3087 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3087) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3087.1, data_13_3087.2]

/-- Complete interval computation for depth 13, residue 3088. -/
theorem bounds_13_3088 : exactInterval 13 3088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3088 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3088) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3088 : oddCount 3088 13 = 4 ∧ acceleratedOrbit 13 3088 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3088 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3088) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3088.1, data_13_3088.2]

/-- Complete interval computation for depth 13, residue 3089. -/
theorem bounds_13_3089 : exactInterval 13 3089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3089 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3089) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3089 : oddCount 3089 13 = 5 ∧ acceleratedOrbit 13 3089 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3089 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3089) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3089.1, data_13_3089.2]

/-- Complete interval computation for depth 13, residue 3090. -/
theorem bounds_13_3090 : exactInterval 13 3090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3090 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3090) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3090 : oddCount 3090 13 = 7 ∧ acceleratedOrbit 13 3090 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3090 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3090) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3090.1, data_13_3090.2]

/-- Complete interval computation for depth 13, residue 3091. -/
theorem bounds_13_3091 : exactInterval 13 3091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3091 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3091) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3091 : oddCount 3091 13 = 7 ∧ acceleratedOrbit 13 3091 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3091 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3091) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3091.1, data_13_3091.2]

end Collatz.Research.StoppingAtlas.Batch0668
