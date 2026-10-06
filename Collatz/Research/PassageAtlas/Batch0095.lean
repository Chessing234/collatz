import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0095

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3080. -/
theorem bounds_15_3080 : exactInterval 15 3080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3080 : oddCount 3080 15 = 5 ∧ acceleratedOrbit 15 3080 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3080) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3080.1, data_15_3080.2]

/-- Complete interval computation for depth 15, residue 3081. -/
theorem bounds_15_3081 : exactInterval 15 3081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3081 : oddCount 3081 15 = 9 ∧ acceleratedOrbit 15 3081 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3081) = 3 ^ 9 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3081.1, data_15_3081.2]

/-- Complete interval computation for depth 15, residue 3082. -/
theorem bounds_15_3082 : exactInterval 15 3082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3082 : oddCount 3082 15 = 5 ∧ acceleratedOrbit 15 3082 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3082) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3082.1, data_15_3082.2]

/-- Complete interval computation for depth 15, residue 3083. -/
theorem bounds_15_3083 : exactInterval 15 3083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3083 : oddCount 3083 15 = 5 ∧ acceleratedOrbit 15 3083 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3083) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3083.1, data_15_3083.2]

/-- Complete interval computation for depth 15, residue 3084. -/
theorem bounds_15_3084 : exactInterval 15 3084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3084 : oddCount 3084 15 = 5 ∧ acceleratedOrbit 15 3084 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3084) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3084.1, data_15_3084.2]

/-- Complete interval computation for depth 15, residue 3085. -/
theorem bounds_15_3085 : exactInterval 15 3085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3085 : oddCount 3085 15 = 5 ∧ acceleratedOrbit 15 3085 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3085) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3085.1, data_15_3085.2]

/-- Complete interval computation for depth 15, residue 3086. -/
theorem bounds_15_3086 : exactInterval 15 3086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3086 : oddCount 3086 15 = 8 ∧ acceleratedOrbit 15 3086 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3086) = 3 ^ 8 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3086.1, data_15_3086.2]

/-- Complete interval computation for depth 15, residue 3087. -/
theorem bounds_15_3087 : exactInterval 15 3087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3087 : oddCount 3087 15 = 8 ∧ acceleratedOrbit 15 3087 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3087) = 3 ^ 8 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3087.1, data_15_3087.2]

/-- Complete interval computation for depth 15, residue 3088. -/
theorem bounds_15_3088 : exactInterval 15 3088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3088 : oddCount 3088 15 = 6 ∧ acceleratedOrbit 15 3088 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3088) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3088.1, data_15_3088.2]

/-- Complete interval computation for depth 15, residue 3089. -/
theorem bounds_15_3089 : exactInterval 15 3089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3089 : oddCount 3089 15 = 5 ∧ acceleratedOrbit 15 3089 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3089) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3089.1, data_15_3089.2]

/-- Complete interval computation for depth 15, residue 3090. -/
theorem bounds_15_3090 : exactInterval 15 3090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3090 : oddCount 3090 15 = 9 ∧ acceleratedOrbit 15 3090 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3090) = 3 ^ 9 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3090.1, data_15_3090.2]

/-- Complete interval computation for depth 15, residue 3091. -/
theorem bounds_15_3091 : exactInterval 15 3091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3091 : oddCount 3091 15 = 9 ∧ acceleratedOrbit 15 3091 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3091) = 3 ^ 9 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3091.1, data_15_3091.2]

/-- Complete interval computation for depth 15, residue 3092. -/
theorem bounds_15_3092 : exactInterval 15 3092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3092 : oddCount 3092 15 = 6 ∧ acceleratedOrbit 15 3092 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3092) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3092.1, data_15_3092.2]

/-- Complete interval computation for depth 15, residue 3093. -/
theorem bounds_15_3093 : exactInterval 15 3093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3093 : oddCount 3093 15 = 6 ∧ acceleratedOrbit 15 3093 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3093) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3093.1, data_15_3093.2]

/-- Complete interval computation for depth 15, residue 3094. -/
theorem bounds_15_3094 : exactInterval 15 3094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3094 : oddCount 3094 15 = 5 ∧ acceleratedOrbit 15 3094 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3094) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3094.1, data_15_3094.2]

/-- Complete interval computation for depth 15, residue 3095. -/
theorem bounds_15_3095 : exactInterval 15 3095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3095 : oddCount 3095 15 = 5 ∧ acceleratedOrbit 15 3095 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3095) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3095.1, data_15_3095.2]

/-- Complete interval computation for depth 15, residue 3096. -/
theorem bounds_15_3096 : exactInterval 15 3096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3096 : oddCount 3096 15 = 6 ∧ acceleratedOrbit 15 3096 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3096) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3096.1, data_15_3096.2]

/-- Complete interval computation for depth 15, residue 3097. -/
theorem bounds_15_3097 : exactInterval 15 3097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3097 : oddCount 3097 15 = 11 ∧ acceleratedOrbit 15 3097 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3097) = 3 ^ 11 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3097.1, data_15_3097.2]

/-- Complete interval computation for depth 15, residue 3098. -/
theorem bounds_15_3098 : exactInterval 15 3098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3098 : oddCount 3098 15 = 6 ∧ acceleratedOrbit 15 3098 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3098) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3098.1, data_15_3098.2]

/-- Complete interval computation for depth 15, residue 3099. -/
theorem bounds_15_3099 : exactInterval 15 3099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3099 : oddCount 3099 15 = 11 ∧ acceleratedOrbit 15 3099 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3099) = 3 ^ 11 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3099.1, data_15_3099.2]

/-- Complete interval computation for depth 15, residue 3100. -/
theorem bounds_15_3100 : exactInterval 15 3100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3100 : oddCount 3100 15 = 8 ∧ acceleratedOrbit 15 3100 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3100) = 3 ^ 8 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3100.1, data_15_3100.2]

/-- Complete interval computation for depth 15, residue 3101. -/
theorem bounds_15_3101 : exactInterval 15 3101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3101 : oddCount 3101 15 = 8 ∧ acceleratedOrbit 15 3101 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3101) = 3 ^ 8 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3101.1, data_15_3101.2]

/-- Complete interval computation for depth 15, residue 3102. -/
theorem bounds_15_3102 : exactInterval 15 3102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3102 : oddCount 3102 15 = 8 ∧ acceleratedOrbit 15 3102 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3102) = 3 ^ 8 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3102.1, data_15_3102.2]

/-- Complete interval computation for depth 15, residue 3103. -/
theorem bounds_15_3103 : exactInterval 15 3103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3103 : oddCount 3103 15 = 10 ∧ acceleratedOrbit 15 3103 = 5594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3103) = 3 ^ 10 * m + 5594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3103.1, data_15_3103.2]

/-- Complete interval computation for depth 15, residue 3104. -/
theorem bounds_15_3104 : exactInterval 15 3104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3104 : oddCount 3104 15 = 6 ∧ acceleratedOrbit 15 3104 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3104) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3104.1, data_15_3104.2]

/-- Complete interval computation for depth 15, residue 3105. -/
theorem bounds_15_3105 : exactInterval 15 3105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3105 : oddCount 3105 15 = 8 ∧ acceleratedOrbit 15 3105 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3105) = 3 ^ 8 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3105.1, data_15_3105.2]

/-- Complete interval computation for depth 15, residue 3106. -/
theorem bounds_15_3106 : exactInterval 15 3106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3106 : oddCount 3106 15 = 6 ∧ acceleratedOrbit 15 3106 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3106) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3106.1, data_15_3106.2]

/-- Complete interval computation for depth 15, residue 3107. -/
theorem bounds_15_3107 : exactInterval 15 3107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3107 : oddCount 3107 15 = 6 ∧ acceleratedOrbit 15 3107 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3107) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3107.1, data_15_3107.2]

/-- Complete interval computation for depth 15, residue 3108. -/
theorem bounds_15_3108 : exactInterval 15 3108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3108 : oddCount 3108 15 = 7 ∧ acceleratedOrbit 15 3108 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3108) = 3 ^ 7 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3108.1, data_15_3108.2]

/-- Complete interval computation for depth 15, residue 3109. -/
theorem bounds_15_3109 : exactInterval 15 3109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3109 : oddCount 3109 15 = 7 ∧ acceleratedOrbit 15 3109 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3109) = 3 ^ 7 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3109.1, data_15_3109.2]

/-- Complete interval computation for depth 15, residue 3110. -/
theorem bounds_15_3110 : exactInterval 15 3110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3110 : oddCount 3110 15 = 7 ∧ acceleratedOrbit 15 3110 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3110) = 3 ^ 7 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3110.1, data_15_3110.2]

/-- Complete interval computation for depth 15, residue 3111. -/
theorem bounds_15_3111 : exactInterval 15 3111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3111 : oddCount 3111 15 = 7 ∧ acceleratedOrbit 15 3111 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3111) = 3 ^ 7 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3111.1, data_15_3111.2]

end Collatz.Research.PassageAtlas.Batch0095
