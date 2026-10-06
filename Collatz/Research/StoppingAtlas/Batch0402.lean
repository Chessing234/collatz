import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0402

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3087. -/
theorem bounds_12_3087 : exactInterval 12 3087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3087 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3087) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3087 : oddCount 3087 12 = 6 ∧ acceleratedOrbit 12 3087 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3087 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3087) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3087.1, data_12_3087.2]

/-- Complete interval computation for depth 12, residue 3088. -/
theorem bounds_12_3088 : exactInterval 12 3088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3088 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3088) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3088 : oddCount 3088 12 = 4 ∧ acceleratedOrbit 12 3088 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3088 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3088) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3088.1, data_12_3088.2]

/-- Complete interval computation for depth 12, residue 3089. -/
theorem bounds_12_3089 : exactInterval 12 3089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3089 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3089) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3089 : oddCount 3089 12 = 5 ∧ acceleratedOrbit 12 3089 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3089 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3089) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3089.1, data_12_3089.2]

/-- Complete interval computation for depth 12, residue 3090. -/
theorem bounds_12_3090 : exactInterval 12 3090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3090 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3090) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3090 : oddCount 3090 12 = 6 ∧ acceleratedOrbit 12 3090 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3090 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3090) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3090.1, data_12_3090.2]

/-- Complete interval computation for depth 12, residue 3091. -/
theorem bounds_12_3091 : exactInterval 12 3091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3091 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3091) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3091 : oddCount 3091 12 = 6 ∧ acceleratedOrbit 12 3091 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3091 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3091) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3091.1, data_12_3091.2]

/-- Complete interval computation for depth 12, residue 3092. -/
theorem bounds_12_3092 : exactInterval 12 3092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3092 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3092) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3092 : oddCount 3092 12 = 4 ∧ acceleratedOrbit 12 3092 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3092 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3092) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3092.1, data_12_3092.2]

/-- Complete interval computation for depth 12, residue 3093. -/
theorem bounds_12_3093 : exactInterval 12 3093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3093 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3093) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3093 : oddCount 3093 12 = 4 ∧ acceleratedOrbit 12 3093 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3093 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3093) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3093.1, data_12_3093.2]

/-- Complete interval computation for depth 12, residue 3094. -/
theorem bounds_12_3094 : exactInterval 12 3094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3094 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3094) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3094 : oddCount 3094 12 = 5 ∧ acceleratedOrbit 12 3094 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3094 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3094) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3094.1, data_12_3094.2]

/-- Complete interval computation for depth 12, residue 3095. -/
theorem bounds_12_3095 : exactInterval 12 3095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3095 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3095) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3095 : oddCount 3095 12 = 5 ∧ acceleratedOrbit 12 3095 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3095 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3095) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3095.1, data_12_3095.2]

/-- Complete interval computation for depth 12, residue 3096. -/
theorem bounds_12_3096 : exactInterval 12 3096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3096 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3096) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3096 : oddCount 3096 12 = 4 ∧ acceleratedOrbit 12 3096 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3096 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3096) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3096.1, data_12_3096.2]

/-- Complete interval computation for depth 12, residue 3097. -/
theorem bounds_12_3097 : exactInterval 12 3097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3097 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3097) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3097 : oddCount 3097 12 = 8 ∧ acceleratedOrbit 12 3097 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3097 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3097) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3097.1, data_12_3097.2]

/-- Complete interval computation for depth 12, residue 3098. -/
theorem bounds_12_3098 : exactInterval 12 3098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3098 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3098) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3098 : oddCount 3098 12 = 4 ∧ acceleratedOrbit 12 3098 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3098 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3098) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3098.1, data_12_3098.2]

/-- Complete interval computation for depth 12, residue 3099. -/
theorem bounds_12_3099 : exactInterval 12 3099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3099 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3099) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3099 : oddCount 3099 12 = 9 ∧ acceleratedOrbit 12 3099 = 14899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3099 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3099) = 3 ^ 9 * m + 14899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3099.1, data_12_3099.2]

/-- Complete interval computation for depth 12, residue 3100. -/
theorem bounds_12_3100 : exactInterval 12 3100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3100 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3100) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3100 : oddCount 3100 12 = 6 ∧ acceleratedOrbit 12 3100 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3100 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3100) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3100.1, data_12_3100.2]

/-- Complete interval computation for depth 12, residue 3101. -/
theorem bounds_12_3101 : exactInterval 12 3101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3101 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3101) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3101 : oddCount 3101 12 = 6 ∧ acceleratedOrbit 12 3101 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3101 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3101) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3101.1, data_12_3101.2]

end Collatz.Research.StoppingAtlas.Batch0402
