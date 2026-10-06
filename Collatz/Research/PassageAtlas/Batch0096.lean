import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0096

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3112. -/
theorem bounds_15_3112 : exactInterval 15 3112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3112 : oddCount 3112 15 = 6 ∧ acceleratedOrbit 15 3112 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3112) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3112.1, data_15_3112.2]

/-- Complete interval computation for depth 15, residue 3113. -/
theorem bounds_15_3113 : exactInterval 15 3113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3113 : oddCount 3113 15 = 10 ∧ acceleratedOrbit 15 3113 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3113) = 3 ^ 10 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3113.1, data_15_3113.2]

/-- Complete interval computation for depth 15, residue 3114. -/
theorem bounds_15_3114 : exactInterval 15 3114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3114 : oddCount 3114 15 = 6 ∧ acceleratedOrbit 15 3114 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3114) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3114.1, data_15_3114.2]

/-- Complete interval computation for depth 15, residue 3115. -/
theorem bounds_15_3115 : exactInterval 15 3115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3115 : oddCount 3115 15 = 7 ∧ acceleratedOrbit 15 3115 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3115) = 3 ^ 7 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3115.1, data_15_3115.2]

/-- Complete interval computation for depth 15, residue 3116. -/
theorem bounds_15_3116 : exactInterval 15 3116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3116 : oddCount 3116 15 = 7 ∧ acceleratedOrbit 15 3116 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3116) = 3 ^ 7 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3116.1, data_15_3116.2]

/-- Complete interval computation for depth 15, residue 3117. -/
theorem bounds_15_3117 : exactInterval 15 3117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3117 : oddCount 3117 15 = 7 ∧ acceleratedOrbit 15 3117 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3117) = 3 ^ 7 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3117.1, data_15_3117.2]

/-- Complete interval computation for depth 15, residue 3118. -/
theorem bounds_15_3118 : exactInterval 15 3118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3118 : oddCount 3118 15 = 7 ∧ acceleratedOrbit 15 3118 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3118) = 3 ^ 7 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3118.1, data_15_3118.2]

/-- Complete interval computation for depth 15, residue 3119. -/
theorem bounds_15_3119 : exactInterval 15 3119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3119 : oddCount 3119 15 = 8 ∧ acceleratedOrbit 15 3119 = 625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3119) = 3 ^ 8 * m + 625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3119.1, data_15_3119.2]

/-- Complete interval computation for depth 15, residue 3120. -/
theorem bounds_15_3120 : exactInterval 15 3120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3120 : oddCount 3120 15 = 6 ∧ acceleratedOrbit 15 3120 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3120) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3120.1, data_15_3120.2]

/-- Complete interval computation for depth 15, residue 3121. -/
theorem bounds_15_3121 : exactInterval 15 3121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3121 : oddCount 3121 15 = 7 ∧ acceleratedOrbit 15 3121 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3121) = 3 ^ 7 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3121.1, data_15_3121.2]

/-- Complete interval computation for depth 15, residue 3122. -/
theorem bounds_15_3122 : exactInterval 15 3122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3122 : oddCount 3122 15 = 7 ∧ acceleratedOrbit 15 3122 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3122) = 3 ^ 7 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3122.1, data_15_3122.2]

/-- Complete interval computation for depth 15, residue 3123. -/
theorem bounds_15_3123 : exactInterval 15 3123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3123 : oddCount 3123 15 = 7 ∧ acceleratedOrbit 15 3123 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3123) = 3 ^ 7 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3123.1, data_15_3123.2]

/-- Complete interval computation for depth 15, residue 3124. -/
theorem bounds_15_3124 : exactInterval 15 3124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3124 : oddCount 3124 15 = 6 ∧ acceleratedOrbit 15 3124 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3124) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3124.1, data_15_3124.2]

/-- Complete interval computation for depth 15, residue 3125. -/
theorem bounds_15_3125 : exactInterval 15 3125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3125 : oddCount 3125 15 = 6 ∧ acceleratedOrbit 15 3125 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3125) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3125.1, data_15_3125.2]

/-- Complete interval computation for depth 15, residue 3126. -/
theorem bounds_15_3126 : exactInterval 15 3126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3126 : oddCount 3126 15 = 9 ∧ acceleratedOrbit 15 3126 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3126) = 3 ^ 9 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3126.1, data_15_3126.2]

/-- Complete interval computation for depth 15, residue 3127. -/
theorem bounds_15_3127 : exactInterval 15 3127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3127 : oddCount 3127 15 = 9 ∧ acceleratedOrbit 15 3127 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3127) = 3 ^ 9 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3127.1, data_15_3127.2]

/-- Complete interval computation for depth 15, residue 3128. -/
theorem bounds_15_3128 : exactInterval 15 3128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3128 : oddCount 3128 15 = 6 ∧ acceleratedOrbit 15 3128 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3128) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3128.1, data_15_3128.2]

/-- Complete interval computation for depth 15, residue 3129. -/
theorem bounds_15_3129 : exactInterval 15 3129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3129 : oddCount 3129 15 = 9 ∧ acceleratedOrbit 15 3129 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3129) = 3 ^ 9 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3129.1, data_15_3129.2]

/-- Complete interval computation for depth 15, residue 3130. -/
theorem bounds_15_3130 : exactInterval 15 3130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3130 : oddCount 3130 15 = 6 ∧ acceleratedOrbit 15 3130 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3130) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3130.1, data_15_3130.2]

/-- Complete interval computation for depth 15, residue 3131. -/
theorem bounds_15_3131 : exactInterval 15 3131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3131 : oddCount 3131 15 = 9 ∧ acceleratedOrbit 15 3131 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3131) = 3 ^ 9 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3131.1, data_15_3131.2]

/-- Complete interval computation for depth 15, residue 3132. -/
theorem bounds_15_3132 : exactInterval 15 3132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3132 : oddCount 3132 15 = 6 ∧ acceleratedOrbit 15 3132 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3132) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3132.1, data_15_3132.2]

/-- Complete interval computation for depth 15, residue 3133. -/
theorem bounds_15_3133 : exactInterval 15 3133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3133 : oddCount 3133 15 = 6 ∧ acceleratedOrbit 15 3133 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3133) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3133.1, data_15_3133.2]

/-- Complete interval computation for depth 15, residue 3134. -/
theorem bounds_15_3134 : exactInterval 15 3134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3134 : oddCount 3134 15 = 8 ∧ acceleratedOrbit 15 3134 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3134) = 3 ^ 8 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3134.1, data_15_3134.2]

/-- Complete interval computation for depth 15, residue 3135. -/
theorem bounds_15_3135 : exactInterval 15 3135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3135 : oddCount 3135 15 = 8 ∧ acceleratedOrbit 15 3135 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3135) = 3 ^ 8 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3135.1, data_15_3135.2]

/-- Complete interval computation for depth 15, residue 3136. -/
theorem bounds_15_3136 : exactInterval 15 3136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3136 : oddCount 3136 15 = 5 ∧ acceleratedOrbit 15 3136 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3136) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3136.1, data_15_3136.2]

/-- Complete interval computation for depth 15, residue 3137. -/
theorem bounds_15_3137 : exactInterval 15 3137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3137 : oddCount 3137 15 = 6 ∧ acceleratedOrbit 15 3137 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3137) = 3 ^ 6 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3137.1, data_15_3137.2]

/-- Complete interval computation for depth 15, residue 3138. -/
theorem bounds_15_3138 : exactInterval 15 3138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3138 : oddCount 3138 15 = 6 ∧ acceleratedOrbit 15 3138 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3138) = 3 ^ 6 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3138.1, data_15_3138.2]

/-- Complete interval computation for depth 15, residue 3139. -/
theorem bounds_15_3139 : exactInterval 15 3139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3139 : oddCount 3139 15 = 6 ∧ acceleratedOrbit 15 3139 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3139) = 3 ^ 6 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3139.1, data_15_3139.2]

/-- Complete interval computation for depth 15, residue 3140. -/
theorem bounds_15_3140 : exactInterval 15 3140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3140 : oddCount 3140 15 = 6 ∧ acceleratedOrbit 15 3140 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3140) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3140.1, data_15_3140.2]

/-- Complete interval computation for depth 15, residue 3141. -/
theorem bounds_15_3141 : exactInterval 15 3141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3141 : oddCount 3141 15 = 6 ∧ acceleratedOrbit 15 3141 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3141) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3141.1, data_15_3141.2]

/-- Complete interval computation for depth 15, residue 3142. -/
theorem bounds_15_3142 : exactInterval 15 3142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3142 : oddCount 3142 15 = 6 ∧ acceleratedOrbit 15 3142 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3142) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3142.1, data_15_3142.2]

/-- Complete interval computation for depth 15, residue 3143. -/
theorem bounds_15_3143 : exactInterval 15 3143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3143 : oddCount 3143 15 = 10 ∧ acceleratedOrbit 15 3143 = 5669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3143) = 3 ^ 10 * m + 5669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3143.1, data_15_3143.2]

/-- Complete interval computation for depth 15, residue 3144. -/
theorem bounds_15_3144 : exactInterval 15 3144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3144 : oddCount 3144 15 = 7 ∧ acceleratedOrbit 15 3144 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3144) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3144.1, data_15_3144.2]

end Collatz.Research.PassageAtlas.Batch0096
