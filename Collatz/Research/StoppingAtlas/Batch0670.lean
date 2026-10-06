import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0670

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3107. -/
theorem bounds_13_3107 : exactInterval 13 3107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3107 : oddCount 3107 13 = 4 ∧ acceleratedOrbit 13 3107 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3107) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3107.1, data_13_3107.2]

/-- Complete interval computation for depth 13, residue 3108. -/
theorem bounds_13_3108 : exactInterval 13 3108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3108 : oddCount 3108 13 = 7 ∧ acceleratedOrbit 13 3108 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3108) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3108.1, data_13_3108.2]

/-- Complete interval computation for depth 13, residue 3109. -/
theorem bounds_13_3109 : exactInterval 13 3109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3109 : oddCount 3109 13 = 7 ∧ acceleratedOrbit 13 3109 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3109) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3109.1, data_13_3109.2]

/-- Complete interval computation for depth 13, residue 3110. -/
theorem bounds_13_3110 : exactInterval 13 3110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3110 : oddCount 3110 13 = 7 ∧ acceleratedOrbit 13 3110 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3110) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3110.1, data_13_3110.2]

/-- Complete interval computation for depth 13, residue 3111. -/
theorem bounds_13_3111 : exactInterval 13 3111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3111 : oddCount 3111 13 = 6 ∧ acceleratedOrbit 13 3111 = 277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3111) = 3 ^ 6 * m + 277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3111.1, data_13_3111.2]

/-- Complete interval computation for depth 13, residue 3112. -/
theorem bounds_13_3112 : exactInterval 13 3112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3112 : oddCount 3112 13 = 5 ∧ acceleratedOrbit 13 3112 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3112) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3112.1, data_13_3112.2]

/-- Complete interval computation for depth 13, residue 3113. -/
theorem bounds_13_3113 : exactInterval 13 3113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3113 : oddCount 3113 13 = 8 ∧ acceleratedOrbit 13 3113 = 2495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3113) = 3 ^ 8 * m + 2495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3113.1, data_13_3113.2]

/-- Complete interval computation for depth 13, residue 3114. -/
theorem bounds_13_3114 : exactInterval 13 3114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3114 : oddCount 3114 13 = 5 ∧ acceleratedOrbit 13 3114 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3114) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3114.1, data_13_3114.2]

/-- Complete interval computation for depth 13, residue 3115. -/
theorem bounds_13_3115 : exactInterval 13 3115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3115 : oddCount 3115 13 = 6 ∧ acceleratedOrbit 13 3115 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3115) = 3 ^ 6 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3115.1, data_13_3115.2]

/-- Complete interval computation for depth 13, residue 3116. -/
theorem bounds_13_3116 : exactInterval 13 3116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3116 : oddCount 3116 13 = 7 ∧ acceleratedOrbit 13 3116 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3116) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3116.1, data_13_3116.2]

/-- Complete interval computation for depth 13, residue 3117. -/
theorem bounds_13_3117 : exactInterval 13 3117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3117 : oddCount 3117 13 = 7 ∧ acceleratedOrbit 13 3117 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3117) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3117.1, data_13_3117.2]

/-- Complete interval computation for depth 13, residue 3118. -/
theorem bounds_13_3118 : exactInterval 13 3118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3118 : oddCount 3118 13 = 7 ∧ acceleratedOrbit 13 3118 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3118) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3118.1, data_13_3118.2]

/-- Complete interval computation for depth 13, residue 3119. -/
theorem bounds_13_3119 : exactInterval 13 3119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3119 : oddCount 3119 13 = 7 ∧ acceleratedOrbit 13 3119 = 833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3119) = 3 ^ 7 * m + 833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3119.1, data_13_3119.2]

/-- Complete interval computation for depth 13, residue 3120. -/
theorem bounds_13_3120 : exactInterval 13 3120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3120 : oddCount 3120 13 = 5 ∧ acceleratedOrbit 13 3120 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3120) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3120.1, data_13_3120.2]

/-- Complete interval computation for depth 13, residue 3121. -/
theorem bounds_13_3121 : exactInterval 13 3121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3121 : oddCount 3121 13 = 7 ∧ acceleratedOrbit 13 3121 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3121) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3121.1, data_13_3121.2]

/-- Complete interval computation for depth 13, residue 3122. -/
theorem bounds_13_3122 : exactInterval 13 3122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3122 : oddCount 3122 13 = 7 ∧ acceleratedOrbit 13 3122 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3122) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3122.1, data_13_3122.2]

end Collatz.Research.StoppingAtlas.Batch0670
