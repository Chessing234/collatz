import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0403

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3102. -/
theorem bounds_12_3102 : exactInterval 12 3102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3102 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3102) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3102 : oddCount 3102 12 = 6 ∧ acceleratedOrbit 12 3102 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3102 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3102) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3102.1, data_12_3102.2]

/-- Complete interval computation for depth 12, residue 3103. -/
theorem bounds_12_3103 : exactInterval 12 3103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3103 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3103) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3103 : oddCount 3103 12 = 9 ∧ acceleratedOrbit 12 3103 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3103 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3103) = 3 ^ 9 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3103.1, data_12_3103.2]

/-- Complete interval computation for depth 12, residue 3104. -/
theorem bounds_12_3104 : exactInterval 12 3104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3104 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3104) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3104 : oddCount 3104 12 = 5 ∧ acceleratedOrbit 12 3104 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3104 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3104) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3104.1, data_12_3104.2]

/-- Complete interval computation for depth 12, residue 3105. -/
theorem bounds_12_3105 : exactInterval 12 3105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3105 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3105) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3105 : oddCount 3105 12 = 7 ∧ acceleratedOrbit 12 3105 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3105 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3105) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3105.1, data_12_3105.2]

/-- Complete interval computation for depth 12, residue 3106. -/
theorem bounds_12_3106 : exactInterval 12 3106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3106 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3106) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3106 : oddCount 3106 12 = 4 ∧ acceleratedOrbit 12 3106 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3106 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3106) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3106.1, data_12_3106.2]

/-- Complete interval computation for depth 12, residue 3107. -/
theorem bounds_12_3107 : exactInterval 12 3107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3107 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3107) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3107 : oddCount 3107 12 = 4 ∧ acceleratedOrbit 12 3107 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3107 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3107) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3107.1, data_12_3107.2]

/-- Complete interval computation for depth 12, residue 3108. -/
theorem bounds_12_3108 : exactInterval 12 3108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3108 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3108) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3108 : oddCount 3108 12 = 7 ∧ acceleratedOrbit 12 3108 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3108 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3108) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3108.1, data_12_3108.2]

/-- Complete interval computation for depth 12, residue 3109. -/
theorem bounds_12_3109 : exactInterval 12 3109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3109 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3109) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3109 : oddCount 3109 12 = 7 ∧ acceleratedOrbit 12 3109 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3109 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3109) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3109.1, data_12_3109.2]

/-- Complete interval computation for depth 12, residue 3110. -/
theorem bounds_12_3110 : exactInterval 12 3110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3110 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3110) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3110 : oddCount 3110 12 = 7 ∧ acceleratedOrbit 12 3110 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3110 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3110) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3110.1, data_12_3110.2]

/-- Complete interval computation for depth 12, residue 3111. -/
theorem bounds_12_3111 : exactInterval 12 3111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3111 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3111) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3111 : oddCount 3111 12 = 6 ∧ acceleratedOrbit 12 3111 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3111 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3111) = 3 ^ 6 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3111.1, data_12_3111.2]

/-- Complete interval computation for depth 12, residue 3112. -/
theorem bounds_12_3112 : exactInterval 12 3112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3112 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3112) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3112 : oddCount 3112 12 = 5 ∧ acceleratedOrbit 12 3112 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3112 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3112) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3112.1, data_12_3112.2]

/-- Complete interval computation for depth 12, residue 3113. -/
theorem bounds_12_3113 : exactInterval 12 3113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3113 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3113) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3113 : oddCount 3113 12 = 7 ∧ acceleratedOrbit 12 3113 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3113 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3113) = 3 ^ 7 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3113.1, data_12_3113.2]

/-- Complete interval computation for depth 12, residue 3114. -/
theorem bounds_12_3114 : exactInterval 12 3114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3114 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3114) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3114 : oddCount 3114 12 = 5 ∧ acceleratedOrbit 12 3114 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3114 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3114) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3114.1, data_12_3114.2]

/-- Complete interval computation for depth 12, residue 3115. -/
theorem bounds_12_3115 : exactInterval 12 3115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3115 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3115) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3115 : oddCount 3115 12 = 5 ∧ acceleratedOrbit 12 3115 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3115 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3115) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3115.1, data_12_3115.2]

/-- Complete interval computation for depth 12, residue 3116. -/
theorem bounds_12_3116 : exactInterval 12 3116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3116 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3116) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3116 : oddCount 3116 12 = 6 ∧ acceleratedOrbit 12 3116 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3116 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3116) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3116.1, data_12_3116.2]

/-- Complete interval computation for depth 12, residue 3117. -/
theorem bounds_12_3117 : exactInterval 12 3117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3117 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3117) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3117 : oddCount 3117 12 = 6 ∧ acceleratedOrbit 12 3117 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3117 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3117) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3117.1, data_12_3117.2]

end Collatz.Research.StoppingAtlas.Batch0403
