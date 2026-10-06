import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch062

/-- Complete interval computation for depth 9, residue 113. -/
theorem bounds_9_113 : exactInterval 9 113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_113 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 113) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_113 : oddCount 113 9 = 2 ∧ acceleratedOrbit 9 113 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_113 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 113) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_113.1, data_9_113.2]

/-- Complete interval computation for depth 9, residue 114. -/
theorem bounds_9_114 : exactInterval 9 114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_114 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 114) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_114 : oddCount 114 9 = 5 ∧ acceleratedOrbit 9 114 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_114 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 114) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_114.1, data_9_114.2]

/-- Complete interval computation for depth 9, residue 115. -/
theorem bounds_9_115 : exactInterval 9 115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_115 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 115) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_115 : oddCount 115 9 = 5 ∧ acceleratedOrbit 9 115 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_115 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 115) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_115.1, data_9_115.2]

/-- Complete interval computation for depth 9, residue 116. -/
theorem bounds_9_116 : exactInterval 9 116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_116 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 116) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_116 : oddCount 116 9 = 4 ∧ acceleratedOrbit 9 116 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_116 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 116) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_116.1, data_9_116.2]

/-- Complete interval computation for depth 9, residue 117. -/
theorem bounds_9_117 : exactInterval 9 117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_117 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 117) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_117 : oddCount 117 9 = 4 ∧ acceleratedOrbit 9 117 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_117 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 117) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_117.1, data_9_117.2]

/-- Complete interval computation for depth 9, residue 118. -/
theorem bounds_9_118 : exactInterval 9 118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_118 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 118) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_118 : oddCount 118 9 = 4 ∧ acceleratedOrbit 9 118 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_118 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 118) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_118.1, data_9_118.2]

/-- Complete interval computation for depth 9, residue 119. -/
theorem bounds_9_119 : exactInterval 9 119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_119 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 119) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_119 : oddCount 119 9 = 4 ∧ acceleratedOrbit 9 119 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_119 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 119) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_119.1, data_9_119.2]

/-- Complete interval computation for depth 9, residue 120. -/
theorem bounds_9_120 : exactInterval 9 120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_120 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 120) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_120 : oddCount 120 9 = 4 ∧ acceleratedOrbit 9 120 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_120 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 120) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_120.1, data_9_120.2]

/-- Complete interval computation for depth 9, residue 121. -/
theorem bounds_9_121 : exactInterval 9 121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_121 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 121) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_121 : oddCount 121 9 = 6 ∧ acceleratedOrbit 9 121 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_121 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 121) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_121.1, data_9_121.2]

/-- Complete interval computation for depth 9, residue 122. -/
theorem bounds_9_122 : exactInterval 9 122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_122 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 122) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_122 : oddCount 122 9 = 4 ∧ acceleratedOrbit 9 122 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_122 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 122) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_122.1, data_9_122.2]

end Collatz.Research.DescentIntervals.Batch062
