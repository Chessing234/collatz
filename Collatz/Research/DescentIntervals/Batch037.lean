import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch037

/-- Complete interval computation for depth 8, residue 113. -/
theorem bounds_8_113 : exactInterval 8 113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_113 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 113) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_113 : oddCount 113 8 = 2 ∧ acceleratedOrbit 8 113 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_113 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 113) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_113.1, data_8_113.2]

/-- Complete interval computation for depth 8, residue 114. -/
theorem bounds_8_114 : exactInterval 8 114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_114 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 114) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_114 : oddCount 114 8 = 4 ∧ acceleratedOrbit 8 114 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_114 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 114) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_114.1, data_8_114.2]

/-- Complete interval computation for depth 8, residue 115. -/
theorem bounds_8_115 : exactInterval 8 115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_115 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 115) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_115 : oddCount 115 8 = 4 ∧ acceleratedOrbit 8 115 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_115 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 115) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_115.1, data_8_115.2]

/-- Complete interval computation for depth 8, residue 116. -/
theorem bounds_8_116 : exactInterval 8 116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_116 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 116) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_116 : oddCount 116 8 = 3 ∧ acceleratedOrbit 8 116 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_116 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 116) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_116.1, data_8_116.2]

/-- Complete interval computation for depth 8, residue 117. -/
theorem bounds_8_117 : exactInterval 8 117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_117 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 117) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_117 : oddCount 117 8 = 3 ∧ acceleratedOrbit 8 117 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_117 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 117) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_117.1, data_8_117.2]

/-- Complete interval computation for depth 8, residue 118. -/
theorem bounds_8_118 : exactInterval 8 118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_118 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 118) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_118 : oddCount 118 8 = 4 ∧ acceleratedOrbit 8 118 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_118 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 118) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_118.1, data_8_118.2]

/-- Complete interval computation for depth 8, residue 119. -/
theorem bounds_8_119 : exactInterval 8 119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_119 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 119) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_119 : oddCount 119 8 = 4 ∧ acceleratedOrbit 8 119 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_119 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 119) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_119.1, data_8_119.2]

/-- Complete interval computation for depth 8, residue 120. -/
theorem bounds_8_120 : exactInterval 8 120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_120 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 120) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_120 : oddCount 120 8 = 4 ∧ acceleratedOrbit 8 120 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_120 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 120) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_120.1, data_8_120.2]

/-- Complete interval computation for depth 8, residue 121. -/
theorem bounds_8_121 : exactInterval 8 121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_121 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 121) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_121 : oddCount 121 8 = 6 ∧ acceleratedOrbit 8 121 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_121 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 121) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_121.1, data_8_121.2]

/-- Complete interval computation for depth 8, residue 122. -/
theorem bounds_8_122 : exactInterval 8 122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_122 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 122) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_122 : oddCount 122 8 = 4 ∧ acceleratedOrbit 8 122 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_122 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 122) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_122.1, data_8_122.2]

/-- Complete interval computation for depth 8, residue 123. -/
theorem bounds_8_123 : exactInterval 8 123 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_123 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 123) 8 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_123 : oddCount 123 8 = 5 ∧ acceleratedOrbit 8 123 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_123 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 123) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_123.1, data_8_123.2]

end Collatz.Research.DescentIntervals.Batch037
