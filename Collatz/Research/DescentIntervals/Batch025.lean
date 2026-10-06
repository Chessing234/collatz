import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch025

/-- Complete interval computation for depth 7, residue 119. -/
theorem bounds_7_119 : exactInterval 7 119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_119 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 119) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_119 : oddCount 119 7 = 4 ∧ acceleratedOrbit 7 119 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_119 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 119) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_119.1, data_7_119.2]

/-- Complete interval computation for depth 7, residue 120. -/
theorem bounds_7_120 : exactInterval 7 120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_120 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 120) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_120 : oddCount 120 7 = 4 ∧ acceleratedOrbit 7 120 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_120 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 120) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_120.1, data_7_120.2]

/-- Complete interval computation for depth 7, residue 121. -/
theorem bounds_7_121 : exactInterval 7 121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_121 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 121) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_121 : oddCount 121 7 = 5 ∧ acceleratedOrbit 7 121 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_121 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 121) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_121.1, data_7_121.2]

/-- Complete interval computation for depth 7, residue 122. -/
theorem bounds_7_122 : exactInterval 7 122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_122 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 122) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_122 : oddCount 122 7 = 4 ∧ acceleratedOrbit 7 122 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_122 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 122) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_122.1, data_7_122.2]

/-- Complete interval computation for depth 7, residue 123. -/
theorem bounds_7_123 : exactInterval 7 123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_123 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 123) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_123 : oddCount 123 7 = 5 ∧ acceleratedOrbit 7 123 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_123 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 123) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_123.1, data_7_123.2]

/-- Complete interval computation for depth 7, residue 124. -/
theorem bounds_7_124 : exactInterval 7 124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_124 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 124) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_124 : oddCount 124 7 = 5 ∧ acceleratedOrbit 7 124 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_124 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 124) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_124.1, data_7_124.2]

/-- Complete interval computation for depth 7, residue 125. -/
theorem bounds_7_125 : exactInterval 7 125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_125 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 125) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_125 : oddCount 125 7 = 5 ∧ acceleratedOrbit 7 125 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_125 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 125) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_125.1, data_7_125.2]

/-- Complete interval computation for depth 7, residue 126. -/
theorem bounds_7_126 : exactInterval 7 126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_126 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 126) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_126 : oddCount 126 7 = 6 ∧ acceleratedOrbit 7 126 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_126 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 126) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_126.1, data_7_126.2]

/-- Complete interval computation for depth 7, residue 127. -/
theorem bounds_7_127 : exactInterval 7 127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_127 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 127) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_127 : oddCount 127 7 = 7 ∧ acceleratedOrbit 7 127 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_127 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 127) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_127.1, data_7_127.2]

/-- Complete interval computation for depth 8, residue 0. -/
theorem bounds_8_0 : exactInterval 8 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_0 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 0) 8 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_0 : oddCount 0 8 = 0 ∧ acceleratedOrbit 8 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_0 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_0.1, data_8_0.2]

end Collatz.Research.DescentIntervals.Batch025
