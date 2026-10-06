import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch038

/-- Complete interval computation for depth 8, residue 124. -/
theorem bounds_8_124 : exactInterval 8 124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_124 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 124) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_124 : oddCount 124 8 = 5 ∧ acceleratedOrbit 8 124 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_124 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 124) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_124.1, data_8_124.2]

/-- Complete interval computation for depth 8, residue 125. -/
theorem bounds_8_125 : exactInterval 8 125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_125 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 125) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_125 : oddCount 125 8 = 5 ∧ acceleratedOrbit 8 125 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_125 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 125) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_125.1, data_8_125.2]

/-- Complete interval computation for depth 8, residue 126. -/
theorem bounds_8_126 : exactInterval 8 126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_126 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 126) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_126 : oddCount 126 8 = 6 ∧ acceleratedOrbit 8 126 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_126 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 126) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_126.1, data_8_126.2]

/-- Complete interval computation for depth 8, residue 127. -/
theorem bounds_8_127 : exactInterval 8 127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_127 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 127) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_127 : oddCount 127 8 = 7 ∧ acceleratedOrbit 8 127 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_127 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 127) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_127.1, data_8_127.2]

/-- Complete interval computation for depth 8, residue 128. -/
theorem bounds_8_128 : exactInterval 8 128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_128 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 128) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_128 : oddCount 128 8 = 1 ∧ acceleratedOrbit 8 128 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_128 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 128) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_128.1, data_8_128.2]

/-- Complete interval computation for depth 8, residue 129. -/
theorem bounds_8_129 : exactInterval 8 129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_129 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 129) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_129 : oddCount 129 8 = 5 ∧ acceleratedOrbit 8 129 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_129 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 129) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_129.1, data_8_129.2]

/-- Complete interval computation for depth 8, residue 130. -/
theorem bounds_8_130 : exactInterval 8 130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_130 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 130) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_130 : oddCount 130 8 = 3 ∧ acceleratedOrbit 8 130 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_130 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 130) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_130.1, data_8_130.2]

/-- Complete interval computation for depth 8, residue 131. -/
theorem bounds_8_131 : exactInterval 8 131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_131 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 131) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_131 : oddCount 131 8 = 3 ∧ acceleratedOrbit 8 131 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_131 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 131) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_131.1, data_8_131.2]

/-- Complete interval computation for depth 8, residue 132. -/
theorem bounds_8_132 : exactInterval 8 132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_132 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 132) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_132 : oddCount 132 8 = 4 ∧ acceleratedOrbit 8 132 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_132 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 132) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_132.1, data_8_132.2]

/-- Complete interval computation for depth 8, residue 133. -/
theorem bounds_8_133 : exactInterval 8 133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_133 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 133) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_133 : oddCount 133 8 = 4 ∧ acceleratedOrbit 8 133 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_133 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 133) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_133.1, data_8_133.2]

end Collatz.Research.DescentIntervals.Batch038
