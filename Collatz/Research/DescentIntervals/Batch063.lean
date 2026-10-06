import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch063

/-- Complete interval computation for depth 9, residue 123. -/
theorem bounds_9_123 : exactInterval 9 123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_123 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 123) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_123 : oddCount 123 9 = 5 ∧ acceleratedOrbit 9 123 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_123 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 123) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_123.1, data_9_123.2]

/-- Complete interval computation for depth 9, residue 124. -/
theorem bounds_9_124 : exactInterval 9 124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_124 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 124) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_124 : oddCount 124 9 = 6 ∧ acceleratedOrbit 9 124 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_124 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 124) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_124.1, data_9_124.2]

/-- Complete interval computation for depth 9, residue 125. -/
theorem bounds_9_125 : exactInterval 9 125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_125 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 125) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_125 : oddCount 125 9 = 6 ∧ acceleratedOrbit 9 125 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_125 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 125) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_125.1, data_9_125.2]

/-- Complete interval computation for depth 9, residue 126. -/
theorem bounds_9_126 : exactInterval 9 126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_126 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 126) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_126 : oddCount 126 9 = 6 ∧ acceleratedOrbit 9 126 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_126 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 126) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_126.1, data_9_126.2]

/-- Complete interval computation for depth 9, residue 127. -/
theorem bounds_9_127 : exactInterval 9 127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_127 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 127) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_127 : oddCount 127 9 = 8 ∧ acceleratedOrbit 9 127 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_127 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 127) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_127.1, data_9_127.2]

/-- Complete interval computation for depth 9, residue 128. -/
theorem bounds_9_128 : exactInterval 9 128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_128 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 128) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_128 : oddCount 128 9 = 1 ∧ acceleratedOrbit 9 128 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_128 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 128) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_128.1, data_9_128.2]

/-- Complete interval computation for depth 9, residue 129. -/
theorem bounds_9_129 : exactInterval 9 129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_129 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 129) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_129 : oddCount 129 9 = 6 ∧ acceleratedOrbit 9 129 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_129 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 129) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_129.1, data_9_129.2]

/-- Complete interval computation for depth 9, residue 130. -/
theorem bounds_9_130 : exactInterval 9 130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_130 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 130) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_130 : oddCount 130 9 = 3 ∧ acceleratedOrbit 9 130 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_130 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 130) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_130.1, data_9_130.2]

/-- Complete interval computation for depth 9, residue 131. -/
theorem bounds_9_131 : exactInterval 9 131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_131 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 131) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_131 : oddCount 131 9 = 3 ∧ acceleratedOrbit 9 131 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_131 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 131) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_131.1, data_9_131.2]

/-- Complete interval computation for depth 9, residue 132. -/
theorem bounds_9_132 : exactInterval 9 132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_132 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 132) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_132 : oddCount 132 9 = 4 ∧ acceleratedOrbit 9 132 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_132 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 132) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_132.1, data_9_132.2]

end Collatz.Research.DescentIntervals.Batch063
