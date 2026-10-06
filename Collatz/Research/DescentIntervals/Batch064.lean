import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch064

/-- Complete interval computation for depth 9, residue 133. -/
theorem bounds_9_133 : exactInterval 9 133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_133 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 133) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_133 : oddCount 133 9 = 4 ∧ acceleratedOrbit 9 133 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_133 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 133) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_133.1, data_9_133.2]

/-- Complete interval computation for depth 9, residue 134. -/
theorem bounds_9_134 : exactInterval 9 134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_134 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 134) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_134 : oddCount 134 9 = 4 ∧ acceleratedOrbit 9 134 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_134 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 134) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_134.1, data_9_134.2]

/-- Complete interval computation for depth 9, residue 135. -/
theorem bounds_9_135 : exactInterval 9 135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_135 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 135) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_135 : oddCount 135 9 = 5 ∧ acceleratedOrbit 9 135 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_135 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 135) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_135.1, data_9_135.2]

/-- Complete interval computation for depth 9, residue 136. -/
theorem bounds_9_136 : exactInterval 9 136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_136 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 136) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_136 : oddCount 136 9 = 3 ∧ acceleratedOrbit 9 136 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_136 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 136) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_136.1, data_9_136.2]

/-- Complete interval computation for depth 9, residue 137. -/
theorem bounds_9_137 : exactInterval 9 137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_137 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 137) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_137 : oddCount 137 9 = 7 ∧ acceleratedOrbit 9 137 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_137 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 137) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_137.1, data_9_137.2]

/-- Complete interval computation for depth 9, residue 138. -/
theorem bounds_9_138 : exactInterval 9 138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_138 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 138) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_138 : oddCount 138 9 = 3 ∧ acceleratedOrbit 9 138 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_138 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 138) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_138.1, data_9_138.2]

/-- Complete interval computation for depth 9, residue 139. -/
theorem bounds_9_139 : exactInterval 9 139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_139 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 139) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_139 : oddCount 139 9 = 5 ∧ acceleratedOrbit 9 139 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_139 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 139) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_139.1, data_9_139.2]

/-- Complete interval computation for depth 9, residue 140. -/
theorem bounds_9_140 : exactInterval 9 140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_140 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 140) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_140 : oddCount 140 9 = 3 ∧ acceleratedOrbit 9 140 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_140 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 140) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_140.1, data_9_140.2]

/-- Complete interval computation for depth 9, residue 141. -/
theorem bounds_9_141 : exactInterval 9 141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_141 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 141) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_141 : oddCount 141 9 = 3 ∧ acceleratedOrbit 9 141 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_141 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 141) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_141.1, data_9_141.2]

/-- Complete interval computation for depth 9, residue 142. -/
theorem bounds_9_142 : exactInterval 9 142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_142 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 142) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_142 : oddCount 142 9 = 6 ∧ acceleratedOrbit 9 142 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_142 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 142) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_142.1, data_9_142.2]

/-- Complete interval computation for depth 9, residue 143. -/
theorem bounds_9_143 : exactInterval 9 143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_143 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 143) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_143 : oddCount 143 9 = 6 ∧ acceleratedOrbit 9 143 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_143 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 143) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_143.1, data_9_143.2]

end Collatz.Research.DescentIntervals.Batch064
