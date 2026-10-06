import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch039

/-- Complete interval computation for depth 8, residue 134. -/
theorem bounds_8_134 : exactInterval 8 134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_134 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 134) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_134 : oddCount 134 8 = 4 ∧ acceleratedOrbit 8 134 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_134 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 134) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_134.1, data_8_134.2]

/-- Complete interval computation for depth 8, residue 135. -/
theorem bounds_8_135 : exactInterval 8 135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_135 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 135) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_135 : oddCount 135 8 = 4 ∧ acceleratedOrbit 8 135 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_135 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 135) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_135.1, data_8_135.2]

/-- Complete interval computation for depth 8, residue 136. -/
theorem bounds_8_136 : exactInterval 8 136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_136 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 136) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_136 : oddCount 136 8 = 2 ∧ acceleratedOrbit 8 136 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_136 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 136) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_136.1, data_8_136.2]

/-- Complete interval computation for depth 8, residue 137. -/
theorem bounds_8_137 : exactInterval 8 137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_137 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 137) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_137 : oddCount 137 8 = 6 ∧ acceleratedOrbit 8 137 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_137 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 137) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_137.1, data_8_137.2]

/-- Complete interval computation for depth 8, residue 138. -/
theorem bounds_8_138 : exactInterval 8 138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_138 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 138) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_138 : oddCount 138 8 = 2 ∧ acceleratedOrbit 8 138 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_138 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 138) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_138.1, data_8_138.2]

/-- Complete interval computation for depth 8, residue 139. -/
theorem bounds_8_139 : exactInterval 8 139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_139 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 139) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_139 : oddCount 139 8 = 5 ∧ acceleratedOrbit 8 139 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_139 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 139) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_139.1, data_8_139.2]

/-- Complete interval computation for depth 8, residue 140. -/
theorem bounds_8_140 : exactInterval 8 140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_140 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 140) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_140 : oddCount 140 8 = 2 ∧ acceleratedOrbit 8 140 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_140 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 140) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_140.1, data_8_140.2]

/-- Complete interval computation for depth 8, residue 141. -/
theorem bounds_8_141 : exactInterval 8 141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_141 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 141) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_141 : oddCount 141 8 = 2 ∧ acceleratedOrbit 8 141 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_141 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 141) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_141.1, data_8_141.2]

/-- Complete interval computation for depth 8, residue 142. -/
theorem bounds_8_142 : exactInterval 8 142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_142 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 142) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_142 : oddCount 142 8 = 5 ∧ acceleratedOrbit 8 142 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_142 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 142) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_142.1, data_8_142.2]

/-- Complete interval computation for depth 8, residue 143. -/
theorem bounds_8_143 : exactInterval 8 143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_143 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 143) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_143 : oddCount 143 8 = 5 ∧ acceleratedOrbit 8 143 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_143 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 143) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_143.1, data_8_143.2]

end Collatz.Research.DescentIntervals.Batch039
