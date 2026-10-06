import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch041

/-- Complete interval computation for depth 8, residue 154. -/
theorem bounds_8_154 : exactInterval 8 154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_154 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 154) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_154 : oddCount 154 8 = 3 ∧ acceleratedOrbit 8 154 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_154 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 154) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_154.1, data_8_154.2]

/-- Complete interval computation for depth 8, residue 155. -/
theorem bounds_8_155 : exactInterval 8 155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_155 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 155) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_155 : oddCount 155 8 = 6 ∧ acceleratedOrbit 8 155 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_155 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 155) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_155.1, data_8_155.2]

/-- Complete interval computation for depth 8, residue 156. -/
theorem bounds_8_156 : exactInterval 8 156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_156 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 156) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_156 : oddCount 156 8 = 5 ∧ acceleratedOrbit 8 156 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_156 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 156) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_156.1, data_8_156.2]

/-- Complete interval computation for depth 8, residue 157. -/
theorem bounds_8_157 : exactInterval 8 157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_157 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 157) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_157 : oddCount 157 8 = 5 ∧ acceleratedOrbit 8 157 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_157 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 157) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_157.1, data_8_157.2]

/-- Complete interval computation for depth 8, residue 158. -/
theorem bounds_8_158 : exactInterval 8 158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_158 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 158) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_158 : oddCount 158 8 = 5 ∧ acceleratedOrbit 8 158 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_158 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 158) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_158.1, data_8_158.2]

/-- Complete interval computation for depth 8, residue 159. -/
theorem bounds_8_159 : exactInterval 8 159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_159 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 159) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_159 : oddCount 159 8 = 7 ∧ acceleratedOrbit 8 159 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_159 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 159) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_159.1, data_8_159.2]

/-- Complete interval computation for depth 8, residue 160. -/
theorem bounds_8_160 : exactInterval 8 160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_160 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 160) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_160 : oddCount 160 8 = 1 ∧ acceleratedOrbit 8 160 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_160 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 160) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_160.1, data_8_160.2]

/-- Complete interval computation for depth 8, residue 161. -/
theorem bounds_8_161 : exactInterval 8 161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_161 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 161) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_161 : oddCount 161 8 = 5 ∧ acceleratedOrbit 8 161 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_161 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 161) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_161.1, data_8_161.2]

/-- Complete interval computation for depth 8, residue 162. -/
theorem bounds_8_162 : exactInterval 8 162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_162 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 162) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_162 : oddCount 162 8 = 4 ∧ acceleratedOrbit 8 162 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_162 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 162) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_162.1, data_8_162.2]

/-- Complete interval computation for depth 8, residue 163. -/
theorem bounds_8_163 : exactInterval 8 163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_163 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 163) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_163 : oddCount 163 8 = 4 ∧ acceleratedOrbit 8 163 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_163 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 163) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_163.1, data_8_163.2]

/-- Complete interval computation for depth 8, residue 164. -/
theorem bounds_8_164 : exactInterval 8 164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_164 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 164) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_164 : oddCount 164 8 = 5 ∧ acceleratedOrbit 8 164 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_164 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 164) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_164.1, data_8_164.2]

end Collatz.Research.DescentIntervals.Batch041
