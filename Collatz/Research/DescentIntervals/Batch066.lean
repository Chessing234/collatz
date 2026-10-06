import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch066

/-- Complete interval computation for depth 9, residue 154. -/
theorem bounds_9_154 : exactInterval 9 154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_154 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 154) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_154 : oddCount 154 9 = 4 ∧ acceleratedOrbit 9 154 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_154 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 154) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_154.1, data_9_154.2]

/-- Complete interval computation for depth 9, residue 155. -/
theorem bounds_9_155 : exactInterval 9 155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_155 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 155) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_155 : oddCount 155 9 = 7 ∧ acceleratedOrbit 9 155 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_155 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 155) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_155.1, data_9_155.2]

/-- Complete interval computation for depth 9, residue 156. -/
theorem bounds_9_156 : exactInterval 9 156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_156 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 156) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_156 : oddCount 156 9 = 5 ∧ acceleratedOrbit 9 156 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_156 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 156) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_156.1, data_9_156.2]

/-- Complete interval computation for depth 9, residue 157. -/
theorem bounds_9_157 : exactInterval 9 157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_157 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 157) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_157 : oddCount 157 9 = 5 ∧ acceleratedOrbit 9 157 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_157 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 157) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_157.1, data_9_157.2]

/-- Complete interval computation for depth 9, residue 158. -/
theorem bounds_9_158 : exactInterval 9 158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_158 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 158) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_158 : oddCount 158 9 = 5 ∧ acceleratedOrbit 9 158 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_158 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 158) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_158.1, data_9_158.2]

/-- Complete interval computation for depth 9, residue 159. -/
theorem bounds_9_159 : exactInterval 9 159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_159 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 159) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_159 : oddCount 159 9 = 8 ∧ acceleratedOrbit 9 159 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_159 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 159) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_159.1, data_9_159.2]

/-- Complete interval computation for depth 9, residue 160. -/
theorem bounds_9_160 : exactInterval 9 160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_160 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 160) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_160 : oddCount 160 9 = 1 ∧ acceleratedOrbit 9 160 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_160 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 160) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_160.1, data_9_160.2]

/-- Complete interval computation for depth 9, residue 161. -/
theorem bounds_9_161 : exactInterval 9 161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_161 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 161) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_161 : oddCount 161 9 = 6 ∧ acceleratedOrbit 9 161 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_161 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 161) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_161.1, data_9_161.2]

/-- Complete interval computation for depth 9, residue 162. -/
theorem bounds_9_162 : exactInterval 9 162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_162 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 162) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_162 : oddCount 162 9 = 5 ∧ acceleratedOrbit 9 162 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_162 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 162) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_162.1, data_9_162.2]

/-- Complete interval computation for depth 9, residue 163. -/
theorem bounds_9_163 : exactInterval 9 163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_163 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 163) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_163 : oddCount 163 9 = 5 ∧ acceleratedOrbit 9 163 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_163 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 163) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_163.1, data_9_163.2]

end Collatz.Research.DescentIntervals.Batch066
