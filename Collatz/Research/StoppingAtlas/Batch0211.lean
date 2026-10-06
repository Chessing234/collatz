import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0211

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 153. -/
theorem bounds_12_153 : exactInterval 12 153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_153 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 153) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_153 : oddCount 153 12 = 6 ∧ acceleratedOrbit 12 153 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_153 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 153) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_153.1, data_12_153.2]

/-- Complete interval computation for depth 12, residue 154. -/
theorem bounds_12_154 : exactInterval 12 154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_154 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 154) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_154 : oddCount 154 12 = 5 ∧ acceleratedOrbit 12 154 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_154 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 154) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_154.1, data_12_154.2]

/-- Complete interval computation for depth 12, residue 155. -/
theorem bounds_12_155 : exactInterval 12 155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_155 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 155) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_155 : oddCount 155 12 = 8 ∧ acceleratedOrbit 12 155 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_155 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 155) = 3 ^ 8 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_155.1, data_12_155.2]

/-- Complete interval computation for depth 12, residue 156. -/
theorem bounds_12_156 : exactInterval 12 156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_156 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 156) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_156 : oddCount 156 12 = 6 ∧ acceleratedOrbit 12 156 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_156 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 156) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_156.1, data_12_156.2]

/-- Complete interval computation for depth 12, residue 157. -/
theorem bounds_12_157 : exactInterval 12 157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_157 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 157) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_157 : oddCount 157 12 = 6 ∧ acceleratedOrbit 12 157 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_157 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 157) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_157.1, data_12_157.2]

/-- Complete interval computation for depth 12, residue 158. -/
theorem bounds_12_158 : exactInterval 12 158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_158 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 158) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_158 : oddCount 158 12 = 6 ∧ acceleratedOrbit 12 158 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_158 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 158) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_158.1, data_12_158.2]

/-- Complete interval computation for depth 12, residue 159. -/
theorem bounds_12_159 : exactInterval 12 159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_159 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 159) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_159 : oddCount 159 12 = 10 ∧ acceleratedOrbit 12 159 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_159 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 159) = 3 ^ 10 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_159.1, data_12_159.2]

/-- Complete interval computation for depth 12, residue 160. -/
theorem bounds_12_160 : exactInterval 12 160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_160 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 160) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_160 : oddCount 160 12 = 3 ∧ acceleratedOrbit 12 160 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_160 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 160) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_160.1, data_12_160.2]

/-- Complete interval computation for depth 12, residue 161. -/
theorem bounds_12_161 : exactInterval 12 161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_161 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 161) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_161 : oddCount 161 12 = 8 ∧ acceleratedOrbit 12 161 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_161 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 161) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_161.1, data_12_161.2]

/-- Complete interval computation for depth 12, residue 162. -/
theorem bounds_12_162 : exactInterval 12 162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_162 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 162) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_162 : oddCount 162 12 = 5 ∧ acceleratedOrbit 12 162 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_162 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 162) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_162.1, data_12_162.2]

/-- Complete interval computation for depth 12, residue 163. -/
theorem bounds_12_163 : exactInterval 12 163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_163 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 163) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_163 : oddCount 163 12 = 5 ∧ acceleratedOrbit 12 163 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_163 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 163) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_163.1, data_12_163.2]

/-- Complete interval computation for depth 12, residue 164. -/
theorem bounds_12_164 : exactInterval 12 164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_164 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 164) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_164 : oddCount 164 12 = 7 ∧ acceleratedOrbit 12 164 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_164 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 164) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_164.1, data_12_164.2]

/-- Complete interval computation for depth 12, residue 165. -/
theorem bounds_12_165 : exactInterval 12 165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_165 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 165) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_165 : oddCount 165 12 = 7 ∧ acceleratedOrbit 12 165 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_165 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 165) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_165.1, data_12_165.2]

/-- Complete interval computation for depth 12, residue 166. -/
theorem bounds_12_166 : exactInterval 12 166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_166 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 166) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_166 : oddCount 166 12 = 7 ∧ acceleratedOrbit 12 166 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_166 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 166) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_166.1, data_12_166.2]

/-- Complete interval computation for depth 12, residue 167. -/
theorem bounds_12_167 : exactInterval 12 167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_167 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 167) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_167 : oddCount 167 12 = 10 ∧ acceleratedOrbit 12 167 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_167 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 167) = 3 ^ 10 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_167.1, data_12_167.2]

end Collatz.Research.StoppingAtlas.Batch0211
