import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0011

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 153. -/
theorem bounds_10_153 : exactInterval 10 153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_153 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 153) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_153 : oddCount 153 10 = 5 ∧ acceleratedOrbit 10 153 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_153 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 153) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_153.1, data_10_153.2]

/-- Complete interval computation for depth 10, residue 154. -/
theorem bounds_10_154 : exactInterval 10 154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_154 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 154) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_154 : oddCount 154 10 = 4 ∧ acceleratedOrbit 10 154 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_154 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 154) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_154.1, data_10_154.2]

/-- Complete interval computation for depth 10, residue 155. -/
theorem bounds_10_155 : exactInterval 10 155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_155 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 155) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_155 : oddCount 155 10 = 7 ∧ acceleratedOrbit 10 155 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_155 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 155) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_155.1, data_10_155.2]

/-- Complete interval computation for depth 10, residue 156. -/
theorem bounds_10_156 : exactInterval 10 156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_156 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 156) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_156 : oddCount 156 10 = 5 ∧ acceleratedOrbit 10 156 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_156 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 156) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_156.1, data_10_156.2]

/-- Complete interval computation for depth 10, residue 157. -/
theorem bounds_10_157 : exactInterval 10 157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_157 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 157) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_157 : oddCount 157 10 = 5 ∧ acceleratedOrbit 10 157 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_157 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 157) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_157.1, data_10_157.2]

/-- Complete interval computation for depth 10, residue 158. -/
theorem bounds_10_158 : exactInterval 10 158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_158 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 158) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_158 : oddCount 158 10 = 5 ∧ acceleratedOrbit 10 158 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_158 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 158) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_158.1, data_10_158.2]

/-- Complete interval computation for depth 10, residue 159. -/
theorem bounds_10_159 : exactInterval 10 159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_159 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 159) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_159 : oddCount 159 10 = 9 ∧ acceleratedOrbit 10 159 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_159 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 159) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_159.1, data_10_159.2]

/-- Complete interval computation for depth 10, residue 160. -/
theorem bounds_10_160 : exactInterval 10 160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_160 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 160) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_160 : oddCount 160 10 = 2 ∧ acceleratedOrbit 10 160 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_160 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 160) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_160.1, data_10_160.2]

/-- Complete interval computation for depth 10, residue 161. -/
theorem bounds_10_161 : exactInterval 10 161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_161 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 161) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_161 : oddCount 161 10 = 7 ∧ acceleratedOrbit 10 161 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_161 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 161) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_161.1, data_10_161.2]

/-- Complete interval computation for depth 10, residue 162. -/
theorem bounds_10_162 : exactInterval 10 162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_162 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 162) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_162 : oddCount 162 10 = 5 ∧ acceleratedOrbit 10 162 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_162 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 162) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_162.1, data_10_162.2]

/-- Complete interval computation for depth 10, residue 163. -/
theorem bounds_10_163 : exactInterval 10 163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_163 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 163) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_163 : oddCount 163 10 = 5 ∧ acceleratedOrbit 10 163 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_163 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 163) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_163.1, data_10_163.2]

/-- Complete interval computation for depth 10, residue 164. -/
theorem bounds_10_164 : exactInterval 10 164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_164 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 164) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_164 : oddCount 164 10 = 6 ∧ acceleratedOrbit 10 164 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_164 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 164) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_164.1, data_10_164.2]

/-- Complete interval computation for depth 10, residue 165. -/
theorem bounds_10_165 : exactInterval 10 165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_165 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 165) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_165 : oddCount 165 10 = 6 ∧ acceleratedOrbit 10 165 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_165 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 165) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_165.1, data_10_165.2]

/-- Complete interval computation for depth 10, residue 166. -/
theorem bounds_10_166 : exactInterval 10 166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_166 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 166) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_166 : oddCount 166 10 = 6 ∧ acceleratedOrbit 10 166 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_166 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 166) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_166.1, data_10_166.2]

/-- Complete interval computation for depth 10, residue 167. -/
theorem bounds_10_167 : exactInterval 10 167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_167 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 167) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_167 : oddCount 167 10 = 8 ∧ acceleratedOrbit 10 167 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_167 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 167) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_167.1, data_10_167.2]

end Collatz.Research.StoppingAtlas.Batch0011
