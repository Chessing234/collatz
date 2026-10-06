import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0478

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 158. -/
theorem bounds_13_158 : exactInterval 13 158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_158 : oddCount 158 13 = 7 ∧ acceleratedOrbit 13 158 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 158) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_158.1, data_13_158.2]

/-- Complete interval computation for depth 13, residue 159. -/
theorem bounds_13_159 : exactInterval 13 159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 159) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_159 : oddCount 159 13 = 10 ∧ acceleratedOrbit 13 159 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 159) = 3 ^ 10 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_159.1, data_13_159.2]

/-- Complete interval computation for depth 13, residue 160. -/
theorem bounds_13_160 : exactInterval 13 160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_160 : oddCount 160 13 = 3 ∧ acceleratedOrbit 13 160 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 160) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_160.1, data_13_160.2]

/-- Complete interval computation for depth 13, residue 161. -/
theorem bounds_13_161 : exactInterval 13 161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_161 : oddCount 161 13 = 9 ∧ acceleratedOrbit 13 161 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 161) = 3 ^ 9 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_161.1, data_13_161.2]

/-- Complete interval computation for depth 13, residue 162. -/
theorem bounds_13_162 : exactInterval 13 162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_162 : oddCount 162 13 = 5 ∧ acceleratedOrbit 13 162 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 162) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_162.1, data_13_162.2]

/-- Complete interval computation for depth 13, residue 163. -/
theorem bounds_13_163 : exactInterval 13 163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_163 : oddCount 163 13 = 5 ∧ acceleratedOrbit 13 163 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 163) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_163.1, data_13_163.2]

/-- Complete interval computation for depth 13, residue 164. -/
theorem bounds_13_164 : exactInterval 13 164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_164 : oddCount 164 13 = 8 ∧ acceleratedOrbit 13 164 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 164) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_164.1, data_13_164.2]

/-- Complete interval computation for depth 13, residue 165. -/
theorem bounds_13_165 : exactInterval 13 165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_165 : oddCount 165 13 = 8 ∧ acceleratedOrbit 13 165 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 165) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_165.1, data_13_165.2]

/-- Complete interval computation for depth 13, residue 166. -/
theorem bounds_13_166 : exactInterval 13 166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_166 : oddCount 166 13 = 8 ∧ acceleratedOrbit 13 166 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 166) = 3 ^ 8 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_166.1, data_13_166.2]

/-- Complete interval computation for depth 13, residue 167. -/
theorem bounds_13_167 : exactInterval 13 167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_167 : oddCount 167 13 = 11 ∧ acceleratedOrbit 13 167 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 167) = 3 ^ 11 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_167.1, data_13_167.2]

/-- Complete interval computation for depth 13, residue 168. -/
theorem bounds_13_168 : exactInterval 13 168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_168 : oddCount 168 13 = 3 ∧ acceleratedOrbit 13 168 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 168) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_168.1, data_13_168.2]

/-- Complete interval computation for depth 13, residue 169. -/
theorem bounds_13_169 : exactInterval 13 169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_169 : oddCount 169 13 = 9 ∧ acceleratedOrbit 13 169 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 169) = 3 ^ 9 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_169.1, data_13_169.2]

/-- Complete interval computation for depth 13, residue 170. -/
theorem bounds_13_170 : exactInterval 13 170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_170 : oddCount 170 13 = 3 ∧ acceleratedOrbit 13 170 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 170) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_170.1, data_13_170.2]

/-- Complete interval computation for depth 13, residue 171. -/
theorem bounds_13_171 : exactInterval 13 171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_171 : oddCount 171 13 = 7 ∧ acceleratedOrbit 13 171 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 171) = 3 ^ 7 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_171.1, data_13_171.2]

/-- Complete interval computation for depth 13, residue 172. -/
theorem bounds_13_172 : exactInterval 13 172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_172 : oddCount 172 13 = 6 ∧ acceleratedOrbit 13 172 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 172) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_172.1, data_13_172.2]

/-- Complete interval computation for depth 13, residue 173. -/
theorem bounds_13_173 : exactInterval 13 173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_173 : oddCount 173 13 = 6 ∧ acceleratedOrbit 13 173 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 173) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_173.1, data_13_173.2]

end Collatz.Research.StoppingAtlas.Batch0478
