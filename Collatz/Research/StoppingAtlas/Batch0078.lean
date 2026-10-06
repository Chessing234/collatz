import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0078

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 158. -/
theorem bounds_11_158 : exactInterval 11 158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_158 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 158) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_158 : oddCount 158 11 = 5 ∧ acceleratedOrbit 11 158 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_158 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 158) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_158.1, data_11_158.2]

/-- Complete interval computation for depth 11, residue 159. -/
theorem bounds_11_159 : exactInterval 11 159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_159 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 159) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_159 : oddCount 159 11 = 10 ∧ acceleratedOrbit 11 159 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_159 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 159) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_159.1, data_11_159.2]

/-- Complete interval computation for depth 11, residue 160. -/
theorem bounds_11_160 : exactInterval 11 160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_160 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 160) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_160 : oddCount 160 11 = 2 ∧ acceleratedOrbit 11 160 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_160 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 160) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_160.1, data_11_160.2]

/-- Complete interval computation for depth 11, residue 161. -/
theorem bounds_11_161 : exactInterval 11 161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_161 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 161) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_161 : oddCount 161 11 = 7 ∧ acceleratedOrbit 11 161 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_161 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 161) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_161.1, data_11_161.2]

/-- Complete interval computation for depth 11, residue 162. -/
theorem bounds_11_162 : exactInterval 11 162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_162 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 162) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_162 : oddCount 162 11 = 5 ∧ acceleratedOrbit 11 162 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_162 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 162) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_162.1, data_11_162.2]

/-- Complete interval computation for depth 11, residue 163. -/
theorem bounds_11_163 : exactInterval 11 163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_163 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 163) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_163 : oddCount 163 11 = 5 ∧ acceleratedOrbit 11 163 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_163 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 163) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_163.1, data_11_163.2]

/-- Complete interval computation for depth 11, residue 164. -/
theorem bounds_11_164 : exactInterval 11 164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_164 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 164) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_164 : oddCount 164 11 = 7 ∧ acceleratedOrbit 11 164 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_164 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 164) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_164.1, data_11_164.2]

/-- Complete interval computation for depth 11, residue 165. -/
theorem bounds_11_165 : exactInterval 11 165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_165 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 165) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_165 : oddCount 165 11 = 7 ∧ acceleratedOrbit 11 165 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_165 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 165) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_165.1, data_11_165.2]

/-- Complete interval computation for depth 11, residue 166. -/
theorem bounds_11_166 : exactInterval 11 166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_166 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 166) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_166 : oddCount 166 11 = 7 ∧ acceleratedOrbit 11 166 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_166 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 166) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_166.1, data_11_166.2]

/-- Complete interval computation for depth 11, residue 167. -/
theorem bounds_11_167 : exactInterval 11 167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_167 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 167) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_167 : oddCount 167 11 = 9 ∧ acceleratedOrbit 11 167 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_167 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 167) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_167.1, data_11_167.2]

/-- Complete interval computation for depth 11, residue 168. -/
theorem bounds_11_168 : exactInterval 11 168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_168 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 168) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_168 : oddCount 168 11 = 2 ∧ acceleratedOrbit 11 168 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_168 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 168) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_168.1, data_11_168.2]

/-- Complete interval computation for depth 11, residue 169. -/
theorem bounds_11_169 : exactInterval 11 169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_169 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 169) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_169 : oddCount 169 11 = 9 ∧ acceleratedOrbit 11 169 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_169 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 169) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_169.1, data_11_169.2]

/-- Complete interval computation for depth 11, residue 170. -/
theorem bounds_11_170 : exactInterval 11 170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_170 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 170) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_170 : oddCount 170 11 = 2 ∧ acceleratedOrbit 11 170 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_170 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 170) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_170.1, data_11_170.2]

/-- Complete interval computation for depth 11, residue 171. -/
theorem bounds_11_171 : exactInterval 11 171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_171 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 171) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_171 : oddCount 171 11 = 6 ∧ acceleratedOrbit 11 171 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_171 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 171) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_171.1, data_11_171.2]

/-- Complete interval computation for depth 11, residue 172. -/
theorem bounds_11_172 : exactInterval 11 172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_172 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 172) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_172 : oddCount 172 11 = 4 ∧ acceleratedOrbit 11 172 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_172 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 172) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_172.1, data_11_172.2]

/-- Complete interval computation for depth 11, residue 173. -/
theorem bounds_11_173 : exactInterval 11 173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_173 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 173) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_173 : oddCount 173 11 = 4 ∧ acceleratedOrbit 11 173 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_173 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 173) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_173.1, data_11_173.2]

end Collatz.Research.StoppingAtlas.Batch0078
