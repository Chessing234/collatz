import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch042

/-- Complete interval computation for depth 8, residue 165. -/
theorem bounds_8_165 : exactInterval 8 165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_165 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 165) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_165 : oddCount 165 8 = 5 ∧ acceleratedOrbit 8 165 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_165 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 165) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_165.1, data_8_165.2]

/-- Complete interval computation for depth 8, residue 166. -/
theorem bounds_8_166 : exactInterval 8 166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_166 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 166) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_166 : oddCount 166 8 = 5 ∧ acceleratedOrbit 8 166 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_166 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 166) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_166.1, data_8_166.2]

/-- Complete interval computation for depth 8, residue 167. -/
theorem bounds_8_167 : exactInterval 8 167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_167 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 167) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_167 : oddCount 167 8 = 6 ∧ acceleratedOrbit 8 167 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_167 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 167) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_167.1, data_8_167.2]

/-- Complete interval computation for depth 8, residue 168. -/
theorem bounds_8_168 : exactInterval 8 168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_168 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 168) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_168 : oddCount 168 8 = 1 ∧ acceleratedOrbit 8 168 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_168 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 168) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_168.1, data_8_168.2]

/-- Complete interval computation for depth 8, residue 169. -/
theorem bounds_8_169 : exactInterval 8 169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_169 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 169) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_169 : oddCount 169 8 = 7 ∧ acceleratedOrbit 8 169 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_169 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 169) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_169.1, data_8_169.2]

/-- Complete interval computation for depth 8, residue 170. -/
theorem bounds_8_170 : exactInterval 8 170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_170 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 170) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_170 : oddCount 170 8 = 1 ∧ acceleratedOrbit 8 170 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_170 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 170) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_170.1, data_8_170.2]

/-- Complete interval computation for depth 8, residue 171. -/
theorem bounds_8_171 : exactInterval 8 171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_171 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 171) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_171 : oddCount 171 8 = 5 ∧ acceleratedOrbit 8 171 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_171 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 171) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_171.1, data_8_171.2]

/-- Complete interval computation for depth 8, residue 172. -/
theorem bounds_8_172 : exactInterval 8 172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_172 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 172) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_172 : oddCount 172 8 = 4 ∧ acceleratedOrbit 8 172 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_172 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 172) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_172.1, data_8_172.2]

/-- Complete interval computation for depth 8, residue 173. -/
theorem bounds_8_173 : exactInterval 8 173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_173 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 173) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_173 : oddCount 173 8 = 4 ∧ acceleratedOrbit 8 173 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_173 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 173) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_173.1, data_8_173.2]

/-- Complete interval computation for depth 8, residue 174. -/
theorem bounds_8_174 : exactInterval 8 174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_174 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 174) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_174 : oddCount 174 8 = 4 ∧ acceleratedOrbit 8 174 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_174 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 174) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_174.1, data_8_174.2]

end Collatz.Research.DescentIntervals.Batch042
