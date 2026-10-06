import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch067

/-- Complete interval computation for depth 9, residue 164. -/
theorem bounds_9_164 : exactInterval 9 164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_164 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 164) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_164 : oddCount 164 9 = 6 ∧ acceleratedOrbit 9 164 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_164 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 164) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_164.1, data_9_164.2]

/-- Complete interval computation for depth 9, residue 165. -/
theorem bounds_9_165 : exactInterval 9 165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_165 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 165) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_165 : oddCount 165 9 = 6 ∧ acceleratedOrbit 9 165 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_165 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 165) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_165.1, data_9_165.2]

/-- Complete interval computation for depth 9, residue 166. -/
theorem bounds_9_166 : exactInterval 9 166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_166 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 166) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_166 : oddCount 166 9 = 6 ∧ acceleratedOrbit 9 166 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_166 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 166) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_166.1, data_9_166.2]

/-- Complete interval computation for depth 9, residue 167. -/
theorem bounds_9_167 : exactInterval 9 167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_167 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 167) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_167 : oddCount 167 9 = 7 ∧ acceleratedOrbit 9 167 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_167 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 167) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_167.1, data_9_167.2]

/-- Complete interval computation for depth 9, residue 168. -/
theorem bounds_9_168 : exactInterval 9 168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_168 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 168) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_168 : oddCount 168 9 = 1 ∧ acceleratedOrbit 9 168 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_168 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 168) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_168.1, data_9_168.2]

/-- Complete interval computation for depth 9, residue 169. -/
theorem bounds_9_169 : exactInterval 9 169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_169 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 169) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_169 : oddCount 169 9 = 8 ∧ acceleratedOrbit 9 169 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_169 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 169) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_169.1, data_9_169.2]

/-- Complete interval computation for depth 9, residue 170. -/
theorem bounds_9_170 : exactInterval 9 170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_170 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 170) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_170 : oddCount 170 9 = 1 ∧ acceleratedOrbit 9 170 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_170 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 170) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_170.1, data_9_170.2]

/-- Complete interval computation for depth 9, residue 171. -/
theorem bounds_9_171 : exactInterval 9 171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_171 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 171) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_171 : oddCount 171 9 = 5 ∧ acceleratedOrbit 9 171 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_171 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 171) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_171.1, data_9_171.2]

/-- Complete interval computation for depth 9, residue 172. -/
theorem bounds_9_172 : exactInterval 9 172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_172 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 172) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_172 : oddCount 172 9 = 4 ∧ acceleratedOrbit 9 172 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_172 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 172) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_172.1, data_9_172.2]

/-- Complete interval computation for depth 9, residue 173. -/
theorem bounds_9_173 : exactInterval 9 173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_173 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 173) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_173 : oddCount 173 9 = 4 ∧ acceleratedOrbit 9 173 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_173 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 173) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_173.1, data_9_173.2]

end Collatz.Research.DescentIntervals.Batch067
