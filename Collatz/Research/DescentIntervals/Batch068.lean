import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch068

/-- Complete interval computation for depth 9, residue 174. -/
theorem bounds_9_174 : exactInterval 9 174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_174 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 174) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_174 : oddCount 174 9 = 4 ∧ acceleratedOrbit 9 174 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_174 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 174) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_174.1, data_9_174.2]

/-- Complete interval computation for depth 9, residue 175. -/
theorem bounds_9_175 : exactInterval 9 175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_175 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 175) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_175 : oddCount 175 9 = 6 ∧ acceleratedOrbit 9 175 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_175 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 175) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_175.1, data_9_175.2]

/-- Complete interval computation for depth 9, residue 176. -/
theorem bounds_9_176 : exactInterval 9 176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_176 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 176) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_176 : oddCount 176 9 = 3 ∧ acceleratedOrbit 9 176 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_176 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 176) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_176.1, data_9_176.2]

/-- Complete interval computation for depth 9, residue 177. -/
theorem bounds_9_177 : exactInterval 9 177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_177 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 177) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_177 : oddCount 177 9 = 4 ∧ acceleratedOrbit 9 177 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_177 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 177) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_177.1, data_9_177.2]

/-- Complete interval computation for depth 9, residue 178. -/
theorem bounds_9_178 : exactInterval 9 178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_178 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 178) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_178 : oddCount 178 9 = 4 ∧ acceleratedOrbit 9 178 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_178 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 178) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_178.1, data_9_178.2]

/-- Complete interval computation for depth 9, residue 179. -/
theorem bounds_9_179 : exactInterval 9 179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_179 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 179) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_179 : oddCount 179 9 = 4 ∧ acceleratedOrbit 9 179 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_179 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 179) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_179.1, data_9_179.2]

/-- Complete interval computation for depth 9, residue 180. -/
theorem bounds_9_180 : exactInterval 9 180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_180 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 180) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_180 : oddCount 180 9 = 3 ∧ acceleratedOrbit 9 180 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_180 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 180) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_180.1, data_9_180.2]

/-- Complete interval computation for depth 9, residue 181. -/
theorem bounds_9_181 : exactInterval 9 181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_181 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 181) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_181 : oddCount 181 9 = 3 ∧ acceleratedOrbit 9 181 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_181 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 181) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_181.1, data_9_181.2]

/-- Complete interval computation for depth 9, residue 182. -/
theorem bounds_9_182 : exactInterval 9 182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_182 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 182) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_182 : oddCount 182 9 = 6 ∧ acceleratedOrbit 9 182 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_182 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 182) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_182.1, data_9_182.2]

/-- Complete interval computation for depth 9, residue 183. -/
theorem bounds_9_183 : exactInterval 9 183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_183 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 183) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_183 : oddCount 183 9 = 6 ∧ acceleratedOrbit 9 183 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_183 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 183) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_183.1, data_9_183.2]

end Collatz.Research.DescentIntervals.Batch068
