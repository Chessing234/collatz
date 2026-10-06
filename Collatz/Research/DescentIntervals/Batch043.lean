import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch043

/-- Complete interval computation for depth 8, residue 175. -/
theorem bounds_8_175 : exactInterval 8 175 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_175 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 175) 8 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_175 : oddCount 175 8 = 5 ∧ acceleratedOrbit 8 175 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_175 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 175) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_175.1, data_8_175.2]

/-- Complete interval computation for depth 8, residue 176. -/
theorem bounds_8_176 : exactInterval 8 176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_176 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 176) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_176 : oddCount 176 8 = 3 ∧ acceleratedOrbit 8 176 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_176 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 176) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_176.1, data_8_176.2]

/-- Complete interval computation for depth 8, residue 177. -/
theorem bounds_8_177 : exactInterval 8 177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_177 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 177) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_177 : oddCount 177 8 = 3 ∧ acceleratedOrbit 8 177 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_177 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 177) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_177.1, data_8_177.2]

/-- Complete interval computation for depth 8, residue 178. -/
theorem bounds_8_178 : exactInterval 8 178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_178 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 178) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_178 : oddCount 178 8 = 3 ∧ acceleratedOrbit 8 178 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_178 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 178) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_178.1, data_8_178.2]

/-- Complete interval computation for depth 8, residue 179. -/
theorem bounds_8_179 : exactInterval 8 179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_179 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 179) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_179 : oddCount 179 8 = 3 ∧ acceleratedOrbit 8 179 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_179 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 179) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_179.1, data_8_179.2]

/-- Complete interval computation for depth 8, residue 180. -/
theorem bounds_8_180 : exactInterval 8 180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_180 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 180) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_180 : oddCount 180 8 = 3 ∧ acceleratedOrbit 8 180 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_180 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 180) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_180.1, data_8_180.2]

/-- Complete interval computation for depth 8, residue 181. -/
theorem bounds_8_181 : exactInterval 8 181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_181 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 181) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_181 : oddCount 181 8 = 3 ∧ acceleratedOrbit 8 181 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_181 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 181) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_181.1, data_8_181.2]

/-- Complete interval computation for depth 8, residue 182. -/
theorem bounds_8_182 : exactInterval 8 182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_182 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 182) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_182 : oddCount 182 8 = 5 ∧ acceleratedOrbit 8 182 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_182 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 182) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_182.1, data_8_182.2]

/-- Complete interval computation for depth 8, residue 183. -/
theorem bounds_8_183 : exactInterval 8 183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_183 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 183) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_183 : oddCount 183 8 = 5 ∧ acceleratedOrbit 8 183 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_183 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 183) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_183.1, data_8_183.2]

/-- Complete interval computation for depth 8, residue 184. -/
theorem bounds_8_184 : exactInterval 8 184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_184 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 184) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_184 : oddCount 184 8 = 3 ∧ acceleratedOrbit 8 184 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_184 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 184) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_184.1, data_8_184.2]

end Collatz.Research.DescentIntervals.Batch043
