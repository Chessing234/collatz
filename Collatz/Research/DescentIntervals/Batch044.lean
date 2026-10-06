import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch044

/-- Complete interval computation for depth 8, residue 185. -/
theorem bounds_8_185 : exactInterval 8 185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_185 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 185) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_185 : oddCount 185 8 = 4 ∧ acceleratedOrbit 8 185 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_185 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 185) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_185.1, data_8_185.2]

/-- Complete interval computation for depth 8, residue 186. -/
theorem bounds_8_186 : exactInterval 8 186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_186 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 186) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_186 : oddCount 186 8 = 3 ∧ acceleratedOrbit 8 186 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_186 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 186) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_186.1, data_8_186.2]

/-- Complete interval computation for depth 8, residue 187. -/
theorem bounds_8_187 : exactInterval 8 187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_187 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 187) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_187 : oddCount 187 8 = 5 ∧ acceleratedOrbit 8 187 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_187 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 187) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_187.1, data_8_187.2]

/-- Complete interval computation for depth 8, residue 188. -/
theorem bounds_8_188 : exactInterval 8 188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_188 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 188) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_188 : oddCount 188 8 = 5 ∧ acceleratedOrbit 8 188 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_188 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 188) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_188.1, data_8_188.2]

/-- Complete interval computation for depth 8, residue 189. -/
theorem bounds_8_189 : exactInterval 8 189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_189 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 189) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_189 : oddCount 189 8 = 5 ∧ acceleratedOrbit 8 189 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_189 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 189) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_189.1, data_8_189.2]

/-- Complete interval computation for depth 8, residue 190. -/
theorem bounds_8_190 : exactInterval 8 190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_190 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 190) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_190 : oddCount 190 8 = 5 ∧ acceleratedOrbit 8 190 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_190 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 190) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_190.1, data_8_190.2]

/-- Complete interval computation for depth 8, residue 191. -/
theorem bounds_8_191 : exactInterval 8 191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_191 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 191) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_191 : oddCount 191 8 = 7 ∧ acceleratedOrbit 8 191 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_191 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 191) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_191.1, data_8_191.2]

/-- Complete interval computation for depth 8, residue 192. -/
theorem bounds_8_192 : exactInterval 8 192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_192 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 192) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_192 : oddCount 192 8 = 2 ∧ acceleratedOrbit 8 192 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_192 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 192) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_192.1, data_8_192.2]

/-- Complete interval computation for depth 8, residue 193. -/
theorem bounds_8_193 : exactInterval 8 193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_193 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 193) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_193 : oddCount 193 8 = 4 ∧ acceleratedOrbit 8 193 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_193 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 193) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_193.1, data_8_193.2]

/-- Complete interval computation for depth 8, residue 194. -/
theorem bounds_8_194 : exactInterval 8 194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_194 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 194) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_194 : oddCount 194 8 = 5 ∧ acceleratedOrbit 8 194 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_194 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 194) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_194.1, data_8_194.2]

end Collatz.Research.DescentIntervals.Batch044
