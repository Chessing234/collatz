import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch069

/-- Complete interval computation for depth 9, residue 184. -/
theorem bounds_9_184 : exactInterval 9 184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_184 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 184) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_184 : oddCount 184 9 = 3 ∧ acceleratedOrbit 9 184 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_184 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 184) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_184.1, data_9_184.2]

/-- Complete interval computation for depth 9, residue 185. -/
theorem bounds_9_185 : exactInterval 9 185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_185 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 185) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_185 : oddCount 185 9 = 5 ∧ acceleratedOrbit 9 185 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_185 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 185) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_185.1, data_9_185.2]

/-- Complete interval computation for depth 9, residue 186. -/
theorem bounds_9_186 : exactInterval 9 186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_186 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 186) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_186 : oddCount 186 9 = 3 ∧ acceleratedOrbit 9 186 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_186 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 186) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_186.1, data_9_186.2]

/-- Complete interval computation for depth 9, residue 187. -/
theorem bounds_9_187 : exactInterval 9 187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_187 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 187) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_187 : oddCount 187 9 = 6 ∧ acceleratedOrbit 9 187 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_187 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 187) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_187.1, data_9_187.2]

/-- Complete interval computation for depth 9, residue 188. -/
theorem bounds_9_188 : exactInterval 9 188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_188 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 188) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_188 : oddCount 188 9 = 5 ∧ acceleratedOrbit 9 188 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_188 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 188) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_188.1, data_9_188.2]

/-- Complete interval computation for depth 9, residue 189. -/
theorem bounds_9_189 : exactInterval 9 189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_189 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 189) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_189 : oddCount 189 9 = 5 ∧ acceleratedOrbit 9 189 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_189 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 189) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_189.1, data_9_189.2]

/-- Complete interval computation for depth 9, residue 190. -/
theorem bounds_9_190 : exactInterval 9 190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_190 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 190) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_190 : oddCount 190 9 = 5 ∧ acceleratedOrbit 9 190 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_190 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 190) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_190.1, data_9_190.2]

/-- Complete interval computation for depth 9, residue 191. -/
theorem bounds_9_191 : exactInterval 9 191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_191 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 191) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_191 : oddCount 191 9 = 7 ∧ acceleratedOrbit 9 191 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_191 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 191) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_191.1, data_9_191.2]

/-- Complete interval computation for depth 9, residue 192. -/
theorem bounds_9_192 : exactInterval 9 192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_192 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 192) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_192 : oddCount 192 9 = 2 ∧ acceleratedOrbit 9 192 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_192 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 192) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_192.1, data_9_192.2]

/-- Complete interval computation for depth 9, residue 193. -/
theorem bounds_9_193 : exactInterval 9 193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_193 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 193) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_193 : oddCount 193 9 = 4 ∧ acceleratedOrbit 9 193 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_193 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 193) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_193.1, data_9_193.2]

/-- Complete interval computation for depth 9, residue 194. -/
theorem bounds_9_194 : exactInterval 9 194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_194 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 194) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_194 : oddCount 194 9 = 5 ∧ acceleratedOrbit 9 194 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_194 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 194) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_194.1, data_9_194.2]

end Collatz.Research.DescentIntervals.Batch069
