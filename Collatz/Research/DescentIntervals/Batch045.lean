import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch045

/-- Complete interval computation for depth 8, residue 195. -/
theorem bounds_8_195 : exactInterval 8 195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_195 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 195) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_195 : oddCount 195 8 = 5 ∧ acceleratedOrbit 8 195 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_195 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 195) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_195.1, data_8_195.2]

/-- Complete interval computation for depth 8, residue 196. -/
theorem bounds_8_196 : exactInterval 8 196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_196 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 196) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_196 : oddCount 196 8 = 2 ∧ acceleratedOrbit 8 196 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_196 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 196) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_196.1, data_8_196.2]

/-- Complete interval computation for depth 8, residue 197. -/
theorem bounds_8_197 : exactInterval 8 197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_197 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 197) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_197 : oddCount 197 8 = 2 ∧ acceleratedOrbit 8 197 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_197 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 197) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_197.1, data_8_197.2]

/-- Complete interval computation for depth 8, residue 198. -/
theorem bounds_8_198 : exactInterval 8 198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_198 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 198) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_198 : oddCount 198 8 = 2 ∧ acceleratedOrbit 8 198 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_198 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 198) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_198.1, data_8_198.2]

/-- Complete interval computation for depth 8, residue 199. -/
theorem bounds_8_199 : exactInterval 8 199 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_199 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 199) 8 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_199 : oddCount 199 8 = 5 ∧ acceleratedOrbit 8 199 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_199 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 199) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_199.1, data_8_199.2]

/-- Complete interval computation for depth 8, residue 200. -/
theorem bounds_8_200 : exactInterval 8 200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_200 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 200) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_200 : oddCount 200 8 = 3 ∧ acceleratedOrbit 8 200 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_200 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 200) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_200.1, data_8_200.2]

/-- Complete interval computation for depth 8, residue 201. -/
theorem bounds_8_201 : exactInterval 8 201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_201 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 201) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_201 : oddCount 201 8 = 4 ∧ acceleratedOrbit 8 201 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_201 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 201) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_201.1, data_8_201.2]

/-- Complete interval computation for depth 8, residue 202. -/
theorem bounds_8_202 : exactInterval 8 202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_202 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 202) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_202 : oddCount 202 8 = 3 ∧ acceleratedOrbit 8 202 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_202 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 202) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_202.1, data_8_202.2]

/-- Complete interval computation for depth 8, residue 203. -/
theorem bounds_8_203 : exactInterval 8 203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_203 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 203) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_203 : oddCount 203 8 = 4 ∧ acceleratedOrbit 8 203 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_203 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 203) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_203.1, data_8_203.2]

/-- Complete interval computation for depth 8, residue 204. -/
theorem bounds_8_204 : exactInterval 8 204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_204 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 204) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_204 : oddCount 204 8 = 3 ∧ acceleratedOrbit 8 204 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_204 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 204) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_204.1, data_8_204.2]

end Collatz.Research.DescentIntervals.Batch045
