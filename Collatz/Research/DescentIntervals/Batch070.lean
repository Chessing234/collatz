import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch070

/-- Complete interval computation for depth 9, residue 195. -/
theorem bounds_9_195 : exactInterval 9 195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_195 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 195) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_195 : oddCount 195 9 = 5 ∧ acceleratedOrbit 9 195 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_195 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 195) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_195.1, data_9_195.2]

/-- Complete interval computation for depth 9, residue 196. -/
theorem bounds_9_196 : exactInterval 9 196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_196 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 196) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_196 : oddCount 196 9 = 3 ∧ acceleratedOrbit 9 196 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_196 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 196) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_196.1, data_9_196.2]

/-- Complete interval computation for depth 9, residue 197. -/
theorem bounds_9_197 : exactInterval 9 197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_197 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 197) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_197 : oddCount 197 9 = 3 ∧ acceleratedOrbit 9 197 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_197 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 197) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_197.1, data_9_197.2]

/-- Complete interval computation for depth 9, residue 198. -/
theorem bounds_9_198 : exactInterval 9 198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_198 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 198) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_198 : oddCount 198 9 = 3 ∧ acceleratedOrbit 9 198 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_198 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 198) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_198.1, data_9_198.2]

/-- Complete interval computation for depth 9, residue 199. -/
theorem bounds_9_199 : exactInterval 9 199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_199 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 199) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_199 : oddCount 199 9 = 5 ∧ acceleratedOrbit 9 199 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_199 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 199) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_199.1, data_9_199.2]

/-- Complete interval computation for depth 9, residue 200. -/
theorem bounds_9_200 : exactInterval 9 200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_200 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 200) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_200 : oddCount 200 9 = 3 ∧ acceleratedOrbit 9 200 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_200 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 200) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_200.1, data_9_200.2]

/-- Complete interval computation for depth 9, residue 201. -/
theorem bounds_9_201 : exactInterval 9 201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_201 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 201) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_201 : oddCount 201 9 = 4 ∧ acceleratedOrbit 9 201 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_201 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 201) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_201.1, data_9_201.2]

/-- Complete interval computation for depth 9, residue 202. -/
theorem bounds_9_202 : exactInterval 9 202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_202 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 202) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_202 : oddCount 202 9 = 3 ∧ acceleratedOrbit 9 202 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_202 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 202) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_202.1, data_9_202.2]

/-- Complete interval computation for depth 9, residue 203. -/
theorem bounds_9_203 : exactInterval 9 203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_203 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 203) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_203 : oddCount 203 9 = 5 ∧ acceleratedOrbit 9 203 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_203 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 203) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_203.1, data_9_203.2]

/-- Complete interval computation for depth 9, residue 204. -/
theorem bounds_9_204 : exactInterval 9 204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_204 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 204) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_204 : oddCount 204 9 = 3 ∧ acceleratedOrbit 9 204 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_204 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 204) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_204.1, data_9_204.2]

end Collatz.Research.DescentIntervals.Batch070
