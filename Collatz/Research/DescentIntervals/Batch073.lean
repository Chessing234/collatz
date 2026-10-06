import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch073

/-- Complete interval computation for depth 9, residue 225. -/
theorem bounds_9_225 : exactInterval 9 225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_225 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 225) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_225 : oddCount 225 9 = 7 ∧ acceleratedOrbit 9 225 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_225 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 225) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_225.1, data_9_225.2]

/-- Complete interval computation for depth 9, residue 226. -/
theorem bounds_9_226 : exactInterval 9 226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_226 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 226) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_226 : oddCount 226 9 = 2 ∧ acceleratedOrbit 9 226 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_226 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 226) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_226.1, data_9_226.2]

/-- Complete interval computation for depth 9, residue 227. -/
theorem bounds_9_227 : exactInterval 9 227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_227 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 227) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_227 : oddCount 227 9 = 2 ∧ acceleratedOrbit 9 227 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_227 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 227) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_227.1, data_9_227.2]

/-- Complete interval computation for depth 9, residue 228. -/
theorem bounds_9_228 : exactInterval 9 228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_228 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 228) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_228 : oddCount 228 9 = 4 ∧ acceleratedOrbit 9 228 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_228 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 228) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_228.1, data_9_228.2]

/-- Complete interval computation for depth 9, residue 229. -/
theorem bounds_9_229 : exactInterval 9 229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_229 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 229) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_229 : oddCount 229 9 = 4 ∧ acceleratedOrbit 9 229 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_229 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 229) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_229.1, data_9_229.2]

/-- Complete interval computation for depth 9, residue 230. -/
theorem bounds_9_230 : exactInterval 9 230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_230 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 230) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_230 : oddCount 230 9 = 4 ∧ acceleratedOrbit 9 230 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_230 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 230) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_230.1, data_9_230.2]

/-- Complete interval computation for depth 9, residue 231. -/
theorem bounds_9_231 : exactInterval 9 231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_231 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 231) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_231 : oddCount 231 9 = 7 ∧ acceleratedOrbit 9 231 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_231 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 231) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_231.1, data_9_231.2]

/-- Complete interval computation for depth 9, residue 232. -/
theorem bounds_9_232 : exactInterval 9 232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_232 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 232) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_232 : oddCount 232 9 = 3 ∧ acceleratedOrbit 9 232 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_232 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 232) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_232.1, data_9_232.2]

/-- Complete interval computation for depth 9, residue 233. -/
theorem bounds_9_233 : exactInterval 9 233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_233 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 233) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_233 : oddCount 233 9 = 6 ∧ acceleratedOrbit 9 233 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_233 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 233) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_233.1, data_9_233.2]

/-- Complete interval computation for depth 9, residue 234. -/
theorem bounds_9_234 : exactInterval 9 234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_234 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 234) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_234 : oddCount 234 9 = 3 ∧ acceleratedOrbit 9 234 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_234 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 234) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_234.1, data_9_234.2]

/-- Complete interval computation for depth 9, residue 235. -/
theorem bounds_9_235 : exactInterval 9 235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_235 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 235) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_235 : oddCount 235 9 = 6 ∧ acceleratedOrbit 9 235 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_235 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 235) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_235.1, data_9_235.2]

end Collatz.Research.DescentIntervals.Batch073
