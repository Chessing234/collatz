import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch048

/-- Complete interval computation for depth 8, residue 226. -/
theorem bounds_8_226 : exactInterval 8 226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_226 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 226) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_226 : oddCount 226 8 = 2 ∧ acceleratedOrbit 8 226 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_226 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 226) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_226.1, data_8_226.2]

/-- Complete interval computation for depth 8, residue 227. -/
theorem bounds_8_227 : exactInterval 8 227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_227 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 227) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_227 : oddCount 227 8 = 2 ∧ acceleratedOrbit 8 227 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_227 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 227) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_227.1, data_8_227.2]

/-- Complete interval computation for depth 8, residue 228. -/
theorem bounds_8_228 : exactInterval 8 228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_228 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 228) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_228 : oddCount 228 8 = 4 ∧ acceleratedOrbit 8 228 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_228 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 228) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_228.1, data_8_228.2]

/-- Complete interval computation for depth 8, residue 229. -/
theorem bounds_8_229 : exactInterval 8 229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_229 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 229) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_229 : oddCount 229 8 = 4 ∧ acceleratedOrbit 8 229 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_229 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 229) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_229.1, data_8_229.2]

/-- Complete interval computation for depth 8, residue 230. -/
theorem bounds_8_230 : exactInterval 8 230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_230 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 230) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_230 : oddCount 230 8 = 4 ∧ acceleratedOrbit 8 230 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_230 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 230) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_230.1, data_8_230.2]

/-- Complete interval computation for depth 8, residue 231. -/
theorem bounds_8_231 : exactInterval 8 231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_231 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 231) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_231 : oddCount 231 8 = 6 ∧ acceleratedOrbit 8 231 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_231 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 231) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_231.1, data_8_231.2]

/-- Complete interval computation for depth 8, residue 232. -/
theorem bounds_8_232 : exactInterval 8 232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_232 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 232) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_232 : oddCount 232 8 = 3 ∧ acceleratedOrbit 8 232 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_232 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 232) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_232.1, data_8_232.2]

/-- Complete interval computation for depth 8, residue 233. -/
theorem bounds_8_233 : exactInterval 8 233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_233 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 233) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_233 : oddCount 233 8 = 6 ∧ acceleratedOrbit 8 233 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_233 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 233) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_233.1, data_8_233.2]

/-- Complete interval computation for depth 8, residue 234. -/
theorem bounds_8_234 : exactInterval 8 234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_234 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 234) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_234 : oddCount 234 8 = 3 ∧ acceleratedOrbit 8 234 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_234 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 234) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_234.1, data_8_234.2]

/-- Complete interval computation for depth 8, residue 235. -/
theorem bounds_8_235 : exactInterval 8 235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_235 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 235) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_235 : oddCount 235 8 = 6 ∧ acceleratedOrbit 8 235 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_235 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 235) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_235.1, data_8_235.2]

end Collatz.Research.DescentIntervals.Batch048
