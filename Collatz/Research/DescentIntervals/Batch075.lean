import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch075

/-- Complete interval computation for depth 9, residue 246. -/
theorem bounds_9_246 : exactInterval 9 246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_246 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 246) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_246 : oddCount 246 9 = 5 ∧ acceleratedOrbit 9 246 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_246 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 246) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_246.1, data_9_246.2]

/-- Complete interval computation for depth 9, residue 247. -/
theorem bounds_9_247 : exactInterval 9 247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_247 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 247) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_247 : oddCount 247 9 = 5 ∧ acceleratedOrbit 9 247 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_247 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 247) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_247.1, data_9_247.2]

/-- Complete interval computation for depth 9, residue 248. -/
theorem bounds_9_248 : exactInterval 9 248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_248 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 248) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_248 : oddCount 248 9 = 5 ∧ acceleratedOrbit 9 248 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_248 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 248) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_248.1, data_9_248.2]

/-- Complete interval computation for depth 9, residue 249. -/
theorem bounds_9_249 : exactInterval 9 249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_249 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 249) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_249 : oddCount 249 9 = 5 ∧ acceleratedOrbit 9 249 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_249 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 249) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_249.1, data_9_249.2]

/-- Complete interval computation for depth 9, residue 250. -/
theorem bounds_9_250 : exactInterval 9 250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_250 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 250) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_250 : oddCount 250 9 = 5 ∧ acceleratedOrbit 9 250 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_250 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 250) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_250.1, data_9_250.2]

/-- Complete interval computation for depth 9, residue 251. -/
theorem bounds_9_251 : exactInterval 9 251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_251 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 251) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_251 : oddCount 251 9 = 7 ∧ acceleratedOrbit 9 251 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_251 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 251) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_251.1, data_9_251.2]

/-- Complete interval computation for depth 9, residue 252. -/
theorem bounds_9_252 : exactInterval 9 252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_252 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 252) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_252 : oddCount 252 9 = 6 ∧ acceleratedOrbit 9 252 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_252 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 252) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_252.1, data_9_252.2]

/-- Complete interval computation for depth 9, residue 253. -/
theorem bounds_9_253 : exactInterval 9 253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_253 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 253) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_253 : oddCount 253 9 = 6 ∧ acceleratedOrbit 9 253 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_253 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 253) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_253.1, data_9_253.2]

/-- Complete interval computation for depth 9, residue 254. -/
theorem bounds_9_254 : exactInterval 9 254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_254 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 254) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_254 : oddCount 254 9 = 7 ∧ acceleratedOrbit 9 254 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_254 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 254) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_254.1, data_9_254.2]

/-- Complete interval computation for depth 9, residue 255. -/
theorem bounds_9_255 : exactInterval 9 255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_255 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 255) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_255 : oddCount 255 9 = 8 ∧ acceleratedOrbit 9 255 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_255 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 255) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_255.1, data_9_255.2]

end Collatz.Research.DescentIntervals.Batch075
