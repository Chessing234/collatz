import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch050

/-- Complete interval computation for depth 8, residue 246. -/
theorem bounds_8_246 : exactInterval 8 246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_246 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 246) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_246 : oddCount 246 8 = 5 ∧ acceleratedOrbit 8 246 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_246 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 246) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_246.1, data_8_246.2]

/-- Complete interval computation for depth 8, residue 247. -/
theorem bounds_8_247 : exactInterval 8 247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_247 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 247) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_247 : oddCount 247 8 = 5 ∧ acceleratedOrbit 8 247 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_247 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 247) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_247.1, data_8_247.2]

/-- Complete interval computation for depth 8, residue 248. -/
theorem bounds_8_248 : exactInterval 8 248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_248 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 248) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_248 : oddCount 248 8 = 5 ∧ acceleratedOrbit 8 248 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_248 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 248) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_248.1, data_8_248.2]

/-- Complete interval computation for depth 8, residue 249. -/
theorem bounds_8_249 : exactInterval 8 249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_249 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 249) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_249 : oddCount 249 8 = 5 ∧ acceleratedOrbit 8 249 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_249 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 249) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_249.1, data_8_249.2]

/-- Complete interval computation for depth 8, residue 250. -/
theorem bounds_8_250 : exactInterval 8 250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_250 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 250) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_250 : oddCount 250 8 = 5 ∧ acceleratedOrbit 8 250 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_250 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 250) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_250.1, data_8_250.2]

/-- Complete interval computation for depth 8, residue 251. -/
theorem bounds_8_251 : exactInterval 8 251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_251 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 251) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_251 : oddCount 251 8 = 6 ∧ acceleratedOrbit 8 251 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_251 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 251) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_251.1, data_8_251.2]

/-- Complete interval computation for depth 8, residue 252. -/
theorem bounds_8_252 : exactInterval 8 252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_252 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 252) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_252 : oddCount 252 8 = 6 ∧ acceleratedOrbit 8 252 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_252 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 252) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_252.1, data_8_252.2]

/-- Complete interval computation for depth 8, residue 253. -/
theorem bounds_8_253 : exactInterval 8 253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_253 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 253) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_253 : oddCount 253 8 = 6 ∧ acceleratedOrbit 8 253 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_253 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 253) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_253.1, data_8_253.2]

/-- Complete interval computation for depth 8, residue 254. -/
theorem bounds_8_254 : exactInterval 8 254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_254 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 254) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_254 : oddCount 254 8 = 7 ∧ acceleratedOrbit 8 254 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_254 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 254) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_254.1, data_8_254.2]

/-- Complete interval computation for depth 8, residue 255. -/
theorem bounds_8_255 : exactInterval 8 255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_255 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 255) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_255 : oddCount 255 8 = 8 ∧ acceleratedOrbit 8 255 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_255 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 255) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_255.1, data_8_255.2]

/-- Complete interval computation for depth 9, residue 0. -/
theorem bounds_9_0 : exactInterval 9 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_0 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 0) 9 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_0 : oddCount 0 9 = 0 ∧ acceleratedOrbit 9 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_0 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_0.1, data_9_0.2]

end Collatz.Research.DescentIntervals.Batch050
