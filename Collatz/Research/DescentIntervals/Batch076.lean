import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch076

/-- Complete interval computation for depth 9, residue 256. -/
theorem bounds_9_256 : exactInterval 9 256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_256 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 256) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_256 : oddCount 256 9 = 1 ∧ acceleratedOrbit 9 256 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_256 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 256) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_256.1, data_9_256.2]

/-- Complete interval computation for depth 9, residue 257. -/
theorem bounds_9_257 : exactInterval 9 257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_257 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 257) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_257 : oddCount 257 9 = 4 ∧ acceleratedOrbit 9 257 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_257 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 257) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_257.1, data_9_257.2]

/-- Complete interval computation for depth 9, residue 258. -/
theorem bounds_9_258 : exactInterval 9 258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_258 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 258) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_258 : oddCount 258 9 = 5 ∧ acceleratedOrbit 9 258 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_258 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 258) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_258.1, data_9_258.2]

/-- Complete interval computation for depth 9, residue 259. -/
theorem bounds_9_259 : exactInterval 9 259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_259 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 259) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_259 : oddCount 259 9 = 5 ∧ acceleratedOrbit 9 259 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_259 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 259) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_259.1, data_9_259.2]

/-- Complete interval computation for depth 9, residue 260. -/
theorem bounds_9_260 : exactInterval 9 260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_260 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 260) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_260 : oddCount 260 9 = 3 ∧ acceleratedOrbit 9 260 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_260 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 260) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_260.1, data_9_260.2]

/-- Complete interval computation for depth 9, residue 261. -/
theorem bounds_9_261 : exactInterval 9 261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_261 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 261) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_261 : oddCount 261 9 = 3 ∧ acceleratedOrbit 9 261 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_261 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 261) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_261.1, data_9_261.2]

/-- Complete interval computation for depth 9, residue 262. -/
theorem bounds_9_262 : exactInterval 9 262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_262 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 262) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_262 : oddCount 262 9 = 3 ∧ acceleratedOrbit 9 262 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_262 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 262) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_262.1, data_9_262.2]

/-- Complete interval computation for depth 9, residue 263. -/
theorem bounds_9_263 : exactInterval 9 263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_263 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 263) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_263 : oddCount 263 9 = 6 ∧ acceleratedOrbit 9 263 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_263 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 263) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_263.1, data_9_263.2]

/-- Complete interval computation for depth 9, residue 264. -/
theorem bounds_9_264 : exactInterval 9 264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_264 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 264) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_264 : oddCount 264 9 = 4 ∧ acceleratedOrbit 9 264 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_264 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 264) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_264.1, data_9_264.2]

/-- Complete interval computation for depth 9, residue 265. -/
theorem bounds_9_265 : exactInterval 9 265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_265 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 265) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_265 : oddCount 265 9 = 6 ∧ acceleratedOrbit 9 265 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_265 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 265) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_265.1, data_9_265.2]

end Collatz.Research.DescentIntervals.Batch076
