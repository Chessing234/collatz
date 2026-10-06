import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch078

/-- Complete interval computation for depth 9, residue 276. -/
theorem bounds_9_276 : exactInterval 9 276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_276 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 276) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_276 : oddCount 276 9 = 2 ∧ acceleratedOrbit 9 276 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_276 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 276) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_276.1, data_9_276.2]

/-- Complete interval computation for depth 9, residue 277. -/
theorem bounds_9_277 : exactInterval 9 277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_277 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 277) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_277 : oddCount 277 9 = 2 ∧ acceleratedOrbit 9 277 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_277 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 277) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_277.1, data_9_277.2]

/-- Complete interval computation for depth 9, residue 278. -/
theorem bounds_9_278 : exactInterval 9 278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_278 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 278) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_278 : oddCount 278 9 = 5 ∧ acceleratedOrbit 9 278 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_278 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 278) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_278.1, data_9_278.2]

/-- Complete interval computation for depth 9, residue 279. -/
theorem bounds_9_279 : exactInterval 9 279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_279 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 279) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_279 : oddCount 279 9 = 5 ∧ acceleratedOrbit 9 279 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_279 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 279) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_279.1, data_9_279.2]

/-- Complete interval computation for depth 9, residue 280. -/
theorem bounds_9_280 : exactInterval 9 280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_280 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 280) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_280 : oddCount 280 9 = 2 ∧ acceleratedOrbit 9 280 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_280 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 280) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_280.1, data_9_280.2]

/-- Complete interval computation for depth 9, residue 281. -/
theorem bounds_9_281 : exactInterval 9 281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_281 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 281) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_281 : oddCount 281 9 = 6 ∧ acceleratedOrbit 9 281 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_281 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 281) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_281.1, data_9_281.2]

/-- Complete interval computation for depth 9, residue 282. -/
theorem bounds_9_282 : exactInterval 9 282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_282 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 282) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_282 : oddCount 282 9 = 2 ∧ acceleratedOrbit 9 282 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_282 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 282) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_282.1, data_9_282.2]

/-- Complete interval computation for depth 9, residue 283. -/
theorem bounds_9_283 : exactInterval 9 283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_283 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 283) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_283 : oddCount 283 9 = 8 ∧ acceleratedOrbit 9 283 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_283 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 283) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_283.1, data_9_283.2]

/-- Complete interval computation for depth 9, residue 284. -/
theorem bounds_9_284 : exactInterval 9 284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_284 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 284) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_284 : oddCount 284 9 = 5 ∧ acceleratedOrbit 9 284 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_284 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 284) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_284.1, data_9_284.2]

/-- Complete interval computation for depth 9, residue 285. -/
theorem bounds_9_285 : exactInterval 9 285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_285 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 285) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_285 : oddCount 285 9 = 5 ∧ acceleratedOrbit 9 285 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_285 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 285) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_285.1, data_9_285.2]

/-- Complete interval computation for depth 9, residue 286. -/
theorem bounds_9_286 : exactInterval 9 286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_286 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 286) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_286 : oddCount 286 9 = 5 ∧ acceleratedOrbit 9 286 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_286 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 286) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_286.1, data_9_286.2]

end Collatz.Research.DescentIntervals.Batch078
