import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0219

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 276. -/
theorem bounds_12_276 : exactInterval 12 276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_276 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 276) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_276 : oddCount 276 12 = 3 ∧ acceleratedOrbit 12 276 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_276 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 276) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_276.1, data_12_276.2]

/-- Complete interval computation for depth 12, residue 277. -/
theorem bounds_12_277 : exactInterval 12 277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_277 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 277) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_277 : oddCount 277 12 = 3 ∧ acceleratedOrbit 12 277 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_277 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 277) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_277.1, data_12_277.2]

/-- Complete interval computation for depth 12, residue 278. -/
theorem bounds_12_278 : exactInterval 12 278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_278 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 278) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_278 : oddCount 278 12 = 7 ∧ acceleratedOrbit 12 278 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_278 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 278) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_278.1, data_12_278.2]

/-- Complete interval computation for depth 12, residue 279. -/
theorem bounds_12_279 : exactInterval 12 279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_279 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 279) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_279 : oddCount 279 12 = 7 ∧ acceleratedOrbit 12 279 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_279 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 279) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_279.1, data_12_279.2]

/-- Complete interval computation for depth 12, residue 280. -/
theorem bounds_12_280 : exactInterval 12 280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_280 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 280) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_280 : oddCount 280 12 = 3 ∧ acceleratedOrbit 12 280 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_280 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 280) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_280.1, data_12_280.2]

/-- Complete interval computation for depth 12, residue 281. -/
theorem bounds_12_281 : exactInterval 12 281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_281 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 281) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_281 : oddCount 281 12 = 7 ∧ acceleratedOrbit 12 281 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_281 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 281) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_281.1, data_12_281.2]

/-- Complete interval computation for depth 12, residue 282. -/
theorem bounds_12_282 : exactInterval 12 282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_282 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 282) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_282 : oddCount 282 12 = 3 ∧ acceleratedOrbit 12 282 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_282 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 282) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_282.1, data_12_282.2]

/-- Complete interval computation for depth 12, residue 283. -/
theorem bounds_12_283 : exactInterval 12 283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_283 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 283) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_283 : oddCount 283 12 = 9 ∧ acceleratedOrbit 12 283 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_283 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 283) = 3 ^ 9 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_283.1, data_12_283.2]

/-- Complete interval computation for depth 12, residue 284. -/
theorem bounds_12_284 : exactInterval 12 284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_284 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 284) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_284 : oddCount 284 12 = 7 ∧ acceleratedOrbit 12 284 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_284 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 284) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_284.1, data_12_284.2]

/-- Complete interval computation for depth 12, residue 285. -/
theorem bounds_12_285 : exactInterval 12 285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_285 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 285) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_285 : oddCount 285 12 = 7 ∧ acceleratedOrbit 12 285 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_285 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 285) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_285.1, data_12_285.2]

/-- Complete interval computation for depth 12, residue 286. -/
theorem bounds_12_286 : exactInterval 12 286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_286 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 286) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_286 : oddCount 286 12 = 7 ∧ acceleratedOrbit 12 286 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_286 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 286) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_286.1, data_12_286.2]

/-- Complete interval computation for depth 12, residue 287. -/
theorem bounds_12_287 : exactInterval 12 287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_287 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 287) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_287 : oddCount 287 12 = 7 ∧ acceleratedOrbit 12 287 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_287 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 287) = 3 ^ 7 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_287.1, data_12_287.2]

/-- Complete interval computation for depth 12, residue 288. -/
theorem bounds_12_288 : exactInterval 12 288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_288 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 288) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_288 : oddCount 288 12 = 5 ∧ acceleratedOrbit 12 288 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_288 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 288) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_288.1, data_12_288.2]

/-- Complete interval computation for depth 12, residue 289. -/
theorem bounds_12_289 : exactInterval 12 289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_289 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 289) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_289 : oddCount 289 12 = 6 ∧ acceleratedOrbit 12 289 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_289 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 289) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_289.1, data_12_289.2]

/-- Complete interval computation for depth 12, residue 290. -/
theorem bounds_12_290 : exactInterval 12 290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_290 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 290) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_290 : oddCount 290 12 = 7 ∧ acceleratedOrbit 12 290 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_290 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 290) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_290.1, data_12_290.2]

end Collatz.Research.StoppingAtlas.Batch0219
