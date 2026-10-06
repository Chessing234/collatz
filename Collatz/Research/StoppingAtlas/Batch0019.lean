import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0019

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 276. -/
theorem bounds_10_276 : exactInterval 10 276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_276 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 276) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_276 : oddCount 276 10 = 3 ∧ acceleratedOrbit 10 276 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_276 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 276) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_276.1, data_10_276.2]

/-- Complete interval computation for depth 10, residue 277. -/
theorem bounds_10_277 : exactInterval 10 277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_277 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 277) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_277 : oddCount 277 10 = 3 ∧ acceleratedOrbit 10 277 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_277 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 277) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_277.1, data_10_277.2]

/-- Complete interval computation for depth 10, residue 278. -/
theorem bounds_10_278 : exactInterval 10 278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_278 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 278) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_278 : oddCount 278 10 = 5 ∧ acceleratedOrbit 10 278 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_278 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 278) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_278.1, data_10_278.2]

/-- Complete interval computation for depth 10, residue 279. -/
theorem bounds_10_279 : exactInterval 10 279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_279 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 279) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_279 : oddCount 279 10 = 5 ∧ acceleratedOrbit 10 279 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_279 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 279) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_279.1, data_10_279.2]

/-- Complete interval computation for depth 10, residue 280. -/
theorem bounds_10_280 : exactInterval 10 280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_280 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 280) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_280 : oddCount 280 10 = 3 ∧ acceleratedOrbit 10 280 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_280 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 280) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_280.1, data_10_280.2]

/-- Complete interval computation for depth 10, residue 281. -/
theorem bounds_10_281 : exactInterval 10 281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_281 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 281) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_281 : oddCount 281 10 = 6 ∧ acceleratedOrbit 10 281 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_281 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 281) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_281.1, data_10_281.2]

/-- Complete interval computation for depth 10, residue 282. -/
theorem bounds_10_282 : exactInterval 10 282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_282 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 282) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_282 : oddCount 282 10 = 3 ∧ acceleratedOrbit 10 282 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_282 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 282) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_282.1, data_10_282.2]

/-- Complete interval computation for depth 10, residue 283. -/
theorem bounds_10_283 : exactInterval 10 283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_283 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 283) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_283 : oddCount 283 10 = 8 ∧ acceleratedOrbit 10 283 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_283 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 283) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_283.1, data_10_283.2]

/-- Complete interval computation for depth 10, residue 284. -/
theorem bounds_10_284 : exactInterval 10 284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_284 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 284) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_284 : oddCount 284 10 = 6 ∧ acceleratedOrbit 10 284 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_284 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 284) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_284.1, data_10_284.2]

/-- Complete interval computation for depth 10, residue 285. -/
theorem bounds_10_285 : exactInterval 10 285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_285 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 285) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_285 : oddCount 285 10 = 6 ∧ acceleratedOrbit 10 285 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_285 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 285) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_285.1, data_10_285.2]

/-- Complete interval computation for depth 10, residue 286. -/
theorem bounds_10_286 : exactInterval 10 286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_286 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 286) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_286 : oddCount 286 10 = 6 ∧ acceleratedOrbit 10 286 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_286 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 286) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_286.1, data_10_286.2]

/-- Complete interval computation for depth 10, residue 287. -/
theorem bounds_10_287 : exactInterval 10 287 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_287 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 287) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_287 : oddCount 287 10 = 6 ∧ acceleratedOrbit 10 287 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_287 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 287) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_287.1, data_10_287.2]

/-- Complete interval computation for depth 10, residue 288. -/
theorem bounds_10_288 : exactInterval 10 288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_288 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 288) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_288 : oddCount 288 10 = 4 ∧ acceleratedOrbit 10 288 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_288 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 288) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_288.1, data_10_288.2]

/-- Complete interval computation for depth 10, residue 289. -/
theorem bounds_10_289 : exactInterval 10 289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_289 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 289) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_289 : oddCount 289 10 = 4 ∧ acceleratedOrbit 10 289 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_289 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 289) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_289.1, data_10_289.2]

/-- Complete interval computation for depth 10, residue 290. -/
theorem bounds_10_290 : exactInterval 10 290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_290 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 290) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_290 : oddCount 290 10 = 5 ∧ acceleratedOrbit 10 290 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_290 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 290) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_290.1, data_10_290.2]

end Collatz.Research.StoppingAtlas.Batch0019
