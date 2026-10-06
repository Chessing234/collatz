import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0162

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5275. -/
theorem bounds_15_5275 : exactInterval 15 5275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5275 : oddCount 5275 15 = 9 ∧ acceleratedOrbit 15 5275 = 3170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5275) = 3 ^ 9 * m + 3170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5275.1, data_15_5275.2]

/-- Complete interval computation for depth 15, residue 5276. -/
theorem bounds_15_5276 : exactInterval 15 5276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5276 : oddCount 5276 15 = 7 ∧ acceleratedOrbit 15 5276 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5276) = 3 ^ 7 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5276.1, data_15_5276.2]

/-- Complete interval computation for depth 15, residue 5277. -/
theorem bounds_15_5277 : exactInterval 15 5277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5277 : oddCount 5277 15 = 7 ∧ acceleratedOrbit 15 5277 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5277) = 3 ^ 7 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5277.1, data_15_5277.2]

/-- Complete interval computation for depth 15, residue 5278. -/
theorem bounds_15_5278 : exactInterval 15 5278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5278 : oddCount 5278 15 = 7 ∧ acceleratedOrbit 15 5278 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5278) = 3 ^ 7 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5278.1, data_15_5278.2]

/-- Complete interval computation for depth 15, residue 5279. -/
theorem bounds_15_5279 : exactInterval 15 5279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5279 : oddCount 5279 15 = 10 ∧ acceleratedOrbit 15 5279 = 9515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5279) = 3 ^ 10 * m + 9515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5279.1, data_15_5279.2]

/-- Complete interval computation for depth 15, residue 5280. -/
theorem bounds_15_5280 : exactInterval 15 5280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5280 : oddCount 5280 15 = 6 ∧ acceleratedOrbit 15 5280 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5280) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5280.1, data_15_5280.2]

/-- Complete interval computation for depth 15, residue 5281. -/
theorem bounds_15_5281 : exactInterval 15 5281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5281 : oddCount 5281 15 = 8 ∧ acceleratedOrbit 15 5281 = 1058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5281) = 3 ^ 8 * m + 1058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5281.1, data_15_5281.2]

/-- Complete interval computation for depth 15, residue 5282. -/
theorem bounds_15_5282 : exactInterval 15 5282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5282 : oddCount 5282 15 = 9 ∧ acceleratedOrbit 15 5282 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5282) = 3 ^ 9 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5282.1, data_15_5282.2]

/-- Complete interval computation for depth 15, residue 5283. -/
theorem bounds_15_5283 : exactInterval 15 5283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5283 : oddCount 5283 15 = 9 ∧ acceleratedOrbit 15 5283 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5283) = 3 ^ 9 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5283.1, data_15_5283.2]

/-- Complete interval computation for depth 15, residue 5284. -/
theorem bounds_15_5284 : exactInterval 15 5284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5284 : oddCount 5284 15 = 9 ∧ acceleratedOrbit 15 5284 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5284) = 3 ^ 9 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5284.1, data_15_5284.2]

/-- Complete interval computation for depth 15, residue 5285. -/
theorem bounds_15_5285 : exactInterval 15 5285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5285 : oddCount 5285 15 = 9 ∧ acceleratedOrbit 15 5285 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5285) = 3 ^ 9 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5285.1, data_15_5285.2]

/-- Complete interval computation for depth 15, residue 5286. -/
theorem bounds_15_5286 : exactInterval 15 5286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5286 : oddCount 5286 15 = 9 ∧ acceleratedOrbit 15 5286 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5286) = 3 ^ 9 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5286.1, data_15_5286.2]

/-- Complete interval computation for depth 15, residue 5287. -/
theorem bounds_15_5287 : exactInterval 15 5287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5287 : oddCount 5287 15 = 11 ∧ acceleratedOrbit 15 5287 = 28592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5287) = 3 ^ 11 * m + 28592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5287.1, data_15_5287.2]

/-- Complete interval computation for depth 15, residue 5288. -/
theorem bounds_15_5288 : exactInterval 15 5288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5288 : oddCount 5288 15 = 6 ∧ acceleratedOrbit 15 5288 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5288) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5288.1, data_15_5288.2]

/-- Complete interval computation for depth 15, residue 5289. -/
theorem bounds_15_5289 : exactInterval 15 5289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5289 : oddCount 5289 15 = 9 ∧ acceleratedOrbit 15 5289 = 3178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5289) = 3 ^ 9 * m + 3178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5289.1, data_15_5289.2]

/-- Complete interval computation for depth 15, residue 5290. -/
theorem bounds_15_5290 : exactInterval 15 5290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5290 : oddCount 5290 15 = 6 ∧ acceleratedOrbit 15 5290 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5290) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5290.1, data_15_5290.2]

/-- Complete interval computation for depth 15, residue 5291. -/
theorem bounds_15_5291 : exactInterval 15 5291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5291 : oddCount 5291 15 = 6 ∧ acceleratedOrbit 15 5291 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5291) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5291.1, data_15_5291.2]

/-- Complete interval computation for depth 15, residue 5292. -/
theorem bounds_15_5292 : exactInterval 15 5292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5292 : oddCount 5292 15 = 6 ∧ acceleratedOrbit 15 5292 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5292) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5292.1, data_15_5292.2]

/-- Complete interval computation for depth 15, residue 5293. -/
theorem bounds_15_5293 : exactInterval 15 5293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5293 : oddCount 5293 15 = 6 ∧ acceleratedOrbit 15 5293 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5293) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5293.1, data_15_5293.2]

/-- Complete interval computation for depth 15, residue 5294. -/
theorem bounds_15_5294 : exactInterval 15 5294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5294 : oddCount 5294 15 = 6 ∧ acceleratedOrbit 15 5294 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5294) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5294.1, data_15_5294.2]

/-- Complete interval computation for depth 15, residue 5295. -/
theorem bounds_15_5295 : exactInterval 15 5295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5295 : oddCount 5295 15 = 8 ∧ acceleratedOrbit 15 5295 = 1061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5295) = 3 ^ 8 * m + 1061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5295.1, data_15_5295.2]

/-- Complete interval computation for depth 15, residue 5296. -/
theorem bounds_15_5296 : exactInterval 15 5296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5296 : oddCount 5296 15 = 5 ∧ acceleratedOrbit 15 5296 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5296) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5296.1, data_15_5296.2]

/-- Complete interval computation for depth 15, residue 5297. -/
theorem bounds_15_5297 : exactInterval 15 5297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5297 : oddCount 5297 15 = 8 ∧ acceleratedOrbit 15 5297 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5297) = 3 ^ 8 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5297.1, data_15_5297.2]

/-- Complete interval computation for depth 15, residue 5298. -/
theorem bounds_15_5298 : exactInterval 15 5298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5298 : oddCount 5298 15 = 8 ∧ acceleratedOrbit 15 5298 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5298) = 3 ^ 8 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5298.1, data_15_5298.2]

/-- Complete interval computation for depth 15, residue 5299. -/
theorem bounds_15_5299 : exactInterval 15 5299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5299 : oddCount 5299 15 = 8 ∧ acceleratedOrbit 15 5299 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5299) = 3 ^ 8 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5299.1, data_15_5299.2]

/-- Complete interval computation for depth 15, residue 5300. -/
theorem bounds_15_5300 : exactInterval 15 5300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5300 : oddCount 5300 15 = 5 ∧ acceleratedOrbit 15 5300 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5300) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5300.1, data_15_5300.2]

/-- Complete interval computation for depth 15, residue 5301. -/
theorem bounds_15_5301 : exactInterval 15 5301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5301 : oddCount 5301 15 = 5 ∧ acceleratedOrbit 15 5301 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5301) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5301.1, data_15_5301.2]

/-- Complete interval computation for depth 15, residue 5302. -/
theorem bounds_15_5302 : exactInterval 15 5302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5302 : oddCount 5302 15 = 9 ∧ acceleratedOrbit 15 5302 = 3187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5302) = 3 ^ 9 * m + 3187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5302.1, data_15_5302.2]

/-- Complete interval computation for depth 15, residue 5303. -/
theorem bounds_15_5303 : exactInterval 15 5303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5303 : oddCount 5303 15 = 9 ∧ acceleratedOrbit 15 5303 = 3187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5303) = 3 ^ 9 * m + 3187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5303.1, data_15_5303.2]

/-- Complete interval computation for depth 15, residue 5304. -/
theorem bounds_15_5304 : exactInterval 15 5304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5304 : oddCount 5304 15 = 5 ∧ acceleratedOrbit 15 5304 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5304) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5304.1, data_15_5304.2]

/-- Complete interval computation for depth 15, residue 5305. -/
theorem bounds_15_5305 : exactInterval 15 5305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5305 : oddCount 5305 15 = 8 ∧ acceleratedOrbit 15 5305 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5305) = 3 ^ 8 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5305.1, data_15_5305.2]

/-- Complete interval computation for depth 15, residue 5306. -/
theorem bounds_15_5306 : exactInterval 15 5306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5306 : oddCount 5306 15 = 5 ∧ acceleratedOrbit 15 5306 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5306) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5306.1, data_15_5306.2]

/-- Complete interval computation for depth 15, residue 5307. -/
theorem bounds_15_5307 : exactInterval 15 5307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5307 : oddCount 5307 15 = 10 ∧ acceleratedOrbit 15 5307 = 9568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5307) = 3 ^ 10 * m + 9568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5307.1, data_15_5307.2]

end Collatz.Research.PassageAtlas.Batch0162
