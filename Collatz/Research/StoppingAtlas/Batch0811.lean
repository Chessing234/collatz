import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0811

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5273. -/
theorem bounds_13_5273 : exactInterval 13 5273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5273 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5273) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5273 : oddCount 5273 13 = 6 ∧ acceleratedOrbit 13 5273 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5273 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5273) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5273.1, data_13_5273.2]

/-- Complete interval computation for depth 13, residue 5274. -/
theorem bounds_13_5274 : exactInterval 13 5274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5274 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5274) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5274 : oddCount 5274 13 = 5 ∧ acceleratedOrbit 13 5274 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5274 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5274) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5274.1, data_13_5274.2]

/-- Complete interval computation for depth 13, residue 5275. -/
theorem bounds_13_5275 : exactInterval 13 5275 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5275 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5275) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5275 : oddCount 5275 13 = 8 ∧ acceleratedOrbit 13 5275 = 4226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5275 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5275) = 3 ^ 8 * m + 4226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5275.1, data_13_5275.2]

/-- Complete interval computation for depth 13, residue 5276. -/
theorem bounds_13_5276 : exactInterval 13 5276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5276 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5276) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5276 : oddCount 5276 13 = 6 ∧ acceleratedOrbit 13 5276 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5276 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5276) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5276.1, data_13_5276.2]

/-- Complete interval computation for depth 13, residue 5277. -/
theorem bounds_13_5277 : exactInterval 13 5277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5277 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5277) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5277 : oddCount 5277 13 = 6 ∧ acceleratedOrbit 13 5277 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5277 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5277) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5277.1, data_13_5277.2]

/-- Complete interval computation for depth 13, residue 5278. -/
theorem bounds_13_5278 : exactInterval 13 5278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5278 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5278) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5278 : oddCount 5278 13 = 6 ∧ acceleratedOrbit 13 5278 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5278 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5278) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5278.1, data_13_5278.2]

/-- Complete interval computation for depth 13, residue 5279. -/
theorem bounds_13_5279 : exactInterval 13 5279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5279 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5279) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5279 : oddCount 5279 13 = 10 ∧ acceleratedOrbit 13 5279 = 38060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5279 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5279) = 3 ^ 10 * m + 38060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5279.1, data_13_5279.2]

/-- Complete interval computation for depth 13, residue 5280. -/
theorem bounds_13_5280 : exactInterval 13 5280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5280 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5280) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5280 : oddCount 5280 13 = 5 ∧ acceleratedOrbit 13 5280 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5280 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5280) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5280.1, data_13_5280.2]

/-- Complete interval computation for depth 13, residue 5281. -/
theorem bounds_13_5281 : exactInterval 13 5281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5281 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5281) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5281 : oddCount 5281 13 = 8 ∧ acceleratedOrbit 13 5281 = 4232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5281 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5281) = 3 ^ 8 * m + 4232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5281.1, data_13_5281.2]

/-- Complete interval computation for depth 13, residue 5282. -/
theorem bounds_13_5282 : exactInterval 13 5282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5282 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5282) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5282 : oddCount 5282 13 = 8 ∧ acceleratedOrbit 13 5282 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5282 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5282) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5282.1, data_13_5282.2]

/-- Complete interval computation for depth 13, residue 5283. -/
theorem bounds_13_5283 : exactInterval 13 5283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5283 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5283) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5283 : oddCount 5283 13 = 8 ∧ acceleratedOrbit 13 5283 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5283 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5283) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5283.1, data_13_5283.2]

/-- Complete interval computation for depth 13, residue 5284. -/
theorem bounds_13_5284 : exactInterval 13 5284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5284 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5284) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5284 : oddCount 5284 13 = 8 ∧ acceleratedOrbit 13 5284 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5284 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5284) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5284.1, data_13_5284.2]

/-- Complete interval computation for depth 13, residue 5285. -/
theorem bounds_13_5285 : exactInterval 13 5285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5285 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5285) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5285 : oddCount 5285 13 = 8 ∧ acceleratedOrbit 13 5285 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5285 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5285) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5285.1, data_13_5285.2]

/-- Complete interval computation for depth 13, residue 5286. -/
theorem bounds_13_5286 : exactInterval 13 5286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5286 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5286) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5286 : oddCount 5286 13 = 8 ∧ acceleratedOrbit 13 5286 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5286 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5286) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5286.1, data_13_5286.2]

/-- Complete interval computation for depth 13, residue 5287. -/
theorem bounds_13_5287 : exactInterval 13 5287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5287 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5287) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5287 : oddCount 5287 13 = 9 ∧ acceleratedOrbit 13 5287 = 12707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5287 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5287) = 3 ^ 9 * m + 12707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5287.1, data_13_5287.2]

end Collatz.Research.StoppingAtlas.Batch0811
