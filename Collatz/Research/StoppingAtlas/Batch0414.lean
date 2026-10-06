import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0414

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3271. -/
theorem bounds_12_3271 : exactInterval 12 3271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3271 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3271) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3271 : oddCount 3271 12 = 7 ∧ acceleratedOrbit 12 3271 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3271 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3271) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3271.1, data_12_3271.2]

/-- Complete interval computation for depth 12, residue 3272. -/
theorem bounds_12_3272 : exactInterval 12 3272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3272 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3272) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3272 : oddCount 3272 12 = 4 ∧ acceleratedOrbit 12 3272 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3272 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3272) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3272.1, data_12_3272.2]

/-- Complete interval computation for depth 12, residue 3273. -/
theorem bounds_12_3273 : exactInterval 12 3273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3273 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3273) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3273 : oddCount 3273 12 = 6 ∧ acceleratedOrbit 12 3273 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3273 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3273) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3273.1, data_12_3273.2]

/-- Complete interval computation for depth 12, residue 3274. -/
theorem bounds_12_3274 : exactInterval 12 3274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3274 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3274) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3274 : oddCount 3274 12 = 4 ∧ acceleratedOrbit 12 3274 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3274 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3274) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3274.1, data_12_3274.2]

/-- Complete interval computation for depth 12, residue 3275. -/
theorem bounds_12_3275 : exactInterval 12 3275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3275 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3275) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3275 : oddCount 3275 12 = 6 ∧ acceleratedOrbit 12 3275 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3275 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3275) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3275.1, data_12_3275.2]

/-- Complete interval computation for depth 12, residue 3276. -/
theorem bounds_12_3276 : exactInterval 12 3276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3276 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3276) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3276 : oddCount 3276 12 = 4 ∧ acceleratedOrbit 12 3276 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3276 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3276) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3276.1, data_12_3276.2]

/-- Complete interval computation for depth 12, residue 3277. -/
theorem bounds_12_3277 : exactInterval 12 3277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3277 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3277) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3277 : oddCount 3277 12 = 4 ∧ acceleratedOrbit 12 3277 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3277 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3277) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3277.1, data_12_3277.2]

/-- Complete interval computation for depth 12, residue 3278. -/
theorem bounds_12_3278 : exactInterval 12 3278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3278 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3278) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3278 : oddCount 3278 12 = 8 ∧ acceleratedOrbit 12 3278 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3278 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3278) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3278.1, data_12_3278.2]

/-- Complete interval computation for depth 12, residue 3279. -/
theorem bounds_12_3279 : exactInterval 12 3279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3279 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3279) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3279 : oddCount 3279 12 = 8 ∧ acceleratedOrbit 12 3279 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3279 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3279) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3279.1, data_12_3279.2]

/-- Complete interval computation for depth 12, residue 3280. -/
theorem bounds_12_3280 : exactInterval 12 3280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3280 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3280) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3280 : oddCount 3280 12 = 3 ∧ acceleratedOrbit 12 3280 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3280 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3280) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3280.1, data_12_3280.2]

/-- Complete interval computation for depth 12, residue 3281. -/
theorem bounds_12_3281 : exactInterval 12 3281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3281 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3281) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3281 : oddCount 3281 12 = 8 ∧ acceleratedOrbit 12 3281 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3281 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3281) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3281.1, data_12_3281.2]

/-- Complete interval computation for depth 12, residue 3282. -/
theorem bounds_12_3282 : exactInterval 12 3282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3282 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3282) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3282 : oddCount 3282 12 = 8 ∧ acceleratedOrbit 12 3282 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3282 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3282) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3282.1, data_12_3282.2]

/-- Complete interval computation for depth 12, residue 3283. -/
theorem bounds_12_3283 : exactInterval 12 3283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3283 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3283) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3283 : oddCount 3283 12 = 8 ∧ acceleratedOrbit 12 3283 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3283 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3283) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3283.1, data_12_3283.2]

/-- Complete interval computation for depth 12, residue 3284. -/
theorem bounds_12_3284 : exactInterval 12 3284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3284 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3284) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3284 : oddCount 3284 12 = 3 ∧ acceleratedOrbit 12 3284 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3284 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3284) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3284.1, data_12_3284.2]

/-- Complete interval computation for depth 12, residue 3285. -/
theorem bounds_12_3285 : exactInterval 12 3285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3285 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3285) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3285 : oddCount 3285 12 = 3 ∧ acceleratedOrbit 12 3285 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3285 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3285) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3285.1, data_12_3285.2]

/-- Complete interval computation for depth 12, residue 3286. -/
theorem bounds_12_3286 : exactInterval 12 3286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3286 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3286) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3286 : oddCount 3286 12 = 7 ∧ acceleratedOrbit 12 3286 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3286 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3286) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3286.1, data_12_3286.2]

end Collatz.Research.StoppingAtlas.Batch0414
