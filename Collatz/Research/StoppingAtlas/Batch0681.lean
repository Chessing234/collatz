import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0681

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3276. -/
theorem bounds_13_3276 : exactInterval 13 3276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3276 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3276) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3276 : oddCount 3276 13 = 5 ∧ acceleratedOrbit 13 3276 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3276 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3276) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3276.1, data_13_3276.2]

/-- Complete interval computation for depth 13, residue 3277. -/
theorem bounds_13_3277 : exactInterval 13 3277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3277 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3277) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3277 : oddCount 3277 13 = 5 ∧ acceleratedOrbit 13 3277 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3277 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3277) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3277.1, data_13_3277.2]

/-- Complete interval computation for depth 13, residue 3278. -/
theorem bounds_13_3278 : exactInterval 13 3278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3278 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3278) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3278 : oddCount 3278 13 = 9 ∧ acceleratedOrbit 13 3278 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3278 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3278) = 3 ^ 9 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3278.1, data_13_3278.2]

/-- Complete interval computation for depth 13, residue 3279. -/
theorem bounds_13_3279 : exactInterval 13 3279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3279 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3279) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3279 : oddCount 3279 13 = 9 ∧ acceleratedOrbit 13 3279 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3279 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3279) = 3 ^ 9 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3279.1, data_13_3279.2]

/-- Complete interval computation for depth 13, residue 3280. -/
theorem bounds_13_3280 : exactInterval 13 3280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3280 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3280) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3280 : oddCount 3280 13 = 3 ∧ acceleratedOrbit 13 3280 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3280 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3280) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3280.1, data_13_3280.2]

/-- Complete interval computation for depth 13, residue 3281. -/
theorem bounds_13_3281 : exactInterval 13 3281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3281 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3281) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3281 : oddCount 3281 13 = 8 ∧ acceleratedOrbit 13 3281 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3281 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3281) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3281.1, data_13_3281.2]

/-- Complete interval computation for depth 13, residue 3282. -/
theorem bounds_13_3282 : exactInterval 13 3282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3282 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3282) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3282 : oddCount 3282 13 = 8 ∧ acceleratedOrbit 13 3282 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3282 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3282) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3282.1, data_13_3282.2]

/-- Complete interval computation for depth 13, residue 3283. -/
theorem bounds_13_3283 : exactInterval 13 3283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3283 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3283) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3283 : oddCount 3283 13 = 8 ∧ acceleratedOrbit 13 3283 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3283 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3283) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3283.1, data_13_3283.2]

/-- Complete interval computation for depth 13, residue 3284. -/
theorem bounds_13_3284 : exactInterval 13 3284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3284 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3284) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3284 : oddCount 3284 13 = 3 ∧ acceleratedOrbit 13 3284 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3284 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3284) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3284.1, data_13_3284.2]

/-- Complete interval computation for depth 13, residue 3285. -/
theorem bounds_13_3285 : exactInterval 13 3285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3285 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3285) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3285 : oddCount 3285 13 = 3 ∧ acceleratedOrbit 13 3285 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3285 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3285) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3285.1, data_13_3285.2]

/-- Complete interval computation for depth 13, residue 3286. -/
theorem bounds_13_3286 : exactInterval 13 3286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3286 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3286) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3286 : oddCount 3286 13 = 8 ∧ acceleratedOrbit 13 3286 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3286 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3286) = 3 ^ 8 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3286.1, data_13_3286.2]

/-- Complete interval computation for depth 13, residue 3287. -/
theorem bounds_13_3287 : exactInterval 13 3287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3287 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3287) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3287 : oddCount 3287 13 = 8 ∧ acceleratedOrbit 13 3287 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3287 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3287) = 3 ^ 8 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3287.1, data_13_3287.2]

/-- Complete interval computation for depth 13, residue 3288. -/
theorem bounds_13_3288 : exactInterval 13 3288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3288 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3288) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3288 : oddCount 3288 13 = 7 ∧ acceleratedOrbit 13 3288 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3288 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3288) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3288.1, data_13_3288.2]

/-- Complete interval computation for depth 13, residue 3289. -/
theorem bounds_13_3289 : exactInterval 13 3289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3289 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3289) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3289 : oddCount 3289 13 = 7 ∧ acceleratedOrbit 13 3289 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3289 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3289) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3289.1, data_13_3289.2]

/-- Complete interval computation for depth 13, residue 3290. -/
theorem bounds_13_3290 : exactInterval 13 3290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3290 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3290) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3290 : oddCount 3290 13 = 7 ∧ acceleratedOrbit 13 3290 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3290 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3290) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3290.1, data_13_3290.2]

/-- Complete interval computation for depth 13, residue 3291. -/
theorem bounds_13_3291 : exactInterval 13 3291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3291 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3291) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3291 : oddCount 3291 13 = 6 ∧ acceleratedOrbit 13 3291 = 293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3291 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3291) = 3 ^ 6 * m + 293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3291.1, data_13_3291.2]

end Collatz.Research.StoppingAtlas.Batch0681
