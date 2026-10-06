import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0101

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3276. -/
theorem bounds_15_3276 : exactInterval 15 3276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3276 : oddCount 3276 15 = 6 ∧ acceleratedOrbit 15 3276 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3276) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3276.1, data_15_3276.2]

/-- Complete interval computation for depth 15, residue 3277. -/
theorem bounds_15_3277 : exactInterval 15 3277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3277 : oddCount 3277 15 = 6 ∧ acceleratedOrbit 15 3277 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3277) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3277.1, data_15_3277.2]

/-- Complete interval computation for depth 15, residue 3278. -/
theorem bounds_15_3278 : exactInterval 15 3278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3278 : oddCount 3278 15 = 11 ∧ acceleratedOrbit 15 3278 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3278) = 3 ^ 11 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3278.1, data_15_3278.2]

/-- Complete interval computation for depth 15, residue 3279. -/
theorem bounds_15_3279 : exactInterval 15 3279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3279 : oddCount 3279 15 = 11 ∧ acceleratedOrbit 15 3279 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3279) = 3 ^ 11 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3279.1, data_15_3279.2]

/-- Complete interval computation for depth 15, residue 3280. -/
theorem bounds_15_3280 : exactInterval 15 3280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3280 : oddCount 3280 15 = 5 ∧ acceleratedOrbit 15 3280 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3280) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3280.1, data_15_3280.2]

/-- Complete interval computation for depth 15, residue 3281. -/
theorem bounds_15_3281 : exactInterval 15 3281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3281 : oddCount 3281 15 = 8 ∧ acceleratedOrbit 15 3281 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3281) = 3 ^ 8 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3281.1, data_15_3281.2]

/-- Complete interval computation for depth 15, residue 3282. -/
theorem bounds_15_3282 : exactInterval 15 3282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3282 : oddCount 3282 15 = 8 ∧ acceleratedOrbit 15 3282 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3282) = 3 ^ 8 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3282.1, data_15_3282.2]

/-- Complete interval computation for depth 15, residue 3283. -/
theorem bounds_15_3283 : exactInterval 15 3283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3283 : oddCount 3283 15 = 8 ∧ acceleratedOrbit 15 3283 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3283) = 3 ^ 8 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3283.1, data_15_3283.2]

/-- Complete interval computation for depth 15, residue 3284. -/
theorem bounds_15_3284 : exactInterval 15 3284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3284 : oddCount 3284 15 = 5 ∧ acceleratedOrbit 15 3284 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3284) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3284.1, data_15_3284.2]

/-- Complete interval computation for depth 15, residue 3285. -/
theorem bounds_15_3285 : exactInterval 15 3285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3285 : oddCount 3285 15 = 5 ∧ acceleratedOrbit 15 3285 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3285) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3285.1, data_15_3285.2]

/-- Complete interval computation for depth 15, residue 3286. -/
theorem bounds_15_3286 : exactInterval 15 3286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3286 : oddCount 3286 15 = 8 ∧ acceleratedOrbit 15 3286 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3286) = 3 ^ 8 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3286.1, data_15_3286.2]

/-- Complete interval computation for depth 15, residue 3287. -/
theorem bounds_15_3287 : exactInterval 15 3287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3287 : oddCount 3287 15 = 8 ∧ acceleratedOrbit 15 3287 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3287) = 3 ^ 8 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3287.1, data_15_3287.2]

/-- Complete interval computation for depth 15, residue 3288. -/
theorem bounds_15_3288 : exactInterval 15 3288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3288 : oddCount 3288 15 = 8 ∧ acceleratedOrbit 15 3288 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3288) = 3 ^ 8 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3288.1, data_15_3288.2]

/-- Complete interval computation for depth 15, residue 3289. -/
theorem bounds_15_3289 : exactInterval 15 3289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3289 : oddCount 3289 15 = 8 ∧ acceleratedOrbit 15 3289 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3289) = 3 ^ 8 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3289.1, data_15_3289.2]

/-- Complete interval computation for depth 15, residue 3290. -/
theorem bounds_15_3290 : exactInterval 15 3290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3290 : oddCount 3290 15 = 8 ∧ acceleratedOrbit 15 3290 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3290) = 3 ^ 8 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3290.1, data_15_3290.2]

/-- Complete interval computation for depth 15, residue 3291. -/
theorem bounds_15_3291 : exactInterval 15 3291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3291 : oddCount 3291 15 = 7 ∧ acceleratedOrbit 15 3291 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3291) = 3 ^ 7 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3291.1, data_15_3291.2]

/-- Complete interval computation for depth 15, residue 3292. -/
theorem bounds_15_3292 : exactInterval 15 3292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3292 : oddCount 3292 15 = 8 ∧ acceleratedOrbit 15 3292 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3292) = 3 ^ 8 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3292.1, data_15_3292.2]

/-- Complete interval computation for depth 15, residue 3293. -/
theorem bounds_15_3293 : exactInterval 15 3293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3293 : oddCount 3293 15 = 8 ∧ acceleratedOrbit 15 3293 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3293) = 3 ^ 8 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3293.1, data_15_3293.2]

/-- Complete interval computation for depth 15, residue 3294. -/
theorem bounds_15_3294 : exactInterval 15 3294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3294 : oddCount 3294 15 = 7 ∧ acceleratedOrbit 15 3294 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3294) = 3 ^ 7 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3294.1, data_15_3294.2]

/-- Complete interval computation for depth 15, residue 3295. -/
theorem bounds_15_3295 : exactInterval 15 3295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3295 : oddCount 3295 15 = 7 ∧ acceleratedOrbit 15 3295 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3295) = 3 ^ 7 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3295.1, data_15_3295.2]

/-- Complete interval computation for depth 15, residue 3296. -/
theorem bounds_15_3296 : exactInterval 15 3296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3296 : oddCount 3296 15 = 8 ∧ acceleratedOrbit 15 3296 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3296) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3296.1, data_15_3296.2]

/-- Complete interval computation for depth 15, residue 3297. -/
theorem bounds_15_3297 : exactInterval 15 3297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3297 : oddCount 3297 15 = 9 ∧ acceleratedOrbit 15 3297 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3297) = 3 ^ 9 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3297.1, data_15_3297.2]

/-- Complete interval computation for depth 15, residue 3298. -/
theorem bounds_15_3298 : exactInterval 15 3298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3298 : oddCount 3298 15 = 5 ∧ acceleratedOrbit 15 3298 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3298) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3298.1, data_15_3298.2]

/-- Complete interval computation for depth 15, residue 3299. -/
theorem bounds_15_3299 : exactInterval 15 3299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3299 : oddCount 3299 15 = 5 ∧ acceleratedOrbit 15 3299 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3299) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3299.1, data_15_3299.2]

/-- Complete interval computation for depth 15, residue 3300. -/
theorem bounds_15_3300 : exactInterval 15 3300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3300 : oddCount 3300 15 = 7 ∧ acceleratedOrbit 15 3300 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3300) = 3 ^ 7 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3300.1, data_15_3300.2]

/-- Complete interval computation for depth 15, residue 3301. -/
theorem bounds_15_3301 : exactInterval 15 3301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3301 : oddCount 3301 15 = 7 ∧ acceleratedOrbit 15 3301 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3301) = 3 ^ 7 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3301.1, data_15_3301.2]

/-- Complete interval computation for depth 15, residue 3302. -/
theorem bounds_15_3302 : exactInterval 15 3302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3302 : oddCount 3302 15 = 7 ∧ acceleratedOrbit 15 3302 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3302) = 3 ^ 7 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3302.1, data_15_3302.2]

/-- Complete interval computation for depth 15, residue 3303. -/
theorem bounds_15_3303 : exactInterval 15 3303 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3303) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3303 : oddCount 3303 15 = 9 ∧ acceleratedOrbit 15 3303 = 1985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3303) = 3 ^ 9 * m + 1985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3303.1, data_15_3303.2]

/-- Complete interval computation for depth 15, residue 3304. -/
theorem bounds_15_3304 : exactInterval 15 3304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3304 : oddCount 3304 15 = 8 ∧ acceleratedOrbit 15 3304 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3304) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3304.1, data_15_3304.2]

/-- Complete interval computation for depth 15, residue 3305. -/
theorem bounds_15_3305 : exactInterval 15 3305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3305 : oddCount 3305 15 = 9 ∧ acceleratedOrbit 15 3305 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3305) = 3 ^ 9 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3305.1, data_15_3305.2]

/-- Complete interval computation for depth 15, residue 3306. -/
theorem bounds_15_3306 : exactInterval 15 3306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3306 : oddCount 3306 15 = 8 ∧ acceleratedOrbit 15 3306 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3306) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3306.1, data_15_3306.2]

/-- Complete interval computation for depth 15, residue 3307. -/
theorem bounds_15_3307 : exactInterval 15 3307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3307 : oddCount 3307 15 = 11 ∧ acceleratedOrbit 15 3307 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3307) = 3 ^ 11 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3307.1, data_15_3307.2]

/-- Complete interval computation for depth 15, residue 3308. -/
theorem bounds_15_3308 : exactInterval 15 3308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3308 : oddCount 3308 15 = 6 ∧ acceleratedOrbit 15 3308 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3308) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3308.1, data_15_3308.2]

end Collatz.Research.PassageAtlas.Batch0101
