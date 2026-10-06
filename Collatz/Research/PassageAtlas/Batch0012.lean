import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0012

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 360. -/
theorem bounds_15_360 : exactInterval 15 360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_360 : oddCount 360 15 = 4 ∧ acceleratedOrbit 15 360 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 360) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_360.1, data_15_360.2]

/-- Complete interval computation for depth 15, residue 361. -/
theorem bounds_15_361 : exactInterval 15 361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_361 : oddCount 361 15 = 8 ∧ acceleratedOrbit 15 361 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 361) = 3 ^ 8 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_361.1, data_15_361.2]

/-- Complete interval computation for depth 15, residue 362. -/
theorem bounds_15_362 : exactInterval 15 362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_362 : oddCount 362 15 = 4 ∧ acceleratedOrbit 15 362 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 362) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_362.1, data_15_362.2]

/-- Complete interval computation for depth 15, residue 363. -/
theorem bounds_15_363 : exactInterval 15 363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_363 : oddCount 363 15 = 8 ∧ acceleratedOrbit 15 363 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 363) = 3 ^ 8 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_363.1, data_15_363.2]

/-- Complete interval computation for depth 15, residue 364. -/
theorem bounds_15_364 : exactInterval 15 364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_364 : oddCount 364 15 = 10 ∧ acceleratedOrbit 15 364 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 364) = 3 ^ 10 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_364.1, data_15_364.2]

/-- Complete interval computation for depth 15, residue 365. -/
theorem bounds_15_365 : exactInterval 15 365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_365 : oddCount 365 15 = 10 ∧ acceleratedOrbit 15 365 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 365) = 3 ^ 10 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_365.1, data_15_365.2]

/-- Complete interval computation for depth 15, residue 366. -/
theorem bounds_15_366 : exactInterval 15 366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_366 : oddCount 366 15 = 10 ∧ acceleratedOrbit 15 366 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 366) = 3 ^ 10 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_366.1, data_15_366.2]

/-- Complete interval computation for depth 15, residue 367. -/
theorem bounds_15_367 : exactInterval 15 367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_367 : oddCount 367 15 = 8 ∧ acceleratedOrbit 15 367 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 367) = 3 ^ 8 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_367.1, data_15_367.2]

/-- Complete interval computation for depth 15, residue 368. -/
theorem bounds_15_368 : exactInterval 15 368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_368 : oddCount 368 15 = 4 ∧ acceleratedOrbit 15 368 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 368) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_368.1, data_15_368.2]

/-- Complete interval computation for depth 15, residue 369. -/
theorem bounds_15_369 : exactInterval 15 369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_369 : oddCount 369 15 = 4 ∧ acceleratedOrbit 15 369 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 369) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_369.1, data_15_369.2]

/-- Complete interval computation for depth 15, residue 370. -/
theorem bounds_15_370 : exactInterval 15 370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_370 : oddCount 370 15 = 8 ∧ acceleratedOrbit 15 370 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 370) = 3 ^ 8 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_370.1, data_15_370.2]

/-- Complete interval computation for depth 15, residue 371. -/
theorem bounds_15_371 : exactInterval 15 371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_371 : oddCount 371 15 = 8 ∧ acceleratedOrbit 15 371 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 371) = 3 ^ 8 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_371.1, data_15_371.2]

/-- Complete interval computation for depth 15, residue 372. -/
theorem bounds_15_372 : exactInterval 15 372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_372 : oddCount 372 15 = 4 ∧ acceleratedOrbit 15 372 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 372) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_372.1, data_15_372.2]

/-- Complete interval computation for depth 15, residue 373. -/
theorem bounds_15_373 : exactInterval 15 373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_373 : oddCount 373 15 = 4 ∧ acceleratedOrbit 15 373 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 373) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_373.1, data_15_373.2]

/-- Complete interval computation for depth 15, residue 374. -/
theorem bounds_15_374 : exactInterval 15 374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_374 : oddCount 374 15 = 8 ∧ acceleratedOrbit 15 374 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 374) = 3 ^ 8 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_374.1, data_15_374.2]

/-- Complete interval computation for depth 15, residue 375. -/
theorem bounds_15_375 : exactInterval 15 375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_375 : oddCount 375 15 = 8 ∧ acceleratedOrbit 15 375 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 375) = 3 ^ 8 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_375.1, data_15_375.2]

/-- Complete interval computation for depth 15, residue 376. -/
theorem bounds_15_376 : exactInterval 15 376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_376 : oddCount 376 15 = 9 ∧ acceleratedOrbit 15 376 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 376) = 3 ^ 9 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_376.1, data_15_376.2]

/-- Complete interval computation for depth 15, residue 377. -/
theorem bounds_15_377 : exactInterval 15 377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_377 : oddCount 377 15 = 11 ∧ acceleratedOrbit 15 377 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 377) = 3 ^ 11 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_377.1, data_15_377.2]

/-- Complete interval computation for depth 15, residue 378. -/
theorem bounds_15_378 : exactInterval 15 378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_378 : oddCount 378 15 = 9 ∧ acceleratedOrbit 15 378 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 378) = 3 ^ 9 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_378.1, data_15_378.2]

/-- Complete interval computation for depth 15, residue 379. -/
theorem bounds_15_379 : exactInterval 15 379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_379 : oddCount 379 15 = 10 ∧ acceleratedOrbit 15 379 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 379) = 3 ^ 10 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_379.1, data_15_379.2]

/-- Complete interval computation for depth 15, residue 380. -/
theorem bounds_15_380 : exactInterval 15 380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_380 : oddCount 380 15 = 9 ∧ acceleratedOrbit 15 380 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 380) = 3 ^ 9 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_380.1, data_15_380.2]

/-- Complete interval computation for depth 15, residue 381. -/
theorem bounds_15_381 : exactInterval 15 381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_381 : oddCount 381 15 = 9 ∧ acceleratedOrbit 15 381 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 381) = 3 ^ 9 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_381.1, data_15_381.2]

/-- Complete interval computation for depth 15, residue 382. -/
theorem bounds_15_382 : exactInterval 15 382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_382 : oddCount 382 15 = 8 ∧ acceleratedOrbit 15 382 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 382) = 3 ^ 8 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_382.1, data_15_382.2]

/-- Complete interval computation for depth 15, residue 383. -/
theorem bounds_15_383 : exactInterval 15 383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_383 : oddCount 383 15 = 8 ∧ acceleratedOrbit 15 383 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 383) = 3 ^ 8 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_383.1, data_15_383.2]

/-- Complete interval computation for depth 15, residue 384. -/
theorem bounds_15_384 : exactInterval 15 384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_384 : oddCount 384 15 = 4 ∧ acceleratedOrbit 15 384 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 384) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_384.1, data_15_384.2]

/-- Complete interval computation for depth 15, residue 385. -/
theorem bounds_15_385 : exactInterval 15 385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_385 : oddCount 385 15 = 8 ∧ acceleratedOrbit 15 385 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 385) = 3 ^ 8 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_385.1, data_15_385.2]

/-- Complete interval computation for depth 15, residue 386. -/
theorem bounds_15_386 : exactInterval 15 386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_386 : oddCount 386 15 = 9 ∧ acceleratedOrbit 15 386 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 386) = 3 ^ 9 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_386.1, data_15_386.2]

/-- Complete interval computation for depth 15, residue 387. -/
theorem bounds_15_387 : exactInterval 15 387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_387 : oddCount 387 15 = 9 ∧ acceleratedOrbit 15 387 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 387) = 3 ^ 9 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_387.1, data_15_387.2]

/-- Complete interval computation for depth 15, residue 388. -/
theorem bounds_15_388 : exactInterval 15 388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_388 : oddCount 388 15 = 9 ∧ acceleratedOrbit 15 388 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 388) = 3 ^ 9 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_388.1, data_15_388.2]

/-- Complete interval computation for depth 15, residue 389. -/
theorem bounds_15_389 : exactInterval 15 389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_389 : oddCount 389 15 = 9 ∧ acceleratedOrbit 15 389 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 389) = 3 ^ 9 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_389.1, data_15_389.2]

/-- Complete interval computation for depth 15, residue 390. -/
theorem bounds_15_390 : exactInterval 15 390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_390 : oddCount 390 15 = 9 ∧ acceleratedOrbit 15 390 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 390) = 3 ^ 9 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_390.1, data_15_390.2]

/-- Complete interval computation for depth 15, residue 391. -/
theorem bounds_15_391 : exactInterval 15 391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_391 : oddCount 391 15 = 9 ∧ acceleratedOrbit 15 391 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 391) = 3 ^ 9 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_391.1, data_15_391.2]

/-- Complete interval computation for depth 15, residue 392. -/
theorem bounds_15_392 : exactInterval 15 392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_392 : oddCount 392 15 = 6 ∧ acceleratedOrbit 15 392 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 392) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_392.1, data_15_392.2]

end Collatz.Research.PassageAtlas.Batch0012
