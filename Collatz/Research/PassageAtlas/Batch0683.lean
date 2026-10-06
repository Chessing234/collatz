import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0683

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22347. -/
theorem bounds_15_22347 : exactInterval 15 22347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22347 : oddCount 22347 15 = 5 ∧ acceleratedOrbit 15 22347 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22347) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22347.1, data_15_22347.2]

/-- Complete interval computation for depth 15, residue 22348. -/
theorem bounds_15_22348 : exactInterval 15 22348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22348 : oddCount 22348 15 = 8 ∧ acceleratedOrbit 15 22348 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22348) = 3 ^ 8 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22348.1, data_15_22348.2]

/-- Complete interval computation for depth 15, residue 22349. -/
theorem bounds_15_22349 : exactInterval 15 22349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22349 : oddCount 22349 15 = 8 ∧ acceleratedOrbit 15 22349 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22349) = 3 ^ 8 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22349.1, data_15_22349.2]

/-- Complete interval computation for depth 15, residue 22350. -/
theorem bounds_15_22350 : exactInterval 15 22350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22350 : oddCount 22350 15 = 10 ∧ acceleratedOrbit 15 22350 = 40283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22350) = 3 ^ 10 * m + 40283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22350.1, data_15_22350.2]

/-- Complete interval computation for depth 15, residue 22351. -/
theorem bounds_15_22351 : exactInterval 15 22351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22351 : oddCount 22351 15 = 10 ∧ acceleratedOrbit 15 22351 = 40283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22351) = 3 ^ 10 * m + 40283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22351.1, data_15_22351.2]

/-- Complete interval computation for depth 15, residue 22352. -/
theorem bounds_15_22352 : exactInterval 15 22352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22352 : oddCount 22352 15 = 4 ∧ acceleratedOrbit 15 22352 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22352) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22352.1, data_15_22352.2]

/-- Complete interval computation for depth 15, residue 22353. -/
theorem bounds_15_22353 : exactInterval 15 22353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22353 : oddCount 22353 15 = 8 ∧ acceleratedOrbit 15 22353 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22353) = 3 ^ 8 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22353.1, data_15_22353.2]

/-- Complete interval computation for depth 15, residue 22354. -/
theorem bounds_15_22354 : exactInterval 15 22354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22354 : oddCount 22354 15 = 9 ∧ acceleratedOrbit 15 22354 = 13430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22354) = 3 ^ 9 * m + 13430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22354.1, data_15_22354.2]

/-- Complete interval computation for depth 15, residue 22355. -/
theorem bounds_15_22355 : exactInterval 15 22355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22355 : oddCount 22355 15 = 9 ∧ acceleratedOrbit 15 22355 = 13430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22355) = 3 ^ 9 * m + 13430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22355.1, data_15_22355.2]

/-- Complete interval computation for depth 15, residue 22356. -/
theorem bounds_15_22356 : exactInterval 15 22356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22356 : oddCount 22356 15 = 4 ∧ acceleratedOrbit 15 22356 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22356) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22356.1, data_15_22356.2]

/-- Complete interval computation for depth 15, residue 22357. -/
theorem bounds_15_22357 : exactInterval 15 22357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22357 : oddCount 22357 15 = 4 ∧ acceleratedOrbit 15 22357 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22357) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22357.1, data_15_22357.2]

/-- Complete interval computation for depth 15, residue 22358. -/
theorem bounds_15_22358 : exactInterval 15 22358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22358 : oddCount 22358 15 = 7 ∧ acceleratedOrbit 15 22358 = 1493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22358) = 3 ^ 7 * m + 1493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22358.1, data_15_22358.2]

/-- Complete interval computation for depth 15, residue 22359. -/
theorem bounds_15_22359 : exactInterval 15 22359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22359 : oddCount 22359 15 = 7 ∧ acceleratedOrbit 15 22359 = 1493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22359) = 3 ^ 7 * m + 1493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22359.1, data_15_22359.2]

/-- Complete interval computation for depth 15, residue 22360. -/
theorem bounds_15_22360 : exactInterval 15 22360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22360 : oddCount 22360 15 = 8 ∧ acceleratedOrbit 15 22360 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22360) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22360.1, data_15_22360.2]

/-- Complete interval computation for depth 15, residue 22361. -/
theorem bounds_15_22361 : exactInterval 15 22361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22361 : oddCount 22361 15 = 8 ∧ acceleratedOrbit 15 22361 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22361) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22361.1, data_15_22361.2]

/-- Complete interval computation for depth 15, residue 22362. -/
theorem bounds_15_22362 : exactInterval 15 22362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22362 : oddCount 22362 15 = 8 ∧ acceleratedOrbit 15 22362 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22362) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22362.1, data_15_22362.2]

/-- Complete interval computation for depth 15, residue 22363. -/
theorem bounds_15_22363 : exactInterval 15 22363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22363 : oddCount 22363 15 = 8 ∧ acceleratedOrbit 15 22363 = 4478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22363) = 3 ^ 8 * m + 4478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22363.1, data_15_22363.2]

/-- Complete interval computation for depth 15, residue 22364. -/
theorem bounds_15_22364 : exactInterval 15 22364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22364 : oddCount 22364 15 = 8 ∧ acceleratedOrbit 15 22364 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22364) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22364.1, data_15_22364.2]

/-- Complete interval computation for depth 15, residue 22365. -/
theorem bounds_15_22365 : exactInterval 15 22365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22365 : oddCount 22365 15 = 8 ∧ acceleratedOrbit 15 22365 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22365) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22365.1, data_15_22365.2]

/-- Complete interval computation for depth 15, residue 22366. -/
theorem bounds_15_22366 : exactInterval 15 22366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22366 : oddCount 22366 15 = 8 ∧ acceleratedOrbit 15 22366 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22366) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22366.1, data_15_22366.2]

/-- Complete interval computation for depth 15, residue 22367. -/
theorem bounds_15_22367 : exactInterval 15 22367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22367 : oddCount 22367 15 = 8 ∧ acceleratedOrbit 15 22367 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22367) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22367.1, data_15_22367.2]

/-- Complete interval computation for depth 15, residue 22368. -/
theorem bounds_15_22368 : exactInterval 15 22368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22368 : oddCount 22368 15 = 6 ∧ acceleratedOrbit 15 22368 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22368) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22368.1, data_15_22368.2]

/-- Complete interval computation for depth 15, residue 22369. -/
theorem bounds_15_22369 : exactInterval 15 22369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22369 : oddCount 22369 15 = 9 ∧ acceleratedOrbit 15 22369 = 13439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22369) = 3 ^ 9 * m + 13439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22369.1, data_15_22369.2]

/-- Complete interval computation for depth 15, residue 22370. -/
theorem bounds_15_22370 : exactInterval 15 22370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22370 : oddCount 22370 15 = 6 ∧ acceleratedOrbit 15 22370 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22370) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22370.1, data_15_22370.2]

/-- Complete interval computation for depth 15, residue 22371. -/
theorem bounds_15_22371 : exactInterval 15 22371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22371 : oddCount 22371 15 = 6 ∧ acceleratedOrbit 15 22371 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22371) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22371.1, data_15_22371.2]

/-- Complete interval computation for depth 15, residue 22372. -/
theorem bounds_15_22372 : exactInterval 15 22372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22372 : oddCount 22372 15 = 6 ∧ acceleratedOrbit 15 22372 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22372) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22372.1, data_15_22372.2]

/-- Complete interval computation for depth 15, residue 22373. -/
theorem bounds_15_22373 : exactInterval 15 22373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22373 : oddCount 22373 15 = 6 ∧ acceleratedOrbit 15 22373 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22373) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22373.1, data_15_22373.2]

/-- Complete interval computation for depth 15, residue 22374. -/
theorem bounds_15_22374 : exactInterval 15 22374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22374 : oddCount 22374 15 = 6 ∧ acceleratedOrbit 15 22374 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22374) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22374.1, data_15_22374.2]

/-- Complete interval computation for depth 15, residue 22375. -/
theorem bounds_15_22375 : exactInterval 15 22375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22375 : oddCount 22375 15 = 12 ∧ acceleratedOrbit 15 22375 = 362906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22375) = 3 ^ 12 * m + 362906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22375.1, data_15_22375.2]

/-- Complete interval computation for depth 15, residue 22376. -/
theorem bounds_15_22376 : exactInterval 15 22376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22376 : oddCount 22376 15 = 6 ∧ acceleratedOrbit 15 22376 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22376) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22376.1, data_15_22376.2]

/-- Complete interval computation for depth 15, residue 22377. -/
theorem bounds_15_22377 : exactInterval 15 22377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22377 : oddCount 22377 15 = 9 ∧ acceleratedOrbit 15 22377 = 13445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22377) = 3 ^ 9 * m + 13445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22377.1, data_15_22377.2]

/-- Complete interval computation for depth 15, residue 22378. -/
theorem bounds_15_22378 : exactInterval 15 22378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22378 : oddCount 22378 15 = 6 ∧ acceleratedOrbit 15 22378 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22378) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22378.1, data_15_22378.2]

/-- Complete interval computation for depth 15, residue 22379. -/
theorem bounds_15_22379 : exactInterval 15 22379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22379 : oddCount 22379 15 = 10 ∧ acceleratedOrbit 15 22379 = 40337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22379) = 3 ^ 10 * m + 40337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22379.1, data_15_22379.2]

end Collatz.Research.PassageAtlas.Batch0683
