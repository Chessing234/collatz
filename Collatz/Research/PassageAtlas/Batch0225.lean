import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0225

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7340. -/
theorem bounds_15_7340 : exactInterval 15 7340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7340 : oddCount 7340 15 = 6 ∧ acceleratedOrbit 15 7340 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7340) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7340.1, data_15_7340.2]

/-- Complete interval computation for depth 15, residue 7341. -/
theorem bounds_15_7341 : exactInterval 15 7341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7341 : oddCount 7341 15 = 6 ∧ acceleratedOrbit 15 7341 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7341) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7341.1, data_15_7341.2]

/-- Complete interval computation for depth 15, residue 7342. -/
theorem bounds_15_7342 : exactInterval 15 7342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7342 : oddCount 7342 15 = 6 ∧ acceleratedOrbit 15 7342 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7342) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7342.1, data_15_7342.2]

/-- Complete interval computation for depth 15, residue 7343. -/
theorem bounds_15_7343 : exactInterval 15 7343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7343 : oddCount 7343 15 = 9 ∧ acceleratedOrbit 15 7343 = 4412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7343) = 3 ^ 9 * m + 4412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7343.1, data_15_7343.2]

/-- Complete interval computation for depth 15, residue 7344. -/
theorem bounds_15_7344 : exactInterval 15 7344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7344 : oddCount 7344 15 = 5 ∧ acceleratedOrbit 15 7344 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7344) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7344.1, data_15_7344.2]

/-- Complete interval computation for depth 15, residue 7345. -/
theorem bounds_15_7345 : exactInterval 15 7345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7345 : oddCount 7345 15 = 7 ∧ acceleratedOrbit 15 7345 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7345) = 3 ^ 7 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7345.1, data_15_7345.2]

/-- Complete interval computation for depth 15, residue 7346. -/
theorem bounds_15_7346 : exactInterval 15 7346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7346 : oddCount 7346 15 = 7 ∧ acceleratedOrbit 15 7346 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7346) = 3 ^ 7 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7346.1, data_15_7346.2]

/-- Complete interval computation for depth 15, residue 7347. -/
theorem bounds_15_7347 : exactInterval 15 7347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7347 : oddCount 7347 15 = 7 ∧ acceleratedOrbit 15 7347 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7347) = 3 ^ 7 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7347.1, data_15_7347.2]

/-- Complete interval computation for depth 15, residue 7348. -/
theorem bounds_15_7348 : exactInterval 15 7348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7348 : oddCount 7348 15 = 5 ∧ acceleratedOrbit 15 7348 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7348) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7348.1, data_15_7348.2]

/-- Complete interval computation for depth 15, residue 7349. -/
theorem bounds_15_7349 : exactInterval 15 7349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7349 : oddCount 7349 15 = 5 ∧ acceleratedOrbit 15 7349 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7349) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7349.1, data_15_7349.2]

/-- Complete interval computation for depth 15, residue 7350. -/
theorem bounds_15_7350 : exactInterval 15 7350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7350 : oddCount 7350 15 = 9 ∧ acceleratedOrbit 15 7350 = 4418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7350) = 3 ^ 9 * m + 4418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7350.1, data_15_7350.2]

/-- Complete interval computation for depth 15, residue 7351. -/
theorem bounds_15_7351 : exactInterval 15 7351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7351 : oddCount 7351 15 = 9 ∧ acceleratedOrbit 15 7351 = 4418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7351) = 3 ^ 9 * m + 4418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7351.1, data_15_7351.2]

/-- Complete interval computation for depth 15, residue 7352. -/
theorem bounds_15_7352 : exactInterval 15 7352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7352 : oddCount 7352 15 = 5 ∧ acceleratedOrbit 15 7352 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7352) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7352.1, data_15_7352.2]

/-- Complete interval computation for depth 15, residue 7353. -/
theorem bounds_15_7353 : exactInterval 15 7353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7353 : oddCount 7353 15 = 7 ∧ acceleratedOrbit 15 7353 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7353) = 3 ^ 7 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7353.1, data_15_7353.2]

/-- Complete interval computation for depth 15, residue 7354. -/
theorem bounds_15_7354 : exactInterval 15 7354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7354 : oddCount 7354 15 = 5 ∧ acceleratedOrbit 15 7354 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7354) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7354.1, data_15_7354.2]

/-- Complete interval computation for depth 15, residue 7355. -/
theorem bounds_15_7355 : exactInterval 15 7355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7355 : oddCount 7355 15 = 10 ∧ acceleratedOrbit 15 7355 = 13259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7355) = 3 ^ 10 * m + 13259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7355.1, data_15_7355.2]

/-- Complete interval computation for depth 15, residue 7356. -/
theorem bounds_15_7356 : exactInterval 15 7356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7356 : oddCount 7356 15 = 8 ∧ acceleratedOrbit 15 7356 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7356) = 3 ^ 8 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7356.1, data_15_7356.2]

/-- Complete interval computation for depth 15, residue 7357. -/
theorem bounds_15_7357 : exactInterval 15 7357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7357 : oddCount 7357 15 = 8 ∧ acceleratedOrbit 15 7357 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7357) = 3 ^ 8 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7357.1, data_15_7357.2]

/-- Complete interval computation for depth 15, residue 7358. -/
theorem bounds_15_7358 : exactInterval 15 7358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7358 : oddCount 7358 15 = 8 ∧ acceleratedOrbit 15 7358 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7358) = 3 ^ 8 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7358.1, data_15_7358.2]

/-- Complete interval computation for depth 15, residue 7359. -/
theorem bounds_15_7359 : exactInterval 15 7359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7359 : oddCount 7359 15 = 11 ∧ acceleratedOrbit 15 7359 = 39791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7359) = 3 ^ 11 * m + 39791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7359.1, data_15_7359.2]

/-- Complete interval computation for depth 15, residue 7360. -/
theorem bounds_15_7360 : exactInterval 15 7360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7360 : oddCount 7360 15 = 5 ∧ acceleratedOrbit 15 7360 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7360) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7360.1, data_15_7360.2]

/-- Complete interval computation for depth 15, residue 7361. -/
theorem bounds_15_7361 : exactInterval 15 7361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7361 : oddCount 7361 15 = 6 ∧ acceleratedOrbit 15 7361 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7361) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7361.1, data_15_7361.2]

/-- Complete interval computation for depth 15, residue 7362. -/
theorem bounds_15_7362 : exactInterval 15 7362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7362 : oddCount 7362 15 = 6 ∧ acceleratedOrbit 15 7362 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7362) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7362.1, data_15_7362.2]

/-- Complete interval computation for depth 15, residue 7363. -/
theorem bounds_15_7363 : exactInterval 15 7363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7363 : oddCount 7363 15 = 6 ∧ acceleratedOrbit 15 7363 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7363) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7363.1, data_15_7363.2]

/-- Complete interval computation for depth 15, residue 7364. -/
theorem bounds_15_7364 : exactInterval 15 7364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7364 : oddCount 7364 15 = 5 ∧ acceleratedOrbit 15 7364 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7364) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7364.1, data_15_7364.2]

/-- Complete interval computation for depth 15, residue 7365. -/
theorem bounds_15_7365 : exactInterval 15 7365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7365 : oddCount 7365 15 = 5 ∧ acceleratedOrbit 15 7365 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7365) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7365.1, data_15_7365.2]

/-- Complete interval computation for depth 15, residue 7366. -/
theorem bounds_15_7366 : exactInterval 15 7366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7366 : oddCount 7366 15 = 5 ∧ acceleratedOrbit 15 7366 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7366) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7366.1, data_15_7366.2]

/-- Complete interval computation for depth 15, residue 7367. -/
theorem bounds_15_7367 : exactInterval 15 7367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7367 : oddCount 7367 15 = 10 ∧ acceleratedOrbit 15 7367 = 13283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7367) = 3 ^ 10 * m + 13283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7367.1, data_15_7367.2]

/-- Complete interval computation for depth 15, residue 7368. -/
theorem bounds_15_7368 : exactInterval 15 7368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7368 : oddCount 7368 15 = 5 ∧ acceleratedOrbit 15 7368 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7368) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7368.1, data_15_7368.2]

/-- Complete interval computation for depth 15, residue 7369. -/
theorem bounds_15_7369 : exactInterval 15 7369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7369 : oddCount 7369 15 = 8 ∧ acceleratedOrbit 15 7369 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7369) = 3 ^ 8 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7369.1, data_15_7369.2]

/-- Complete interval computation for depth 15, residue 7370. -/
theorem bounds_15_7370 : exactInterval 15 7370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7370 : oddCount 7370 15 = 5 ∧ acceleratedOrbit 15 7370 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7370) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7370.1, data_15_7370.2]

/-- Complete interval computation for depth 15, residue 7371. -/
theorem bounds_15_7371 : exactInterval 15 7371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7371 : oddCount 7371 15 = 8 ∧ acceleratedOrbit 15 7371 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7371) = 3 ^ 8 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7371.1, data_15_7371.2]

end Collatz.Research.PassageAtlas.Batch0225
