import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0024

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 353. -/
theorem bounds_10_353 : exactInterval 10 353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_353 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 353) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_353 : oddCount 353 10 = 6 ∧ acceleratedOrbit 10 353 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_353 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 353) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_353.1, data_10_353.2]

/-- Complete interval computation for depth 10, residue 354. -/
theorem bounds_10_354 : exactInterval 10 354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_354 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 354) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_354 : oddCount 354 10 = 4 ∧ acceleratedOrbit 10 354 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_354 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 354) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_354.1, data_10_354.2]

/-- Complete interval computation for depth 10, residue 355. -/
theorem bounds_10_355 : exactInterval 10 355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_355 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 355) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_355 : oddCount 355 10 = 4 ∧ acceleratedOrbit 10 355 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_355 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 355) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_355.1, data_10_355.2]

/-- Complete interval computation for depth 10, residue 356. -/
theorem bounds_10_356 : exactInterval 10 356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_356 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 356) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_356 : oddCount 356 10 = 4 ∧ acceleratedOrbit 10 356 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_356 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 356) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_356.1, data_10_356.2]

/-- Complete interval computation for depth 10, residue 357. -/
theorem bounds_10_357 : exactInterval 10 357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_357 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 357) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_357 : oddCount 357 10 = 4 ∧ acceleratedOrbit 10 357 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_357 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 357) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_357.1, data_10_357.2]

/-- Complete interval computation for depth 10, residue 358. -/
theorem bounds_10_358 : exactInterval 10 358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_358 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 358) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_358 : oddCount 358 10 = 4 ∧ acceleratedOrbit 10 358 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_358 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 358) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_358.1, data_10_358.2]

/-- Complete interval computation for depth 10, residue 359. -/
theorem bounds_10_359 : exactInterval 10 359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_359 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 359) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_359 : oddCount 359 10 = 8 ∧ acceleratedOrbit 10 359 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_359 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 359) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_359.1, data_10_359.2]

/-- Complete interval computation for depth 10, residue 360. -/
theorem bounds_10_360 : exactInterval 10 360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_360 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 360) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_360 : oddCount 360 10 = 3 ∧ acceleratedOrbit 10 360 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_360 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 360) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_360.1, data_10_360.2]

/-- Complete interval computation for depth 10, residue 361. -/
theorem bounds_10_361 : exactInterval 10 361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_361 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 361) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_361 : oddCount 361 10 = 5 ∧ acceleratedOrbit 10 361 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_361 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 361) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_361.1, data_10_361.2]

/-- Complete interval computation for depth 10, residue 362. -/
theorem bounds_10_362 : exactInterval 10 362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_362 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 362) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_362 : oddCount 362 10 = 3 ∧ acceleratedOrbit 10 362 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_362 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 362) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_362.1, data_10_362.2]

/-- Complete interval computation for depth 10, residue 363. -/
theorem bounds_10_363 : exactInterval 10 363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_363 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 363) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_363 : oddCount 363 10 = 6 ∧ acceleratedOrbit 10 363 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_363 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 363) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_363.1, data_10_363.2]

/-- Complete interval computation for depth 10, residue 364. -/
theorem bounds_10_364 : exactInterval 10 364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_364 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 364) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_364 : oddCount 364 10 = 6 ∧ acceleratedOrbit 10 364 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_364 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 364) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_364.1, data_10_364.2]

/-- Complete interval computation for depth 10, residue 365. -/
theorem bounds_10_365 : exactInterval 10 365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_365 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 365) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_365 : oddCount 365 10 = 6 ∧ acceleratedOrbit 10 365 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_365 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 365) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_365.1, data_10_365.2]

/-- Complete interval computation for depth 10, residue 366. -/
theorem bounds_10_366 : exactInterval 10 366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_366 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 366) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_366 : oddCount 366 10 = 6 ∧ acceleratedOrbit 10 366 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_366 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 366) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_366.1, data_10_366.2]

/-- Complete interval computation for depth 10, residue 367. -/
theorem bounds_10_367 : exactInterval 10 367 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_367 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 367) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_367 : oddCount 367 10 = 6 ∧ acceleratedOrbit 10 367 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_367 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 367) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_367.1, data_10_367.2]

end Collatz.Research.StoppingAtlas.Batch0024
