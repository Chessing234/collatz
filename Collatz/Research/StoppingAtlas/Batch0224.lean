import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0224

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 353. -/
theorem bounds_12_353 : exactInterval 12 353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_353 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 353) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_353 : oddCount 353 12 = 7 ∧ acceleratedOrbit 12 353 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_353 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 353) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_353.1, data_12_353.2]

/-- Complete interval computation for depth 12, residue 354. -/
theorem bounds_12_354 : exactInterval 12 354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_354 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 354) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_354 : oddCount 354 12 = 5 ∧ acceleratedOrbit 12 354 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_354 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 354) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_354.1, data_12_354.2]

/-- Complete interval computation for depth 12, residue 355. -/
theorem bounds_12_355 : exactInterval 12 355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_355 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 355) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_355 : oddCount 355 12 = 5 ∧ acceleratedOrbit 12 355 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_355 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 355) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_355.1, data_12_355.2]

/-- Complete interval computation for depth 12, residue 356. -/
theorem bounds_12_356 : exactInterval 12 356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_356 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 356) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_356 : oddCount 356 12 = 5 ∧ acceleratedOrbit 12 356 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_356 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 356) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_356.1, data_12_356.2]

/-- Complete interval computation for depth 12, residue 357. -/
theorem bounds_12_357 : exactInterval 12 357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_357 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 357) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_357 : oddCount 357 12 = 5 ∧ acceleratedOrbit 12 357 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_357 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 357) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_357.1, data_12_357.2]

/-- Complete interval computation for depth 12, residue 358. -/
theorem bounds_12_358 : exactInterval 12 358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_358 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 358) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_358 : oddCount 358 12 = 5 ∧ acceleratedOrbit 12 358 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_358 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 358) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_358.1, data_12_358.2]

/-- Complete interval computation for depth 12, residue 359. -/
theorem bounds_12_359 : exactInterval 12 359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_359 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 359) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_359 : oddCount 359 12 = 8 ∧ acceleratedOrbit 12 359 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_359 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 359) = 3 ^ 8 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_359.1, data_12_359.2]

/-- Complete interval computation for depth 12, residue 360. -/
theorem bounds_12_360 : exactInterval 12 360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_360 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 360) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_360 : oddCount 360 12 = 4 ∧ acceleratedOrbit 12 360 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_360 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 360) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_360.1, data_12_360.2]

/-- Complete interval computation for depth 12, residue 361. -/
theorem bounds_12_361 : exactInterval 12 361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_361 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 361) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_361 : oddCount 361 12 = 6 ∧ acceleratedOrbit 12 361 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_361 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 361) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_361.1, data_12_361.2]

/-- Complete interval computation for depth 12, residue 362. -/
theorem bounds_12_362 : exactInterval 12 362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_362 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 362) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_362 : oddCount 362 12 = 4 ∧ acceleratedOrbit 12 362 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_362 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 362) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_362.1, data_12_362.2]

/-- Complete interval computation for depth 12, residue 363. -/
theorem bounds_12_363 : exactInterval 12 363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_363 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 363) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_363 : oddCount 363 12 = 6 ∧ acceleratedOrbit 12 363 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_363 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 363) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_363.1, data_12_363.2]

/-- Complete interval computation for depth 12, residue 364. -/
theorem bounds_12_364 : exactInterval 12 364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_364 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 364) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_364 : oddCount 364 12 = 8 ∧ acceleratedOrbit 12 364 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_364 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 364) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_364.1, data_12_364.2]

/-- Complete interval computation for depth 12, residue 365. -/
theorem bounds_12_365 : exactInterval 12 365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_365 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 365) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_365 : oddCount 365 12 = 8 ∧ acceleratedOrbit 12 365 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_365 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 365) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_365.1, data_12_365.2]

/-- Complete interval computation for depth 12, residue 366. -/
theorem bounds_12_366 : exactInterval 12 366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_366 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 366) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_366 : oddCount 366 12 = 8 ∧ acceleratedOrbit 12 366 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_366 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 366) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_366.1, data_12_366.2]

/-- Complete interval computation for depth 12, residue 367. -/
theorem bounds_12_367 : exactInterval 12 367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_367 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 367) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_367 : oddCount 367 12 = 7 ∧ acceleratedOrbit 12 367 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_367 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 367) = 3 ^ 7 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_367.1, data_12_367.2]

end Collatz.Research.StoppingAtlas.Batch0224
