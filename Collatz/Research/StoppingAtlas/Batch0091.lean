import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0091

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 358. -/
theorem bounds_11_358 : exactInterval 11 358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_358 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 358) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_358 : oddCount 358 11 = 5 ∧ acceleratedOrbit 11 358 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_358 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 358) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_358.1, data_11_358.2]

/-- Complete interval computation for depth 11, residue 359. -/
theorem bounds_11_359 : exactInterval 11 359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_359 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 359) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_359 : oddCount 359 11 = 8 ∧ acceleratedOrbit 11 359 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_359 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 359) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_359.1, data_11_359.2]

/-- Complete interval computation for depth 11, residue 360. -/
theorem bounds_11_360 : exactInterval 11 360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_360 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 360) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_360 : oddCount 360 11 = 3 ∧ acceleratedOrbit 11 360 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_360 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 360) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_360.1, data_11_360.2]

/-- Complete interval computation for depth 11, residue 361. -/
theorem bounds_11_361 : exactInterval 11 361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_361 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 361) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_361 : oddCount 361 11 = 5 ∧ acceleratedOrbit 11 361 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_361 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 361) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_361.1, data_11_361.2]

/-- Complete interval computation for depth 11, residue 362. -/
theorem bounds_11_362 : exactInterval 11 362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_362 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 362) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_362 : oddCount 362 11 = 3 ∧ acceleratedOrbit 11 362 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_362 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 362) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_362.1, data_11_362.2]

/-- Complete interval computation for depth 11, residue 363. -/
theorem bounds_11_363 : exactInterval 11 363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_363 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 363) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_363 : oddCount 363 11 = 6 ∧ acceleratedOrbit 11 363 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_363 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 363) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_363.1, data_11_363.2]

/-- Complete interval computation for depth 11, residue 364. -/
theorem bounds_11_364 : exactInterval 11 364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_364 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 364) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_364 : oddCount 364 11 = 7 ∧ acceleratedOrbit 11 364 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_364 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 364) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_364.1, data_11_364.2]

/-- Complete interval computation for depth 11, residue 365. -/
theorem bounds_11_365 : exactInterval 11 365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_365 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 365) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_365 : oddCount 365 11 = 7 ∧ acceleratedOrbit 11 365 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_365 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 365) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_365.1, data_11_365.2]

/-- Complete interval computation for depth 11, residue 366. -/
theorem bounds_11_366 : exactInterval 11 366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_366 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 366) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_366 : oddCount 366 11 = 7 ∧ acceleratedOrbit 11 366 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_366 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 366) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_366.1, data_11_366.2]

/-- Complete interval computation for depth 11, residue 367. -/
theorem bounds_11_367 : exactInterval 11 367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_367 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 367) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_367 : oddCount 367 11 = 6 ∧ acceleratedOrbit 11 367 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_367 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 367) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_367.1, data_11_367.2]

/-- Complete interval computation for depth 11, residue 368. -/
theorem bounds_11_368 : exactInterval 11 368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_368 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 368) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_368 : oddCount 368 11 = 3 ∧ acceleratedOrbit 11 368 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_368 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 368) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_368.1, data_11_368.2]

/-- Complete interval computation for depth 11, residue 369. -/
theorem bounds_11_369 : exactInterval 11 369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_369 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 369) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_369 : oddCount 369 11 = 3 ∧ acceleratedOrbit 11 369 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_369 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 369) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_369.1, data_11_369.2]

/-- Complete interval computation for depth 11, residue 370. -/
theorem bounds_11_370 : exactInterval 11 370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_370 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 370) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_370 : oddCount 370 11 = 6 ∧ acceleratedOrbit 11 370 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_370 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 370) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_370.1, data_11_370.2]

/-- Complete interval computation for depth 11, residue 371. -/
theorem bounds_11_371 : exactInterval 11 371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_371 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 371) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_371 : oddCount 371 11 = 6 ∧ acceleratedOrbit 11 371 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_371 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 371) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_371.1, data_11_371.2]

/-- Complete interval computation for depth 11, residue 372. -/
theorem bounds_11_372 : exactInterval 11 372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_372 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 372) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_372 : oddCount 372 11 = 3 ∧ acceleratedOrbit 11 372 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_372 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 372) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_372.1, data_11_372.2]

end Collatz.Research.StoppingAtlas.Batch0091
