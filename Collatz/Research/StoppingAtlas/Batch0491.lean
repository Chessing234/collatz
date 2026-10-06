import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0491

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 358. -/
theorem bounds_13_358 : exactInterval 13 358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_358 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 358) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_358 : oddCount 358 13 = 5 ∧ acceleratedOrbit 13 358 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_358 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 358) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_358.1, data_13_358.2]

/-- Complete interval computation for depth 13, residue 359. -/
theorem bounds_13_359 : exactInterval 13 359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_359 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 359) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_359 : oddCount 359 13 = 9 ∧ acceleratedOrbit 13 359 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_359 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 359) = 3 ^ 9 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_359.1, data_13_359.2]

/-- Complete interval computation for depth 13, residue 360. -/
theorem bounds_13_360 : exactInterval 13 360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_360 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 360) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_360 : oddCount 360 13 = 4 ∧ acceleratedOrbit 13 360 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_360 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 360) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_360.1, data_13_360.2]

/-- Complete interval computation for depth 13, residue 361. -/
theorem bounds_13_361 : exactInterval 13 361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_361 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 361) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_361 : oddCount 361 13 = 7 ∧ acceleratedOrbit 13 361 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_361 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 361) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_361.1, data_13_361.2]

/-- Complete interval computation for depth 13, residue 362. -/
theorem bounds_13_362 : exactInterval 13 362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_362 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 362) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_362 : oddCount 362 13 = 4 ∧ acceleratedOrbit 13 362 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_362 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 362) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_362.1, data_13_362.2]

/-- Complete interval computation for depth 13, residue 363. -/
theorem bounds_13_363 : exactInterval 13 363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_363 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 363) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_363 : oddCount 363 13 = 7 ∧ acceleratedOrbit 13 363 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_363 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 363) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_363.1, data_13_363.2]

/-- Complete interval computation for depth 13, residue 364. -/
theorem bounds_13_364 : exactInterval 13 364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_364 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 364) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_364 : oddCount 364 13 = 9 ∧ acceleratedOrbit 13 364 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_364 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 364) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_364.1, data_13_364.2]

/-- Complete interval computation for depth 13, residue 365. -/
theorem bounds_13_365 : exactInterval 13 365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_365 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 365) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_365 : oddCount 365 13 = 9 ∧ acceleratedOrbit 13 365 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_365 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 365) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_365.1, data_13_365.2]

/-- Complete interval computation for depth 13, residue 366. -/
theorem bounds_13_366 : exactInterval 13 366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_366 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 366) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_366 : oddCount 366 13 = 9 ∧ acceleratedOrbit 13 366 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_366 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 366) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_366.1, data_13_366.2]

/-- Complete interval computation for depth 13, residue 367. -/
theorem bounds_13_367 : exactInterval 13 367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_367 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 367) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_367 : oddCount 367 13 = 8 ∧ acceleratedOrbit 13 367 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_367 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 367) = 3 ^ 8 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_367.1, data_13_367.2]

/-- Complete interval computation for depth 13, residue 368. -/
theorem bounds_13_368 : exactInterval 13 368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_368 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 368) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_368 : oddCount 368 13 = 4 ∧ acceleratedOrbit 13 368 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_368 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 368) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_368.1, data_13_368.2]

/-- Complete interval computation for depth 13, residue 369. -/
theorem bounds_13_369 : exactInterval 13 369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_369 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 369) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_369 : oddCount 369 13 = 4 ∧ acceleratedOrbit 13 369 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_369 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 369) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_369.1, data_13_369.2]

/-- Complete interval computation for depth 13, residue 370. -/
theorem bounds_13_370 : exactInterval 13 370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_370 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 370) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_370 : oddCount 370 13 = 7 ∧ acceleratedOrbit 13 370 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_370 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 370) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_370.1, data_13_370.2]

/-- Complete interval computation for depth 13, residue 371. -/
theorem bounds_13_371 : exactInterval 13 371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_371 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 371) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_371 : oddCount 371 13 = 7 ∧ acceleratedOrbit 13 371 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_371 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 371) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_371.1, data_13_371.2]

/-- Complete interval computation for depth 13, residue 372. -/
theorem bounds_13_372 : exactInterval 13 372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_372 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 372) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_372 : oddCount 372 13 = 4 ∧ acceleratedOrbit 13 372 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_372 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 372) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_372.1, data_13_372.2]

end Collatz.Research.StoppingAtlas.Batch0491
