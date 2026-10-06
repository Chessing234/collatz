import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0490

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 343. -/
theorem bounds_13_343 : exactInterval 13 343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_343 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 343) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_343 : oddCount 343 13 = 6 ∧ acceleratedOrbit 13 343 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_343 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 343) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_343.1, data_13_343.2]

/-- Complete interval computation for depth 13, residue 344. -/
theorem bounds_13_344 : exactInterval 13 344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_344 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 344) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_344 : oddCount 344 13 = 5 ∧ acceleratedOrbit 13 344 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_344 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 344) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_344.1, data_13_344.2]

/-- Complete interval computation for depth 13, residue 345. -/
theorem bounds_13_345 : exactInterval 13 345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_345 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 345) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_345 : oddCount 345 13 = 7 ∧ acceleratedOrbit 13 345 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_345 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 345) = 3 ^ 7 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_345.1, data_13_345.2]

/-- Complete interval computation for depth 13, residue 346. -/
theorem bounds_13_346 : exactInterval 13 346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_346 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 346) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_346 : oddCount 346 13 = 5 ∧ acceleratedOrbit 13 346 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_346 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 346) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_346.1, data_13_346.2]

/-- Complete interval computation for depth 13, residue 347. -/
theorem bounds_13_347 : exactInterval 13 347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_347 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 347) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_347 : oddCount 347 13 = 6 ∧ acceleratedOrbit 13 347 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_347 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 347) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_347.1, data_13_347.2]

/-- Complete interval computation for depth 13, residue 348. -/
theorem bounds_13_348 : exactInterval 13 348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_348 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 348) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_348 : oddCount 348 13 = 5 ∧ acceleratedOrbit 13 348 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_348 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 348) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_348.1, data_13_348.2]

/-- Complete interval computation for depth 13, residue 349. -/
theorem bounds_13_349 : exactInterval 13 349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_349 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 349) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_349 : oddCount 349 13 = 5 ∧ acceleratedOrbit 13 349 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_349 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 349) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_349.1, data_13_349.2]

/-- Complete interval computation for depth 13, residue 350. -/
theorem bounds_13_350 : exactInterval 13 350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_350 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 350) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_350 : oddCount 350 13 = 8 ∧ acceleratedOrbit 13 350 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_350 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 350) = 3 ^ 8 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_350.1, data_13_350.2]

/-- Complete interval computation for depth 13, residue 351. -/
theorem bounds_13_351 : exactInterval 13 351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_351 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 351) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_351 : oddCount 351 13 = 8 ∧ acceleratedOrbit 13 351 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_351 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 351) = 3 ^ 8 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_351.1, data_13_351.2]

/-- Complete interval computation for depth 13, residue 352. -/
theorem bounds_13_352 : exactInterval 13 352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_352 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 352) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_352 : oddCount 352 13 = 4 ∧ acceleratedOrbit 13 352 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_352 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 352) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_352.1, data_13_352.2]

/-- Complete interval computation for depth 13, residue 353. -/
theorem bounds_13_353 : exactInterval 13 353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_353 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 353) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_353 : oddCount 353 13 = 7 ∧ acceleratedOrbit 13 353 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_353 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 353) = 3 ^ 7 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_353.1, data_13_353.2]

/-- Complete interval computation for depth 13, residue 354. -/
theorem bounds_13_354 : exactInterval 13 354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_354 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 354) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_354 : oddCount 354 13 = 5 ∧ acceleratedOrbit 13 354 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_354 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 354) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_354.1, data_13_354.2]

/-- Complete interval computation for depth 13, residue 355. -/
theorem bounds_13_355 : exactInterval 13 355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_355 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 355) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_355 : oddCount 355 13 = 5 ∧ acceleratedOrbit 13 355 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_355 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 355) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_355.1, data_13_355.2]

/-- Complete interval computation for depth 13, residue 356. -/
theorem bounds_13_356 : exactInterval 13 356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_356 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 356) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_356 : oddCount 356 13 = 5 ∧ acceleratedOrbit 13 356 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_356 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 356) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_356.1, data_13_356.2]

/-- Complete interval computation for depth 13, residue 357. -/
theorem bounds_13_357 : exactInterval 13 357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_357 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 357) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_357 : oddCount 357 13 = 5 ∧ acceleratedOrbit 13 357 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_357 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 357) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_357.1, data_13_357.2]

end Collatz.Research.StoppingAtlas.Batch0490
