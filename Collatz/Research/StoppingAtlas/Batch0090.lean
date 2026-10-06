import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0090

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 343. -/
theorem bounds_11_343 : exactInterval 11 343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_343 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 343) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_343 : oddCount 343 11 = 5 ∧ acceleratedOrbit 11 343 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_343 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 343) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_343.1, data_11_343.2]

/-- Complete interval computation for depth 11, residue 344. -/
theorem bounds_11_344 : exactInterval 11 344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_344 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 344) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_344 : oddCount 344 11 = 4 ∧ acceleratedOrbit 11 344 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_344 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 344) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_344.1, data_11_344.2]

/-- Complete interval computation for depth 11, residue 345. -/
theorem bounds_11_345 : exactInterval 11 345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_345 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 345) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_345 : oddCount 345 11 = 6 ∧ acceleratedOrbit 11 345 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_345 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 345) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_345.1, data_11_345.2]

/-- Complete interval computation for depth 11, residue 346. -/
theorem bounds_11_346 : exactInterval 11 346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_346 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 346) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_346 : oddCount 346 11 = 4 ∧ acceleratedOrbit 11 346 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_346 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 346) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_346.1, data_11_346.2]

/-- Complete interval computation for depth 11, residue 347. -/
theorem bounds_11_347 : exactInterval 11 347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_347 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 347) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_347 : oddCount 347 11 = 6 ∧ acceleratedOrbit 11 347 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_347 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 347) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_347.1, data_11_347.2]

/-- Complete interval computation for depth 11, residue 348. -/
theorem bounds_11_348 : exactInterval 11 348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_348 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 348) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_348 : oddCount 348 11 = 4 ∧ acceleratedOrbit 11 348 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_348 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 348) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_348.1, data_11_348.2]

/-- Complete interval computation for depth 11, residue 349. -/
theorem bounds_11_349 : exactInterval 11 349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_349 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 349) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_349 : oddCount 349 11 = 4 ∧ acceleratedOrbit 11 349 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_349 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 349) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_349.1, data_11_349.2]

/-- Complete interval computation for depth 11, residue 350. -/
theorem bounds_11_350 : exactInterval 11 350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_350 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 350) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_350 : oddCount 350 11 = 7 ∧ acceleratedOrbit 11 350 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_350 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 350) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_350.1, data_11_350.2]

/-- Complete interval computation for depth 11, residue 351. -/
theorem bounds_11_351 : exactInterval 11 351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_351 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 351) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_351 : oddCount 351 11 = 7 ∧ acceleratedOrbit 11 351 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_351 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 351) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_351.1, data_11_351.2]

/-- Complete interval computation for depth 11, residue 352. -/
theorem bounds_11_352 : exactInterval 11 352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_352 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 352) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_352 : oddCount 352 11 = 3 ∧ acceleratedOrbit 11 352 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_352 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 352) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_352.1, data_11_352.2]

/-- Complete interval computation for depth 11, residue 353. -/
theorem bounds_11_353 : exactInterval 11 353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_353 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 353) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_353 : oddCount 353 11 = 7 ∧ acceleratedOrbit 11 353 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_353 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 353) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_353.1, data_11_353.2]

/-- Complete interval computation for depth 11, residue 354. -/
theorem bounds_11_354 : exactInterval 11 354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_354 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 354) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_354 : oddCount 354 11 = 5 ∧ acceleratedOrbit 11 354 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_354 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 354) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_354.1, data_11_354.2]

/-- Complete interval computation for depth 11, residue 355. -/
theorem bounds_11_355 : exactInterval 11 355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_355 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 355) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_355 : oddCount 355 11 = 5 ∧ acceleratedOrbit 11 355 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_355 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 355) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_355.1, data_11_355.2]

/-- Complete interval computation for depth 11, residue 356. -/
theorem bounds_11_356 : exactInterval 11 356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_356 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 356) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_356 : oddCount 356 11 = 5 ∧ acceleratedOrbit 11 356 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_356 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 356) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_356.1, data_11_356.2]

/-- Complete interval computation for depth 11, residue 357. -/
theorem bounds_11_357 : exactInterval 11 357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_357 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 357) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_357 : oddCount 357 11 = 5 ∧ acceleratedOrbit 11 357 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_357 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 357) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_357.1, data_11_357.2]

end Collatz.Research.StoppingAtlas.Batch0090
