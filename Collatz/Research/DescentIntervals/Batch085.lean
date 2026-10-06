import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch085

/-- Complete interval computation for depth 9, residue 348. -/
theorem bounds_9_348 : exactInterval 9 348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_348 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 348) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_348 : oddCount 348 9 = 4 ∧ acceleratedOrbit 9 348 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_348 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 348) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_348.1, data_9_348.2]

/-- Complete interval computation for depth 9, residue 349. -/
theorem bounds_9_349 : exactInterval 9 349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_349 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 349) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_349 : oddCount 349 9 = 4 ∧ acceleratedOrbit 9 349 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_349 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 349) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_349.1, data_9_349.2]

/-- Complete interval computation for depth 9, residue 350. -/
theorem bounds_9_350 : exactInterval 9 350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_350 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 350) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_350 : oddCount 350 9 = 5 ∧ acceleratedOrbit 9 350 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_350 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 350) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_350.1, data_9_350.2]

/-- Complete interval computation for depth 9, residue 351. -/
theorem bounds_9_351 : exactInterval 9 351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_351 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 351) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_351 : oddCount 351 9 = 5 ∧ acceleratedOrbit 9 351 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_351 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 351) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_351.1, data_9_351.2]

/-- Complete interval computation for depth 9, residue 352. -/
theorem bounds_9_352 : exactInterval 9 352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_352 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 352) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_352 : oddCount 352 9 = 3 ∧ acceleratedOrbit 9 352 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_352 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 352) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_352.1, data_9_352.2]

/-- Complete interval computation for depth 9, residue 353. -/
theorem bounds_9_353 : exactInterval 9 353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_353 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 353) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_353 : oddCount 353 9 = 6 ∧ acceleratedOrbit 9 353 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_353 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 353) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_353.1, data_9_353.2]

/-- Complete interval computation for depth 9, residue 354. -/
theorem bounds_9_354 : exactInterval 9 354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_354 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 354) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_354 : oddCount 354 9 = 3 ∧ acceleratedOrbit 9 354 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_354 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 354) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_354.1, data_9_354.2]

/-- Complete interval computation for depth 9, residue 355. -/
theorem bounds_9_355 : exactInterval 9 355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_355 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 355) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_355 : oddCount 355 9 = 3 ∧ acceleratedOrbit 9 355 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_355 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 355) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_355.1, data_9_355.2]

/-- Complete interval computation for depth 9, residue 356. -/
theorem bounds_9_356 : exactInterval 9 356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_356 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 356) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_356 : oddCount 356 9 = 3 ∧ acceleratedOrbit 9 356 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_356 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 356) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_356.1, data_9_356.2]

/-- Complete interval computation for depth 9, residue 357. -/
theorem bounds_9_357 : exactInterval 9 357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_357 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 357) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_357 : oddCount 357 9 = 3 ∧ acceleratedOrbit 9 357 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_357 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 357) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_357.1, data_9_357.2]

end Collatz.Research.DescentIntervals.Batch085
