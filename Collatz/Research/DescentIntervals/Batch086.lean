import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch086

/-- Complete interval computation for depth 9, residue 358. -/
theorem bounds_9_358 : exactInterval 9 358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_358 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 358) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_358 : oddCount 358 9 = 3 ∧ acceleratedOrbit 9 358 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_358 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 358) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_358.1, data_9_358.2]

/-- Complete interval computation for depth 9, residue 359. -/
theorem bounds_9_359 : exactInterval 9 359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_359 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 359) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_359 : oddCount 359 9 = 8 ∧ acceleratedOrbit 9 359 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_359 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 359) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_359.1, data_9_359.2]

/-- Complete interval computation for depth 9, residue 360. -/
theorem bounds_9_360 : exactInterval 9 360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_360 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 360) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_360 : oddCount 360 9 = 3 ∧ acceleratedOrbit 9 360 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_360 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 360) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_360.1, data_9_360.2]

/-- Complete interval computation for depth 9, residue 361. -/
theorem bounds_9_361 : exactInterval 9 361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_361 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 361) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_361 : oddCount 361 9 = 5 ∧ acceleratedOrbit 9 361 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_361 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 361) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_361.1, data_9_361.2]

/-- Complete interval computation for depth 9, residue 362. -/
theorem bounds_9_362 : exactInterval 9 362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_362 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 362) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_362 : oddCount 362 9 = 3 ∧ acceleratedOrbit 9 362 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_362 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 362) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_362.1, data_9_362.2]

/-- Complete interval computation for depth 9, residue 363. -/
theorem bounds_9_363 : exactInterval 9 363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_363 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 363) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_363 : oddCount 363 9 = 5 ∧ acceleratedOrbit 9 363 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_363 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 363) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_363.1, data_9_363.2]

/-- Complete interval computation for depth 9, residue 364. -/
theorem bounds_9_364 : exactInterval 9 364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_364 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 364) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_364 : oddCount 364 9 = 5 ∧ acceleratedOrbit 9 364 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_364 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 364) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_364.1, data_9_364.2]

/-- Complete interval computation for depth 9, residue 365. -/
theorem bounds_9_365 : exactInterval 9 365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_365 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 365) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_365 : oddCount 365 9 = 5 ∧ acceleratedOrbit 9 365 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_365 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 365) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_365.1, data_9_365.2]

/-- Complete interval computation for depth 9, residue 366. -/
theorem bounds_9_366 : exactInterval 9 366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_366 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 366) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_366 : oddCount 366 9 = 5 ∧ acceleratedOrbit 9 366 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_366 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 366) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_366.1, data_9_366.2]

/-- Complete interval computation for depth 9, residue 367. -/
theorem bounds_9_367 : exactInterval 9 367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_367 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 367) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_367 : oddCount 367 9 = 6 ∧ acceleratedOrbit 9 367 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_367 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 367) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_367.1, data_9_367.2]

end Collatz.Research.DescentIntervals.Batch086
