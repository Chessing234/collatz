import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch091

/-- Complete interval computation for depth 9, residue 409. -/
theorem bounds_9_409 : exactInterval 9 409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_409 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 409) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_409 : oddCount 409 9 = 4 ∧ acceleratedOrbit 9 409 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_409 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 409) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_409.1, data_9_409.2]

/-- Complete interval computation for depth 9, residue 410. -/
theorem bounds_9_410 : exactInterval 9 410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_410 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 410) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_410 : oddCount 410 9 = 3 ∧ acceleratedOrbit 9 410 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_410 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 410) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_410.1, data_9_410.2]

/-- Complete interval computation for depth 9, residue 411. -/
theorem bounds_9_411 : exactInterval 9 411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_411 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 411) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_411 : oddCount 411 9 = 6 ∧ acceleratedOrbit 9 411 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_411 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 411) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_411.1, data_9_411.2]

/-- Complete interval computation for depth 9, residue 412. -/
theorem bounds_9_412 : exactInterval 9 412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_412 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 412) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_412 : oddCount 412 9 = 6 ∧ acceleratedOrbit 9 412 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_412 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 412) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_412.1, data_9_412.2]

/-- Complete interval computation for depth 9, residue 413. -/
theorem bounds_9_413 : exactInterval 9 413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_413 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 413) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_413 : oddCount 413 9 = 6 ∧ acceleratedOrbit 9 413 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_413 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 413) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_413.1, data_9_413.2]

/-- Complete interval computation for depth 9, residue 414. -/
theorem bounds_9_414 : exactInterval 9 414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_414 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 414) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_414 : oddCount 414 9 = 6 ∧ acceleratedOrbit 9 414 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_414 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 414) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_414.1, data_9_414.2]

/-- Complete interval computation for depth 9, residue 415. -/
theorem bounds_9_415 : exactInterval 9 415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_415 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 415) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_415 : oddCount 415 9 = 7 ∧ acceleratedOrbit 9 415 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_415 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 415) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_415.1, data_9_415.2]

/-- Complete interval computation for depth 9, residue 416. -/
theorem bounds_9_416 : exactInterval 9 416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_416 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 416) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_416 : oddCount 416 9 = 2 ∧ acceleratedOrbit 9 416 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_416 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 416) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_416.1, data_9_416.2]

/-- Complete interval computation for depth 9, residue 417. -/
theorem bounds_9_417 : exactInterval 9 417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_417 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 417) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_417 : oddCount 417 9 = 5 ∧ acceleratedOrbit 9 417 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_417 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 417) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_417.1, data_9_417.2]

/-- Complete interval computation for depth 9, residue 418. -/
theorem bounds_9_418 : exactInterval 9 418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_418 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 418) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_418 : oddCount 418 9 = 4 ∧ acceleratedOrbit 9 418 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_418 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 418) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_418.1, data_9_418.2]

/-- Complete interval computation for depth 9, residue 419. -/
theorem bounds_9_419 : exactInterval 9 419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_419 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 419) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_419 : oddCount 419 9 = 4 ∧ acceleratedOrbit 9 419 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_419 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 419) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_419.1, data_9_419.2]

end Collatz.Research.DescentIntervals.Batch091
