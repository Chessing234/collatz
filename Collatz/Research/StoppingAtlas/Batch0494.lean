import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0494

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 404. -/
theorem bounds_13_404 : exactInterval 13 404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_404 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 404) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_404 : oddCount 404 13 = 5 ∧ acceleratedOrbit 13 404 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_404 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 404) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_404.1, data_13_404.2]

/-- Complete interval computation for depth 13, residue 405. -/
theorem bounds_13_405 : exactInterval 13 405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_405 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 405) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_405 : oddCount 405 13 = 5 ∧ acceleratedOrbit 13 405 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_405 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 405) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_405.1, data_13_405.2]

/-- Complete interval computation for depth 13, residue 406. -/
theorem bounds_13_406 : exactInterval 13 406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_406 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 406) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_406 : oddCount 406 13 = 6 ∧ acceleratedOrbit 13 406 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_406 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 406) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_406.1, data_13_406.2]

/-- Complete interval computation for depth 13, residue 407. -/
theorem bounds_13_407 : exactInterval 13 407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_407 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 407) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_407 : oddCount 407 13 = 6 ∧ acceleratedOrbit 13 407 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_407 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 407) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_407.1, data_13_407.2]

/-- Complete interval computation for depth 13, residue 408. -/
theorem bounds_13_408 : exactInterval 13 408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_408 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 408) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_408 : oddCount 408 13 = 5 ∧ acceleratedOrbit 13 408 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_408 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 408) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_408.1, data_13_408.2]

/-- Complete interval computation for depth 13, residue 409. -/
theorem bounds_13_409 : exactInterval 13 409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_409 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 409) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_409 : oddCount 409 13 = 6 ∧ acceleratedOrbit 13 409 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_409 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 409) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_409.1, data_13_409.2]

/-- Complete interval computation for depth 13, residue 410. -/
theorem bounds_13_410 : exactInterval 13 410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_410 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 410) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_410 : oddCount 410 13 = 5 ∧ acceleratedOrbit 13 410 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_410 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 410) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_410.1, data_13_410.2]

/-- Complete interval computation for depth 13, residue 411. -/
theorem bounds_13_411 : exactInterval 13 411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_411 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 411) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_411 : oddCount 411 13 = 9 ∧ acceleratedOrbit 13 411 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_411 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 411) = 3 ^ 9 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_411.1, data_13_411.2]

/-- Complete interval computation for depth 13, residue 412. -/
theorem bounds_13_412 : exactInterval 13 412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_412 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 412) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_412 : oddCount 412 13 = 8 ∧ acceleratedOrbit 13 412 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_412 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 412) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_412.1, data_13_412.2]

/-- Complete interval computation for depth 13, residue 413. -/
theorem bounds_13_413 : exactInterval 13 413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_413 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 413) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_413 : oddCount 413 13 = 8 ∧ acceleratedOrbit 13 413 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_413 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 413) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_413.1, data_13_413.2]

/-- Complete interval computation for depth 13, residue 414. -/
theorem bounds_13_414 : exactInterval 13 414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_414 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 414) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_414 : oddCount 414 13 = 8 ∧ acceleratedOrbit 13 414 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_414 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 414) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_414.1, data_13_414.2]

/-- Complete interval computation for depth 13, residue 415. -/
theorem bounds_13_415 : exactInterval 13 415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_415 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 415) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_415 : oddCount 415 13 = 9 ∧ acceleratedOrbit 13 415 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_415 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 415) = 3 ^ 9 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_415.1, data_13_415.2]

/-- Complete interval computation for depth 13, residue 416. -/
theorem bounds_13_416 : exactInterval 13 416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_416 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 416) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_416 : oddCount 416 13 = 3 ∧ acceleratedOrbit 13 416 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_416 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 416) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_416.1, data_13_416.2]

/-- Complete interval computation for depth 13, residue 417. -/
theorem bounds_13_417 : exactInterval 13 417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_417 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 417) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_417 : oddCount 417 13 = 8 ∧ acceleratedOrbit 13 417 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_417 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 417) = 3 ^ 8 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_417.1, data_13_417.2]

/-- Complete interval computation for depth 13, residue 418. -/
theorem bounds_13_418 : exactInterval 13 418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_418 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 418) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_418 : oddCount 418 13 = 6 ∧ acceleratedOrbit 13 418 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_418 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 418) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_418.1, data_13_418.2]

end Collatz.Research.StoppingAtlas.Batch0494
