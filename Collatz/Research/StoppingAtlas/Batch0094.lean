import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0094

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 404. -/
theorem bounds_11_404 : exactInterval 11 404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_404 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 404) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_404 : oddCount 404 11 = 4 ∧ acceleratedOrbit 11 404 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_404 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 404) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_404.1, data_11_404.2]

/-- Complete interval computation for depth 11, residue 405. -/
theorem bounds_11_405 : exactInterval 11 405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_405 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 405) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_405 : oddCount 405 11 = 4 ∧ acceleratedOrbit 11 405 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_405 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 405) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_405.1, data_11_405.2]

/-- Complete interval computation for depth 11, residue 406. -/
theorem bounds_11_406 : exactInterval 11 406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_406 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 406) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_406 : oddCount 406 11 = 5 ∧ acceleratedOrbit 11 406 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_406 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 406) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_406.1, data_11_406.2]

/-- Complete interval computation for depth 11, residue 407. -/
theorem bounds_11_407 : exactInterval 11 407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_407 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 407) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_407 : oddCount 407 11 = 5 ∧ acceleratedOrbit 11 407 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_407 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 407) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_407.1, data_11_407.2]

/-- Complete interval computation for depth 11, residue 408. -/
theorem bounds_11_408 : exactInterval 11 408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_408 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 408) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_408 : oddCount 408 11 = 4 ∧ acceleratedOrbit 11 408 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_408 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 408) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_408.1, data_11_408.2]

/-- Complete interval computation for depth 11, residue 409. -/
theorem bounds_11_409 : exactInterval 11 409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_409 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 409) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_409 : oddCount 409 11 = 5 ∧ acceleratedOrbit 11 409 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_409 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 409) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_409.1, data_11_409.2]

/-- Complete interval computation for depth 11, residue 410. -/
theorem bounds_11_410 : exactInterval 11 410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_410 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 410) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_410 : oddCount 410 11 = 4 ∧ acceleratedOrbit 11 410 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_410 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 410) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_410.1, data_11_410.2]

/-- Complete interval computation for depth 11, residue 411. -/
theorem bounds_11_411 : exactInterval 11 411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_411 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 411) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_411 : oddCount 411 11 = 8 ∧ acceleratedOrbit 11 411 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_411 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 411) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_411.1, data_11_411.2]

/-- Complete interval computation for depth 11, residue 412. -/
theorem bounds_11_412 : exactInterval 11 412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_412 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 412) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_412 : oddCount 412 11 = 7 ∧ acceleratedOrbit 11 412 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_412 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 412) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_412.1, data_11_412.2]

/-- Complete interval computation for depth 11, residue 413. -/
theorem bounds_11_413 : exactInterval 11 413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_413 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 413) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_413 : oddCount 413 11 = 7 ∧ acceleratedOrbit 11 413 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_413 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 413) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_413.1, data_11_413.2]

/-- Complete interval computation for depth 11, residue 414. -/
theorem bounds_11_414 : exactInterval 11 414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_414 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 414) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_414 : oddCount 414 11 = 7 ∧ acceleratedOrbit 11 414 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_414 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 414) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_414.1, data_11_414.2]

/-- Complete interval computation for depth 11, residue 415. -/
theorem bounds_11_415 : exactInterval 11 415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_415 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 415) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_415 : oddCount 415 11 = 8 ∧ acceleratedOrbit 11 415 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_415 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 415) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_415.1, data_11_415.2]

/-- Complete interval computation for depth 11, residue 416. -/
theorem bounds_11_416 : exactInterval 11 416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_416 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 416) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_416 : oddCount 416 11 = 2 ∧ acceleratedOrbit 11 416 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_416 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 416) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_416.1, data_11_416.2]

/-- Complete interval computation for depth 11, residue 417. -/
theorem bounds_11_417 : exactInterval 11 417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_417 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 417) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_417 : oddCount 417 11 = 7 ∧ acceleratedOrbit 11 417 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_417 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 417) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_417.1, data_11_417.2]

/-- Complete interval computation for depth 11, residue 418. -/
theorem bounds_11_418 : exactInterval 11 418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_418 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 418) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_418 : oddCount 418 11 = 6 ∧ acceleratedOrbit 11 418 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_418 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 418) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_418.1, data_11_418.2]

end Collatz.Research.StoppingAtlas.Batch0094
