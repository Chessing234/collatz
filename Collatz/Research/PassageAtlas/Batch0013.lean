import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0013

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 393. -/
theorem bounds_15_393 : exactInterval 15 393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_393 : oddCount 393 15 = 9 ∧ acceleratedOrbit 15 393 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 393) = 3 ^ 9 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_393.1, data_15_393.2]

/-- Complete interval computation for depth 15, residue 394. -/
theorem bounds_15_394 : exactInterval 15 394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_394 : oddCount 394 15 = 6 ∧ acceleratedOrbit 15 394 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 394) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_394.1, data_15_394.2]

/-- Complete interval computation for depth 15, residue 395. -/
theorem bounds_15_395 : exactInterval 15 395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_395 : oddCount 395 15 = 10 ∧ acceleratedOrbit 15 395 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 395) = 3 ^ 10 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_395.1, data_15_395.2]

/-- Complete interval computation for depth 15, residue 396. -/
theorem bounds_15_396 : exactInterval 15 396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_396 : oddCount 396 15 = 6 ∧ acceleratedOrbit 15 396 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 396) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_396.1, data_15_396.2]

/-- Complete interval computation for depth 15, residue 397. -/
theorem bounds_15_397 : exactInterval 15 397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_397 : oddCount 397 15 = 6 ∧ acceleratedOrbit 15 397 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 397) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_397.1, data_15_397.2]

/-- Complete interval computation for depth 15, residue 398. -/
theorem bounds_15_398 : exactInterval 15 398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_398 : oddCount 398 15 = 10 ∧ acceleratedOrbit 15 398 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 398) = 3 ^ 10 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_398.1, data_15_398.2]

/-- Complete interval computation for depth 15, residue 399. -/
theorem bounds_15_399 : exactInterval 15 399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_399 : oddCount 399 15 = 10 ∧ acceleratedOrbit 15 399 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 399) = 3 ^ 10 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_399.1, data_15_399.2]

/-- Complete interval computation for depth 15, residue 400. -/
theorem bounds_15_400 : exactInterval 15 400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_400 : oddCount 400 15 = 6 ∧ acceleratedOrbit 15 400 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 400) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_400.1, data_15_400.2]

/-- Complete interval computation for depth 15, residue 401. -/
theorem bounds_15_401 : exactInterval 15 401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_401 : oddCount 401 15 = 4 ∧ acceleratedOrbit 15 401 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 401) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_401.1, data_15_401.2]

/-- Complete interval computation for depth 15, residue 402. -/
theorem bounds_15_402 : exactInterval 15 402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_402 : oddCount 402 15 = 4 ∧ acceleratedOrbit 15 402 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 402) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_402.1, data_15_402.2]

/-- Complete interval computation for depth 15, residue 403. -/
theorem bounds_15_403 : exactInterval 15 403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_403 : oddCount 403 15 = 4 ∧ acceleratedOrbit 15 403 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 403) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_403.1, data_15_403.2]

/-- Complete interval computation for depth 15, residue 404. -/
theorem bounds_15_404 : exactInterval 15 404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_404 : oddCount 404 15 = 6 ∧ acceleratedOrbit 15 404 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 404) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_404.1, data_15_404.2]

/-- Complete interval computation for depth 15, residue 405. -/
theorem bounds_15_405 : exactInterval 15 405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_405 : oddCount 405 15 = 6 ∧ acceleratedOrbit 15 405 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 405) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_405.1, data_15_405.2]

/-- Complete interval computation for depth 15, residue 406. -/
theorem bounds_15_406 : exactInterval 15 406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_406 : oddCount 406 15 = 7 ∧ acceleratedOrbit 15 406 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 406) = 3 ^ 7 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_406.1, data_15_406.2]

/-- Complete interval computation for depth 15, residue 407. -/
theorem bounds_15_407 : exactInterval 15 407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_407 : oddCount 407 15 = 7 ∧ acceleratedOrbit 15 407 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 407) = 3 ^ 7 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_407.1, data_15_407.2]

/-- Complete interval computation for depth 15, residue 408. -/
theorem bounds_15_408 : exactInterval 15 408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_408 : oddCount 408 15 = 6 ∧ acceleratedOrbit 15 408 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 408) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_408.1, data_15_408.2]

/-- Complete interval computation for depth 15, residue 409. -/
theorem bounds_15_409 : exactInterval 15 409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_409 : oddCount 409 15 = 7 ∧ acceleratedOrbit 15 409 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 409) = 3 ^ 7 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_409.1, data_15_409.2]

/-- Complete interval computation for depth 15, residue 410. -/
theorem bounds_15_410 : exactInterval 15 410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_410 : oddCount 410 15 = 6 ∧ acceleratedOrbit 15 410 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 410) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_410.1, data_15_410.2]

/-- Complete interval computation for depth 15, residue 411. -/
theorem bounds_15_411 : exactInterval 15 411 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 411) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_411 : oddCount 411 15 = 9 ∧ acceleratedOrbit 15 411 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 411) = 3 ^ 9 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_411.1, data_15_411.2]

/-- Complete interval computation for depth 15, residue 412. -/
theorem bounds_15_412 : exactInterval 15 412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_412 : oddCount 412 15 = 9 ∧ acceleratedOrbit 15 412 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 412) = 3 ^ 9 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_412.1, data_15_412.2]

/-- Complete interval computation for depth 15, residue 413. -/
theorem bounds_15_413 : exactInterval 15 413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_413 : oddCount 413 15 = 9 ∧ acceleratedOrbit 15 413 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 413) = 3 ^ 9 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_413.1, data_15_413.2]

/-- Complete interval computation for depth 15, residue 414. -/
theorem bounds_15_414 : exactInterval 15 414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_414 : oddCount 414 15 = 9 ∧ acceleratedOrbit 15 414 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 414) = 3 ^ 9 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_414.1, data_15_414.2]

/-- Complete interval computation for depth 15, residue 415. -/
theorem bounds_15_415 : exactInterval 15 415 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 415) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_415 : oddCount 415 15 = 9 ∧ acceleratedOrbit 15 415 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 415) = 3 ^ 9 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_415.1, data_15_415.2]

/-- Complete interval computation for depth 15, residue 416. -/
theorem bounds_15_416 : exactInterval 15 416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_416 : oddCount 416 15 = 4 ∧ acceleratedOrbit 15 416 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 416) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_416.1, data_15_416.2]

/-- Complete interval computation for depth 15, residue 417. -/
theorem bounds_15_417 : exactInterval 15 417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_417 : oddCount 417 15 = 9 ∧ acceleratedOrbit 15 417 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 417) = 3 ^ 9 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_417.1, data_15_417.2]

/-- Complete interval computation for depth 15, residue 418. -/
theorem bounds_15_418 : exactInterval 15 418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_418 : oddCount 418 15 = 7 ∧ acceleratedOrbit 15 418 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 418) = 3 ^ 7 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_418.1, data_15_418.2]

/-- Complete interval computation for depth 15, residue 419. -/
theorem bounds_15_419 : exactInterval 15 419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_419 : oddCount 419 15 = 7 ∧ acceleratedOrbit 15 419 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 419) = 3 ^ 7 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_419.1, data_15_419.2]

/-- Complete interval computation for depth 15, residue 420. -/
theorem bounds_15_420 : exactInterval 15 420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_420 : oddCount 420 15 = 7 ∧ acceleratedOrbit 15 420 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 420) = 3 ^ 7 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_420.1, data_15_420.2]

/-- Complete interval computation for depth 15, residue 421. -/
theorem bounds_15_421 : exactInterval 15 421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_421 : oddCount 421 15 = 7 ∧ acceleratedOrbit 15 421 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 421) = 3 ^ 7 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_421.1, data_15_421.2]

/-- Complete interval computation for depth 15, residue 422. -/
theorem bounds_15_422 : exactInterval 15 422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_422 : oddCount 422 15 = 7 ∧ acceleratedOrbit 15 422 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 422) = 3 ^ 7 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_422.1, data_15_422.2]

/-- Complete interval computation for depth 15, residue 423. -/
theorem bounds_15_423 : exactInterval 15 423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_423 : oddCount 423 15 = 9 ∧ acceleratedOrbit 15 423 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 423) = 3 ^ 9 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_423.1, data_15_423.2]

/-- Complete interval computation for depth 15, residue 424. -/
theorem bounds_15_424 : exactInterval 15 424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_424 : oddCount 424 15 = 4 ∧ acceleratedOrbit 15 424 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 424) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_424.1, data_15_424.2]

end Collatz.Research.PassageAtlas.Batch0013
