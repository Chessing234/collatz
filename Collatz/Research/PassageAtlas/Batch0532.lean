import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0532

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17399. -/
theorem bounds_15_17399 : exactInterval 15 17399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17399 : oddCount 17399 15 = 8 ∧ acceleratedOrbit 15 17399 = 3485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17399) = 3 ^ 8 * m + 3485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17399.1, data_15_17399.2]

/-- Complete interval computation for depth 15, residue 17400. -/
theorem bounds_15_17400 : exactInterval 15 17400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17400 : oddCount 17400 15 = 9 ∧ acceleratedOrbit 15 17400 = 10457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17400) = 3 ^ 9 * m + 10457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17400.1, data_15_17400.2]

/-- Complete interval computation for depth 15, residue 17401. -/
theorem bounds_15_17401 : exactInterval 15 17401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17401 : oddCount 17401 15 = 9 ∧ acceleratedOrbit 15 17401 = 10454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17401) = 3 ^ 9 * m + 10454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17401.1, data_15_17401.2]

/-- Complete interval computation for depth 15, residue 17402. -/
theorem bounds_15_17402 : exactInterval 15 17402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17402 : oddCount 17402 15 = 9 ∧ acceleratedOrbit 15 17402 = 10457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17402) = 3 ^ 9 * m + 10457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17402.1, data_15_17402.2]

/-- Complete interval computation for depth 15, residue 17403. -/
theorem bounds_15_17403 : exactInterval 15 17403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17403 : oddCount 17403 15 = 8 ∧ acceleratedOrbit 15 17403 = 3485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17403) = 3 ^ 8 * m + 3485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17403.1, data_15_17403.2]

/-- Complete interval computation for depth 15, residue 17404. -/
theorem bounds_15_17404 : exactInterval 15 17404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17404 : oddCount 17404 15 = 9 ∧ acceleratedOrbit 15 17404 = 10457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17404) = 3 ^ 9 * m + 10457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17404.1, data_15_17404.2]

/-- Complete interval computation for depth 15, residue 17405. -/
theorem bounds_15_17405 : exactInterval 15 17405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17405 : oddCount 17405 15 = 9 ∧ acceleratedOrbit 15 17405 = 10457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17405) = 3 ^ 9 * m + 10457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17405.1, data_15_17405.2]

/-- Complete interval computation for depth 15, residue 17406. -/
theorem bounds_15_17406 : exactInterval 15 17406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17406 : oddCount 17406 15 = 12 ∧ acceleratedOrbit 15 17406 = 282329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17406) = 3 ^ 12 * m + 282329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17406.1, data_15_17406.2]

/-- Complete interval computation for depth 15, residue 17407. -/
theorem bounds_15_17407 : exactInterval 15 17407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17407 : oddCount 17407 15 = 12 ∧ acceleratedOrbit 15 17407 = 282329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17407) = 3 ^ 12 * m + 282329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17407.1, data_15_17407.2]

/-- Complete interval computation for depth 15, residue 17408. -/
theorem bounds_15_17408 : exactInterval 15 17408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17408 : oddCount 17408 15 = 2 ∧ acceleratedOrbit 15 17408 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17408) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17408.1, data_15_17408.2]

/-- Complete interval computation for depth 15, residue 17409. -/
theorem bounds_15_17409 : exactInterval 15 17409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17409 : oddCount 17409 15 = 7 ∧ acceleratedOrbit 15 17409 = 1163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17409) = 3 ^ 7 * m + 1163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17409.1, data_15_17409.2]

/-- Complete interval computation for depth 15, residue 17410. -/
theorem bounds_15_17410 : exactInterval 15 17410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17410 : oddCount 17410 15 = 7 ∧ acceleratedOrbit 15 17410 = 1163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17410) = 3 ^ 7 * m + 1163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17410.1, data_15_17410.2]

/-- Complete interval computation for depth 15, residue 17411. -/
theorem bounds_15_17411 : exactInterval 15 17411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17411 : oddCount 17411 15 = 7 ∧ acceleratedOrbit 15 17411 = 1163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17411) = 3 ^ 7 * m + 1163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17411.1, data_15_17411.2]

/-- Complete interval computation for depth 15, residue 17412. -/
theorem bounds_15_17412 : exactInterval 15 17412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17412 : oddCount 17412 15 = 6 ∧ acceleratedOrbit 15 17412 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17412) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17412.1, data_15_17412.2]

/-- Complete interval computation for depth 15, residue 17413. -/
theorem bounds_15_17413 : exactInterval 15 17413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17413 : oddCount 17413 15 = 6 ∧ acceleratedOrbit 15 17413 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17413) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17413.1, data_15_17413.2]

/-- Complete interval computation for depth 15, residue 17414. -/
theorem bounds_15_17414 : exactInterval 15 17414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17414 : oddCount 17414 15 = 6 ∧ acceleratedOrbit 15 17414 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17414) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17414.1, data_15_17414.2]

/-- Complete interval computation for depth 15, residue 17415. -/
theorem bounds_15_17415 : exactInterval 15 17415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17415 : oddCount 17415 15 = 7 ∧ acceleratedOrbit 15 17415 = 1163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17415) = 3 ^ 7 * m + 1163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17415.1, data_15_17415.2]

/-- Complete interval computation for depth 15, residue 17416. -/
theorem bounds_15_17416 : exactInterval 15 17416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17416 : oddCount 17416 15 = 6 ∧ acceleratedOrbit 15 17416 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17416) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17416.1, data_15_17416.2]

/-- Complete interval computation for depth 15, residue 17417. -/
theorem bounds_15_17417 : exactInterval 15 17417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17417 : oddCount 17417 15 = 8 ∧ acceleratedOrbit 15 17417 = 3488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17417) = 3 ^ 8 * m + 3488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17417.1, data_15_17417.2]

/-- Complete interval computation for depth 15, residue 17418. -/
theorem bounds_15_17418 : exactInterval 15 17418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17418 : oddCount 17418 15 = 6 ∧ acceleratedOrbit 15 17418 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17418) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17418.1, data_15_17418.2]

/-- Complete interval computation for depth 15, residue 17419. -/
theorem bounds_15_17419 : exactInterval 15 17419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17419 : oddCount 17419 15 = 6 ∧ acceleratedOrbit 15 17419 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17419) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17419.1, data_15_17419.2]

/-- Complete interval computation for depth 15, residue 17420. -/
theorem bounds_15_17420 : exactInterval 15 17420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17420 : oddCount 17420 15 = 6 ∧ acceleratedOrbit 15 17420 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17420) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17420.1, data_15_17420.2]

/-- Complete interval computation for depth 15, residue 17421. -/
theorem bounds_15_17421 : exactInterval 15 17421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17421 : oddCount 17421 15 = 6 ∧ acceleratedOrbit 15 17421 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17421) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17421.1, data_15_17421.2]

/-- Complete interval computation for depth 15, residue 17422. -/
theorem bounds_15_17422 : exactInterval 15 17422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17422 : oddCount 17422 15 = 9 ∧ acceleratedOrbit 15 17422 = 10469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17422) = 3 ^ 9 * m + 10469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17422.1, data_15_17422.2]

/-- Complete interval computation for depth 15, residue 17423. -/
theorem bounds_15_17423 : exactInterval 15 17423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17423 : oddCount 17423 15 = 9 ∧ acceleratedOrbit 15 17423 = 10469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17423) = 3 ^ 9 * m + 10469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17423.1, data_15_17423.2]

/-- Complete interval computation for depth 15, residue 17424. -/
theorem bounds_15_17424 : exactInterval 15 17424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17424 : oddCount 17424 15 = 5 ∧ acceleratedOrbit 15 17424 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17424) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17424.1, data_15_17424.2]

/-- Complete interval computation for depth 15, residue 17425. -/
theorem bounds_15_17425 : exactInterval 15 17425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17425 : oddCount 17425 15 = 6 ∧ acceleratedOrbit 15 17425 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17425) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17425.1, data_15_17425.2]

/-- Complete interval computation for depth 15, residue 17426. -/
theorem bounds_15_17426 : exactInterval 15 17426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17426 : oddCount 17426 15 = 6 ∧ acceleratedOrbit 15 17426 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17426) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17426.1, data_15_17426.2]

/-- Complete interval computation for depth 15, residue 17427. -/
theorem bounds_15_17427 : exactInterval 15 17427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17427 : oddCount 17427 15 = 6 ∧ acceleratedOrbit 15 17427 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17427) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17427.1, data_15_17427.2]

/-- Complete interval computation for depth 15, residue 17428. -/
theorem bounds_15_17428 : exactInterval 15 17428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17428 : oddCount 17428 15 = 5 ∧ acceleratedOrbit 15 17428 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17428) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17428.1, data_15_17428.2]

/-- Complete interval computation for depth 15, residue 17429. -/
theorem bounds_15_17429 : exactInterval 15 17429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17429 : oddCount 17429 15 = 5 ∧ acceleratedOrbit 15 17429 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17429) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17429.1, data_15_17429.2]

/-- Complete interval computation for depth 15, residue 17430. -/
theorem bounds_15_17430 : exactInterval 15 17430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17430 : oddCount 17430 15 = 6 ∧ acceleratedOrbit 15 17430 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17430) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17430.1, data_15_17430.2]

/-- Complete interval computation for depth 15, residue 17431. -/
theorem bounds_15_17431 : exactInterval 15 17431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17431 : oddCount 17431 15 = 6 ∧ acceleratedOrbit 15 17431 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17431) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17431.1, data_15_17431.2]

end Collatz.Research.PassageAtlas.Batch0532
