import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0015

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 458. -/
theorem bounds_15_458 : exactInterval 15 458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_458 : oddCount 458 15 = 6 ∧ acceleratedOrbit 15 458 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 458) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_458.1, data_15_458.2]

/-- Complete interval computation for depth 15, residue 459. -/
theorem bounds_15_459 : exactInterval 15 459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_459 : oddCount 459 15 = 8 ∧ acceleratedOrbit 15 459 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 459) = 3 ^ 8 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_459.1, data_15_459.2]

/-- Complete interval computation for depth 15, residue 460. -/
theorem bounds_15_460 : exactInterval 15 460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_460 : oddCount 460 15 = 6 ∧ acceleratedOrbit 15 460 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 460) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_460.1, data_15_460.2]

/-- Complete interval computation for depth 15, residue 461. -/
theorem bounds_15_461 : exactInterval 15 461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_461 : oddCount 461 15 = 6 ∧ acceleratedOrbit 15 461 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 461) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_461.1, data_15_461.2]

/-- Complete interval computation for depth 15, residue 462. -/
theorem bounds_15_462 : exactInterval 15 462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_462 : oddCount 462 15 = 7 ∧ acceleratedOrbit 15 462 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 462) = 3 ^ 7 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_462.1, data_15_462.2]

/-- Complete interval computation for depth 15, residue 463. -/
theorem bounds_15_463 : exactInterval 15 463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_463 : oddCount 463 15 = 7 ∧ acceleratedOrbit 15 463 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 463) = 3 ^ 7 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_463.1, data_15_463.2]

/-- Complete interval computation for depth 15, residue 464. -/
theorem bounds_15_464 : exactInterval 15 464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_464 : oddCount 464 15 = 5 ∧ acceleratedOrbit 15 464 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 464) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_464.1, data_15_464.2]

/-- Complete interval computation for depth 15, residue 465. -/
theorem bounds_15_465 : exactInterval 15 465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_465 : oddCount 465 15 = 6 ∧ acceleratedOrbit 15 465 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 465) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_465.1, data_15_465.2]

/-- Complete interval computation for depth 15, residue 466. -/
theorem bounds_15_466 : exactInterval 15 466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_466 : oddCount 466 15 = 9 ∧ acceleratedOrbit 15 466 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 466) = 3 ^ 9 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_466.1, data_15_466.2]

/-- Complete interval computation for depth 15, residue 467. -/
theorem bounds_15_467 : exactInterval 15 467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_467 : oddCount 467 15 = 9 ∧ acceleratedOrbit 15 467 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 467) = 3 ^ 9 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_467.1, data_15_467.2]

/-- Complete interval computation for depth 15, residue 468. -/
theorem bounds_15_468 : exactInterval 15 468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_468 : oddCount 468 15 = 5 ∧ acceleratedOrbit 15 468 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 468) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_468.1, data_15_468.2]

/-- Complete interval computation for depth 15, residue 469. -/
theorem bounds_15_469 : exactInterval 15 469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_469 : oddCount 469 15 = 5 ∧ acceleratedOrbit 15 469 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 469) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_469.1, data_15_469.2]

/-- Complete interval computation for depth 15, residue 470. -/
theorem bounds_15_470 : exactInterval 15 470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_470 : oddCount 470 15 = 8 ∧ acceleratedOrbit 15 470 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 470) = 3 ^ 8 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_470.1, data_15_470.2]

/-- Complete interval computation for depth 15, residue 471. -/
theorem bounds_15_471 : exactInterval 15 471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_471 : oddCount 471 15 = 8 ∧ acceleratedOrbit 15 471 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 471) = 3 ^ 8 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_471.1, data_15_471.2]

/-- Complete interval computation for depth 15, residue 472. -/
theorem bounds_15_472 : exactInterval 15 472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_472 : oddCount 472 15 = 6 ∧ acceleratedOrbit 15 472 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 472) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_472.1, data_15_472.2]

/-- Complete interval computation for depth 15, residue 473. -/
theorem bounds_15_473 : exactInterval 15 473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_473 : oddCount 473 15 = 6 ∧ acceleratedOrbit 15 473 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 473) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_473.1, data_15_473.2]

/-- Complete interval computation for depth 15, residue 474. -/
theorem bounds_15_474 : exactInterval 15 474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_474 : oddCount 474 15 = 6 ∧ acceleratedOrbit 15 474 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 474) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_474.1, data_15_474.2]

/-- Complete interval computation for depth 15, residue 475. -/
theorem bounds_15_475 : exactInterval 15 475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_475 : oddCount 475 15 = 7 ∧ acceleratedOrbit 15 475 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 475) = 3 ^ 7 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_475.1, data_15_475.2]

/-- Complete interval computation for depth 15, residue 476. -/
theorem bounds_15_476 : exactInterval 15 476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_476 : oddCount 476 15 = 6 ∧ acceleratedOrbit 15 476 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 476) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_476.1, data_15_476.2]

/-- Complete interval computation for depth 15, residue 477. -/
theorem bounds_15_477 : exactInterval 15 477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_477 : oddCount 477 15 = 6 ∧ acceleratedOrbit 15 477 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 477) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_477.1, data_15_477.2]

/-- Complete interval computation for depth 15, residue 478. -/
theorem bounds_15_478 : exactInterval 15 478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_478 : oddCount 478 15 = 10 ∧ acceleratedOrbit 15 478 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 478) = 3 ^ 10 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_478.1, data_15_478.2]

/-- Complete interval computation for depth 15, residue 479. -/
theorem bounds_15_479 : exactInterval 15 479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_479 : oddCount 479 15 = 10 ∧ acceleratedOrbit 15 479 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 479) = 3 ^ 10 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_479.1, data_15_479.2]

/-- Complete interval computation for depth 15, residue 480. -/
theorem bounds_15_480 : exactInterval 15 480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_480 : oddCount 480 15 = 5 ∧ acceleratedOrbit 15 480 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 480) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_480.1, data_15_480.2]

/-- Complete interval computation for depth 15, residue 481. -/
theorem bounds_15_481 : exactInterval 15 481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_481 : oddCount 481 15 = 8 ∧ acceleratedOrbit 15 481 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 481) = 3 ^ 8 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_481.1, data_15_481.2]

/-- Complete interval computation for depth 15, residue 482. -/
theorem bounds_15_482 : exactInterval 15 482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_482 : oddCount 482 15 = 5 ∧ acceleratedOrbit 15 482 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 482) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_482.1, data_15_482.2]

/-- Complete interval computation for depth 15, residue 483. -/
theorem bounds_15_483 : exactInterval 15 483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_483 : oddCount 483 15 = 5 ∧ acceleratedOrbit 15 483 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 483) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_483.1, data_15_483.2]

/-- Complete interval computation for depth 15, residue 484. -/
theorem bounds_15_484 : exactInterval 15 484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_484 : oddCount 484 15 = 10 ∧ acceleratedOrbit 15 484 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 484) = 3 ^ 10 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_484.1, data_15_484.2]

/-- Complete interval computation for depth 15, residue 485. -/
theorem bounds_15_485 : exactInterval 15 485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_485 : oddCount 485 15 = 10 ∧ acceleratedOrbit 15 485 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 485) = 3 ^ 10 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_485.1, data_15_485.2]

/-- Complete interval computation for depth 15, residue 486. -/
theorem bounds_15_486 : exactInterval 15 486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_486 : oddCount 486 15 = 10 ∧ acceleratedOrbit 15 486 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 486) = 3 ^ 10 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_486.1, data_15_486.2]

/-- Complete interval computation for depth 15, residue 487. -/
theorem bounds_15_487 : exactInterval 15 487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_487 : oddCount 487 15 = 10 ∧ acceleratedOrbit 15 487 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 487) = 3 ^ 10 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_487.1, data_15_487.2]

/-- Complete interval computation for depth 15, residue 488. -/
theorem bounds_15_488 : exactInterval 15 488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_488 : oddCount 488 15 = 5 ∧ acceleratedOrbit 15 488 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 488) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_488.1, data_15_488.2]

/-- Complete interval computation for depth 15, residue 489. -/
theorem bounds_15_489 : exactInterval 15 489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_489 : oddCount 489 15 = 9 ∧ acceleratedOrbit 15 489 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 489) = 3 ^ 9 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_489.1, data_15_489.2]

/-- Complete interval computation for depth 15, residue 490. -/
theorem bounds_15_490 : exactInterval 15 490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_490 : oddCount 490 15 = 5 ∧ acceleratedOrbit 15 490 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 490) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_490.1, data_15_490.2]

end Collatz.Research.PassageAtlas.Batch0015
