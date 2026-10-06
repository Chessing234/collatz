import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0498

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 465. -/
theorem bounds_13_465 : exactInterval 13 465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_465 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 465) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_465 : oddCount 465 13 = 5 ∧ acceleratedOrbit 13 465 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_465 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 465) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_465.1, data_13_465.2]

/-- Complete interval computation for depth 13, residue 466. -/
theorem bounds_13_466 : exactInterval 13 466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_466 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 466) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_466 : oddCount 466 13 = 8 ∧ acceleratedOrbit 13 466 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_466 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 466) = 3 ^ 8 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_466.1, data_13_466.2]

/-- Complete interval computation for depth 13, residue 467. -/
theorem bounds_13_467 : exactInterval 13 467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_467 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 467) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_467 : oddCount 467 13 = 8 ∧ acceleratedOrbit 13 467 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_467 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 467) = 3 ^ 8 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_467.1, data_13_467.2]

/-- Complete interval computation for depth 13, residue 468. -/
theorem bounds_13_468 : exactInterval 13 468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_468 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 468) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_468 : oddCount 468 13 = 4 ∧ acceleratedOrbit 13 468 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_468 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 468) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_468.1, data_13_468.2]

/-- Complete interval computation for depth 13, residue 469. -/
theorem bounds_13_469 : exactInterval 13 469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_469 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 469) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_469 : oddCount 469 13 = 4 ∧ acceleratedOrbit 13 469 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_469 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 469) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_469.1, data_13_469.2]

/-- Complete interval computation for depth 13, residue 470. -/
theorem bounds_13_470 : exactInterval 13 470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_470 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 470) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_470 : oddCount 470 13 = 8 ∧ acceleratedOrbit 13 470 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_470 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 470) = 3 ^ 8 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_470.1, data_13_470.2]

/-- Complete interval computation for depth 13, residue 471. -/
theorem bounds_13_471 : exactInterval 13 471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_471 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 471) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_471 : oddCount 471 13 = 8 ∧ acceleratedOrbit 13 471 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_471 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 471) = 3 ^ 8 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_471.1, data_13_471.2]

/-- Complete interval computation for depth 13, residue 472. -/
theorem bounds_13_472 : exactInterval 13 472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_472 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 472) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_472 : oddCount 472 13 = 6 ∧ acceleratedOrbit 13 472 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_472 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 472) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_472.1, data_13_472.2]

/-- Complete interval computation for depth 13, residue 473. -/
theorem bounds_13_473 : exactInterval 13 473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_473 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 473) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_473 : oddCount 473 13 = 6 ∧ acceleratedOrbit 13 473 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_473 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 473) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_473.1, data_13_473.2]

/-- Complete interval computation for depth 13, residue 474. -/
theorem bounds_13_474 : exactInterval 13 474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_474 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 474) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_474 : oddCount 474 13 = 6 ∧ acceleratedOrbit 13 474 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_474 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 474) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_474.1, data_13_474.2]

/-- Complete interval computation for depth 13, residue 475. -/
theorem bounds_13_475 : exactInterval 13 475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_475 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 475) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_475 : oddCount 475 13 = 7 ∧ acceleratedOrbit 13 475 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_475 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 475) = 3 ^ 7 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_475.1, data_13_475.2]

/-- Complete interval computation for depth 13, residue 476. -/
theorem bounds_13_476 : exactInterval 13 476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_476 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 476) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_476 : oddCount 476 13 = 6 ∧ acceleratedOrbit 13 476 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_476 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 476) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_476.1, data_13_476.2]

/-- Complete interval computation for depth 13, residue 477. -/
theorem bounds_13_477 : exactInterval 13 477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_477 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 477) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_477 : oddCount 477 13 = 6 ∧ acceleratedOrbit 13 477 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_477 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 477) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_477.1, data_13_477.2]

/-- Complete interval computation for depth 13, residue 478. -/
theorem bounds_13_478 : exactInterval 13 478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_478 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 478) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_478 : oddCount 478 13 = 9 ∧ acceleratedOrbit 13 478 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_478 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 478) = 3 ^ 9 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_478.1, data_13_478.2]

/-- Complete interval computation for depth 13, residue 479. -/
theorem bounds_13_479 : exactInterval 13 479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_479 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 479) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_479 : oddCount 479 13 = 9 ∧ acceleratedOrbit 13 479 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_479 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 479) = 3 ^ 9 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_479.1, data_13_479.2]

/-- Complete interval computation for depth 13, residue 480. -/
theorem bounds_13_480 : exactInterval 13 480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_480 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 480) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_480 : oddCount 480 13 = 4 ∧ acceleratedOrbit 13 480 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_480 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 480) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_480.1, data_13_480.2]

end Collatz.Research.StoppingAtlas.Batch0498
