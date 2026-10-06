import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0098

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 465. -/
theorem bounds_11_465 : exactInterval 11 465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_465 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 465) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_465 : oddCount 465 11 = 5 ∧ acceleratedOrbit 11 465 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_465 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 465) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_465.1, data_11_465.2]

/-- Complete interval computation for depth 11, residue 466. -/
theorem bounds_11_466 : exactInterval 11 466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_466 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 466) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_466 : oddCount 466 11 = 6 ∧ acceleratedOrbit 11 466 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_466 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 466) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_466.1, data_11_466.2]

/-- Complete interval computation for depth 11, residue 467. -/
theorem bounds_11_467 : exactInterval 11 467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_467 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 467) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_467 : oddCount 467 11 = 6 ∧ acceleratedOrbit 11 467 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_467 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 467) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_467.1, data_11_467.2]

/-- Complete interval computation for depth 11, residue 468. -/
theorem bounds_11_468 : exactInterval 11 468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_468 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 468) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_468 : oddCount 468 11 = 4 ∧ acceleratedOrbit 11 468 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_468 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 468) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_468.1, data_11_468.2]

/-- Complete interval computation for depth 11, residue 469. -/
theorem bounds_11_469 : exactInterval 11 469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_469 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 469) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_469 : oddCount 469 11 = 4 ∧ acceleratedOrbit 11 469 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_469 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 469) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_469.1, data_11_469.2]

/-- Complete interval computation for depth 11, residue 470. -/
theorem bounds_11_470 : exactInterval 11 470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_470 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 470) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_470 : oddCount 470 11 = 7 ∧ acceleratedOrbit 11 470 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_470 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 470) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_470.1, data_11_470.2]

/-- Complete interval computation for depth 11, residue 471. -/
theorem bounds_11_471 : exactInterval 11 471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_471 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 471) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_471 : oddCount 471 11 = 7 ∧ acceleratedOrbit 11 471 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_471 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 471) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_471.1, data_11_471.2]

/-- Complete interval computation for depth 11, residue 472. -/
theorem bounds_11_472 : exactInterval 11 472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_472 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 472) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_472 : oddCount 472 11 = 4 ∧ acceleratedOrbit 11 472 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_472 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 472) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_472.1, data_11_472.2]

/-- Complete interval computation for depth 11, residue 473. -/
theorem bounds_11_473 : exactInterval 11 473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_473 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 473) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_473 : oddCount 473 11 = 4 ∧ acceleratedOrbit 11 473 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_473 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 473) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_473.1, data_11_473.2]

/-- Complete interval computation for depth 11, residue 474. -/
theorem bounds_11_474 : exactInterval 11 474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_474 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 474) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_474 : oddCount 474 11 = 4 ∧ acceleratedOrbit 11 474 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_474 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 474) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_474.1, data_11_474.2]

/-- Complete interval computation for depth 11, residue 475. -/
theorem bounds_11_475 : exactInterval 11 475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_475 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 475) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_475 : oddCount 475 11 = 6 ∧ acceleratedOrbit 11 475 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_475 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 475) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_475.1, data_11_475.2]

/-- Complete interval computation for depth 11, residue 476. -/
theorem bounds_11_476 : exactInterval 11 476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_476 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 476) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_476 : oddCount 476 11 = 4 ∧ acceleratedOrbit 11 476 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_476 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 476) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_476.1, data_11_476.2]

/-- Complete interval computation for depth 11, residue 477. -/
theorem bounds_11_477 : exactInterval 11 477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_477 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 477) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_477 : oddCount 477 11 = 4 ∧ acceleratedOrbit 11 477 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_477 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 477) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_477.1, data_11_477.2]

/-- Complete interval computation for depth 11, residue 478. -/
theorem bounds_11_478 : exactInterval 11 478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_478 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 478) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_478 : oddCount 478 11 = 9 ∧ acceleratedOrbit 11 478 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_478 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 478) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_478.1, data_11_478.2]

/-- Complete interval computation for depth 11, residue 479. -/
theorem bounds_11_479 : exactInterval 11 479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_479 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 479) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_479 : oddCount 479 11 = 9 ∧ acceleratedOrbit 11 479 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_479 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 479) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_479.1, data_11_479.2]

/-- Complete interval computation for depth 11, residue 480. -/
theorem bounds_11_480 : exactInterval 11 480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_480 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 480) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_480 : oddCount 480 11 = 4 ∧ acceleratedOrbit 11 480 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_480 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 480) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_480.1, data_11_480.2]

end Collatz.Research.StoppingAtlas.Batch0098
