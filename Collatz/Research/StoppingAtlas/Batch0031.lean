import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0031

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 460. -/
theorem bounds_10_460 : exactInterval 10 460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_460 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 460) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_460 : oddCount 460 10 = 4 ∧ acceleratedOrbit 10 460 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_460 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 460) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_460.1, data_10_460.2]

/-- Complete interval computation for depth 10, residue 461. -/
theorem bounds_10_461 : exactInterval 10 461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_461 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 461) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_461 : oddCount 461 10 = 4 ∧ acceleratedOrbit 10 461 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_461 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 461) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_461.1, data_10_461.2]

/-- Complete interval computation for depth 10, residue 462. -/
theorem bounds_10_462 : exactInterval 10 462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_462 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 462) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_462 : oddCount 462 10 = 7 ∧ acceleratedOrbit 10 462 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_462 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 462) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_462.1, data_10_462.2]

/-- Complete interval computation for depth 10, residue 463. -/
theorem bounds_10_463 : exactInterval 10 463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_463 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 463) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_463 : oddCount 463 10 = 7 ∧ acceleratedOrbit 10 463 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_463 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 463) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_463.1, data_10_463.2]

/-- Complete interval computation for depth 10, residue 464. -/
theorem bounds_10_464 : exactInterval 10 464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_464 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 464) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_464 : oddCount 464 10 = 3 ∧ acceleratedOrbit 10 464 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_464 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 464) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_464.1, data_10_464.2]

/-- Complete interval computation for depth 10, residue 465. -/
theorem bounds_10_465 : exactInterval 10 465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_465 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 465) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_465 : oddCount 465 10 = 4 ∧ acceleratedOrbit 10 465 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_465 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 465) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_465.1, data_10_465.2]

/-- Complete interval computation for depth 10, residue 466. -/
theorem bounds_10_466 : exactInterval 10 466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_466 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 466) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_466 : oddCount 466 10 = 6 ∧ acceleratedOrbit 10 466 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_466 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 466) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_466.1, data_10_466.2]

/-- Complete interval computation for depth 10, residue 467. -/
theorem bounds_10_467 : exactInterval 10 467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_467 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 467) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_467 : oddCount 467 10 = 6 ∧ acceleratedOrbit 10 467 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_467 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 467) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_467.1, data_10_467.2]

/-- Complete interval computation for depth 10, residue 468. -/
theorem bounds_10_468 : exactInterval 10 468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_468 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 468) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_468 : oddCount 468 10 = 3 ∧ acceleratedOrbit 10 468 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_468 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 468) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_468.1, data_10_468.2]

/-- Complete interval computation for depth 10, residue 469. -/
theorem bounds_10_469 : exactInterval 10 469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_469 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 469) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_469 : oddCount 469 10 = 3 ∧ acceleratedOrbit 10 469 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_469 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 469) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_469.1, data_10_469.2]

/-- Complete interval computation for depth 10, residue 470. -/
theorem bounds_10_470 : exactInterval 10 470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_470 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 470) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_470 : oddCount 470 10 = 6 ∧ acceleratedOrbit 10 470 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_470 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 470) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_470.1, data_10_470.2]

/-- Complete interval computation for depth 10, residue 471. -/
theorem bounds_10_471 : exactInterval 10 471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_471 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 471) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_471 : oddCount 471 10 = 6 ∧ acceleratedOrbit 10 471 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_471 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 471) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_471.1, data_10_471.2]

/-- Complete interval computation for depth 10, residue 472. -/
theorem bounds_10_472 : exactInterval 10 472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_472 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 472) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_472 : oddCount 472 10 = 4 ∧ acceleratedOrbit 10 472 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_472 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 472) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_472.1, data_10_472.2]

/-- Complete interval computation for depth 10, residue 473. -/
theorem bounds_10_473 : exactInterval 10 473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_473 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 473) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_473 : oddCount 473 10 = 4 ∧ acceleratedOrbit 10 473 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_473 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 473) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_473.1, data_10_473.2]

/-- Complete interval computation for depth 10, residue 474. -/
theorem bounds_10_474 : exactInterval 10 474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_474 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 474) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_474 : oddCount 474 10 = 4 ∧ acceleratedOrbit 10 474 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_474 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 474) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_474.1, data_10_474.2]

/-- Complete interval computation for depth 10, residue 475. -/
theorem bounds_10_475 : exactInterval 10 475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_475 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 475) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_475 : oddCount 475 10 = 5 ∧ acceleratedOrbit 10 475 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_475 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 475) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_475.1, data_10_475.2]

end Collatz.Research.StoppingAtlas.Batch0031
