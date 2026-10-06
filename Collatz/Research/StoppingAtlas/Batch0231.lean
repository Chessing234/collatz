import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0231

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 460. -/
theorem bounds_12_460 : exactInterval 12 460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_460 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 460) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_460 : oddCount 460 12 = 5 ∧ acceleratedOrbit 12 460 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_460 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 460) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_460.1, data_12_460.2]

/-- Complete interval computation for depth 12, residue 461. -/
theorem bounds_12_461 : exactInterval 12 461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_461 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 461) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_461 : oddCount 461 12 = 5 ∧ acceleratedOrbit 12 461 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_461 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 461) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_461.1, data_12_461.2]

/-- Complete interval computation for depth 12, residue 462. -/
theorem bounds_12_462 : exactInterval 12 462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_462 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 462) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_462 : oddCount 462 12 = 7 ∧ acceleratedOrbit 12 462 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_462 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 462) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_462.1, data_12_462.2]

/-- Complete interval computation for depth 12, residue 463. -/
theorem bounds_12_463 : exactInterval 12 463 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_463 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 463) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_463 : oddCount 463 12 = 7 ∧ acceleratedOrbit 12 463 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_463 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 463) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_463.1, data_12_463.2]

/-- Complete interval computation for depth 12, residue 464. -/
theorem bounds_12_464 : exactInterval 12 464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_464 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 464) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_464 : oddCount 464 12 = 4 ∧ acceleratedOrbit 12 464 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_464 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 464) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_464.1, data_12_464.2]

/-- Complete interval computation for depth 12, residue 465. -/
theorem bounds_12_465 : exactInterval 12 465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_465 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 465) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_465 : oddCount 465 12 = 5 ∧ acceleratedOrbit 12 465 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_465 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 465) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_465.1, data_12_465.2]

/-- Complete interval computation for depth 12, residue 466. -/
theorem bounds_12_466 : exactInterval 12 466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_466 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 466) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_466 : oddCount 466 12 = 7 ∧ acceleratedOrbit 12 466 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_466 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 466) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_466.1, data_12_466.2]

/-- Complete interval computation for depth 12, residue 467. -/
theorem bounds_12_467 : exactInterval 12 467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_467 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 467) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_467 : oddCount 467 12 = 7 ∧ acceleratedOrbit 12 467 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_467 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 467) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_467.1, data_12_467.2]

/-- Complete interval computation for depth 12, residue 468. -/
theorem bounds_12_468 : exactInterval 12 468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_468 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 468) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_468 : oddCount 468 12 = 4 ∧ acceleratedOrbit 12 468 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_468 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 468) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_468.1, data_12_468.2]

/-- Complete interval computation for depth 12, residue 469. -/
theorem bounds_12_469 : exactInterval 12 469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_469 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 469) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_469 : oddCount 469 12 = 4 ∧ acceleratedOrbit 12 469 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_469 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 469) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_469.1, data_12_469.2]

/-- Complete interval computation for depth 12, residue 470. -/
theorem bounds_12_470 : exactInterval 12 470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_470 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 470) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_470 : oddCount 470 12 = 7 ∧ acceleratedOrbit 12 470 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_470 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 470) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_470.1, data_12_470.2]

/-- Complete interval computation for depth 12, residue 471. -/
theorem bounds_12_471 : exactInterval 12 471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_471 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 471) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_471 : oddCount 471 12 = 7 ∧ acceleratedOrbit 12 471 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_471 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 471) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_471.1, data_12_471.2]

/-- Complete interval computation for depth 12, residue 472. -/
theorem bounds_12_472 : exactInterval 12 472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_472 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 472) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_472 : oddCount 472 12 = 5 ∧ acceleratedOrbit 12 472 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_472 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 472) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_472.1, data_12_472.2]

/-- Complete interval computation for depth 12, residue 473. -/
theorem bounds_12_473 : exactInterval 12 473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_473 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 473) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_473 : oddCount 473 12 = 5 ∧ acceleratedOrbit 12 473 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_473 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 473) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_473.1, data_12_473.2]

/-- Complete interval computation for depth 12, residue 474. -/
theorem bounds_12_474 : exactInterval 12 474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_474 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 474) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_474 : oddCount 474 12 = 5 ∧ acceleratedOrbit 12 474 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_474 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 474) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_474.1, data_12_474.2]

/-- Complete interval computation for depth 12, residue 475. -/
theorem bounds_12_475 : exactInterval 12 475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_475 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 475) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_475 : oddCount 475 12 = 6 ∧ acceleratedOrbit 12 475 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_475 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 475) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_475.1, data_12_475.2]

end Collatz.Research.StoppingAtlas.Batch0231
