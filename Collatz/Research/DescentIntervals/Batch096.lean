import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch096

/-- Complete interval computation for depth 9, residue 460. -/
theorem bounds_9_460 : exactInterval 9 460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_460 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 460) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_460 : oddCount 460 9 = 4 ∧ acceleratedOrbit 9 460 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_460 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 460) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_460.1, data_9_460.2]

/-- Complete interval computation for depth 9, residue 461. -/
theorem bounds_9_461 : exactInterval 9 461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_461 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 461) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_461 : oddCount 461 9 = 4 ∧ acceleratedOrbit 9 461 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_461 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 461) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_461.1, data_9_461.2]

/-- Complete interval computation for depth 9, residue 462. -/
theorem bounds_9_462 : exactInterval 9 462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_462 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 462) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_462 : oddCount 462 9 = 6 ∧ acceleratedOrbit 9 462 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_462 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 462) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_462.1, data_9_462.2]

/-- Complete interval computation for depth 9, residue 463. -/
theorem bounds_9_463 : exactInterval 9 463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_463 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 463) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_463 : oddCount 463 9 = 6 ∧ acceleratedOrbit 9 463 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_463 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 463) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_463.1, data_9_463.2]

/-- Complete interval computation for depth 9, residue 464. -/
theorem bounds_9_464 : exactInterval 9 464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_464 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 464) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_464 : oddCount 464 9 = 3 ∧ acceleratedOrbit 9 464 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_464 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 464) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_464.1, data_9_464.2]

/-- Complete interval computation for depth 9, residue 465. -/
theorem bounds_9_465 : exactInterval 9 465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_465 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 465) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_465 : oddCount 465 9 = 4 ∧ acceleratedOrbit 9 465 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_465 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 465) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_465.1, data_9_465.2]

/-- Complete interval computation for depth 9, residue 466. -/
theorem bounds_9_466 : exactInterval 9 466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_466 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 466) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_466 : oddCount 466 9 = 6 ∧ acceleratedOrbit 9 466 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_466 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 466) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_466.1, data_9_466.2]

/-- Complete interval computation for depth 9, residue 467. -/
theorem bounds_9_467 : exactInterval 9 467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_467 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 467) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_467 : oddCount 467 9 = 6 ∧ acceleratedOrbit 9 467 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_467 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 467) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_467.1, data_9_467.2]

/-- Complete interval computation for depth 9, residue 468. -/
theorem bounds_9_468 : exactInterval 9 468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_468 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 468) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_468 : oddCount 468 9 = 3 ∧ acceleratedOrbit 9 468 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_468 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 468) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_468.1, data_9_468.2]

/-- Complete interval computation for depth 9, residue 469. -/
theorem bounds_9_469 : exactInterval 9 469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_469 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 469) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_469 : oddCount 469 9 = 3 ∧ acceleratedOrbit 9 469 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_469 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 469) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_469.1, data_9_469.2]

/-- Complete interval computation for depth 9, residue 470. -/
theorem bounds_9_470 : exactInterval 9 470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_470 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 470) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_470 : oddCount 470 9 = 6 ∧ acceleratedOrbit 9 470 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_470 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 470) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_470.1, data_9_470.2]

end Collatz.Research.DescentIntervals.Batch096
