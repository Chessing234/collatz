import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch097

/-- Complete interval computation for depth 9, residue 471. -/
theorem bounds_9_471 : exactInterval 9 471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_471 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 471) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_471 : oddCount 471 9 = 6 ∧ acceleratedOrbit 9 471 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_471 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 471) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_471.1, data_9_471.2]

/-- Complete interval computation for depth 9, residue 472. -/
theorem bounds_9_472 : exactInterval 9 472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_472 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 472) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_472 : oddCount 472 9 = 4 ∧ acceleratedOrbit 9 472 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_472 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 472) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_472.1, data_9_472.2]

/-- Complete interval computation for depth 9, residue 473. -/
theorem bounds_9_473 : exactInterval 9 473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_473 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 473) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_473 : oddCount 473 9 = 3 ∧ acceleratedOrbit 9 473 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_473 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 473) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_473.1, data_9_473.2]

/-- Complete interval computation for depth 9, residue 474. -/
theorem bounds_9_474 : exactInterval 9 474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_474 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 474) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_474 : oddCount 474 9 = 4 ∧ acceleratedOrbit 9 474 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_474 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 474) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_474.1, data_9_474.2]

/-- Complete interval computation for depth 9, residue 475. -/
theorem bounds_9_475 : exactInterval 9 475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_475 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 475) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_475 : oddCount 475 9 = 5 ∧ acceleratedOrbit 9 475 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_475 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 475) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_475.1, data_9_475.2]

/-- Complete interval computation for depth 9, residue 476. -/
theorem bounds_9_476 : exactInterval 9 476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_476 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 476) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_476 : oddCount 476 9 = 4 ∧ acceleratedOrbit 9 476 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_476 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 476) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_476.1, data_9_476.2]

/-- Complete interval computation for depth 9, residue 477. -/
theorem bounds_9_477 : exactInterval 9 477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_477 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 477) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_477 : oddCount 477 9 = 4 ∧ acceleratedOrbit 9 477 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_477 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 477) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_477.1, data_9_477.2]

/-- Complete interval computation for depth 9, residue 478. -/
theorem bounds_9_478 : exactInterval 9 478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_478 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 478) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_478 : oddCount 478 9 = 7 ∧ acceleratedOrbit 9 478 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_478 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 478) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_478.1, data_9_478.2]

/-- Complete interval computation for depth 9, residue 479. -/
theorem bounds_9_479 : exactInterval 9 479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_479 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 479) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_479 : oddCount 479 9 = 7 ∧ acceleratedOrbit 9 479 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_479 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 479) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_479.1, data_9_479.2]

/-- Complete interval computation for depth 9, residue 480. -/
theorem bounds_9_480 : exactInterval 9 480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_480 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 480) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_480 : oddCount 480 9 = 4 ∧ acceleratedOrbit 9 480 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_480 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 480) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_480.1, data_9_480.2]

end Collatz.Research.DescentIntervals.Batch097
