import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch098

/-- Complete interval computation for depth 9, residue 481. -/
theorem bounds_9_481 : exactInterval 9 481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_481 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 481) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_481 : oddCount 481 9 = 6 ∧ acceleratedOrbit 9 481 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_481 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 481) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_481.1, data_9_481.2]

/-- Complete interval computation for depth 9, residue 482. -/
theorem bounds_9_482 : exactInterval 9 482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_482 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 482) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_482 : oddCount 482 9 = 3 ∧ acceleratedOrbit 9 482 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_482 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 482) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_482.1, data_9_482.2]

/-- Complete interval computation for depth 9, residue 483. -/
theorem bounds_9_483 : exactInterval 9 483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_483 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 483) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_483 : oddCount 483 9 = 3 ∧ acceleratedOrbit 9 483 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_483 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 483) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_483.1, data_9_483.2]

/-- Complete interval computation for depth 9, residue 484. -/
theorem bounds_9_484 : exactInterval 9 484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_484 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 484) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_484 : oddCount 484 9 = 5 ∧ acceleratedOrbit 9 484 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_484 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 484) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_484.1, data_9_484.2]

/-- Complete interval computation for depth 9, residue 485. -/
theorem bounds_9_485 : exactInterval 9 485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_485 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 485) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_485 : oddCount 485 9 = 5 ∧ acceleratedOrbit 9 485 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_485 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 485) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_485.1, data_9_485.2]

/-- Complete interval computation for depth 9, residue 486. -/
theorem bounds_9_486 : exactInterval 9 486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_486 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 486) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_486 : oddCount 486 9 = 5 ∧ acceleratedOrbit 9 486 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_486 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 486) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_486.1, data_9_486.2]

/-- Complete interval computation for depth 9, residue 487. -/
theorem bounds_9_487 : exactInterval 9 487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_487 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 487) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_487 : oddCount 487 9 = 6 ∧ acceleratedOrbit 9 487 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_487 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 487) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_487.1, data_9_487.2]

/-- Complete interval computation for depth 9, residue 488. -/
theorem bounds_9_488 : exactInterval 9 488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_488 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 488) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_488 : oddCount 488 9 = 4 ∧ acceleratedOrbit 9 488 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_488 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 488) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_488.1, data_9_488.2]

/-- Complete interval computation for depth 9, residue 489. -/
theorem bounds_9_489 : exactInterval 9 489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_489 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 489) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_489 : oddCount 489 9 = 7 ∧ acceleratedOrbit 9 489 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_489 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 489) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_489.1, data_9_489.2]

/-- Complete interval computation for depth 9, residue 490. -/
theorem bounds_9_490 : exactInterval 9 490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_490 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 490) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_490 : oddCount 490 9 = 4 ∧ acceleratedOrbit 9 490 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_490 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 490) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_490.1, data_9_490.2]

end Collatz.Research.DescentIntervals.Batch098
