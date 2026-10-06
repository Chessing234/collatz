import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch093

/-- Complete interval computation for depth 9, residue 430. -/
theorem bounds_9_430 : exactInterval 9 430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_430 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 430) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_430 : oddCount 430 9 = 5 ∧ acceleratedOrbit 9 430 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_430 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 430) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_430.1, data_9_430.2]

/-- Complete interval computation for depth 9, residue 431. -/
theorem bounds_9_431 : exactInterval 9 431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_431 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 431) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_431 : oddCount 431 9 = 5 ∧ acceleratedOrbit 9 431 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_431 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 431) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_431.1, data_9_431.2]

/-- Complete interval computation for depth 9, residue 432. -/
theorem bounds_9_432 : exactInterval 9 432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_432 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 432) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_432 : oddCount 432 9 = 4 ∧ acceleratedOrbit 9 432 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_432 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 432) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_432.1, data_9_432.2]

/-- Complete interval computation for depth 9, residue 433. -/
theorem bounds_9_433 : exactInterval 9 433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_433 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 433) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_433 : oddCount 433 9 = 3 ∧ acceleratedOrbit 9 433 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_433 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 433) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_433.1, data_9_433.2]

/-- Complete interval computation for depth 9, residue 434. -/
theorem bounds_9_434 : exactInterval 9 434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_434 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 434) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_434 : oddCount 434 9 = 3 ∧ acceleratedOrbit 9 434 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_434 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 434) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_434.1, data_9_434.2]

/-- Complete interval computation for depth 9, residue 435. -/
theorem bounds_9_435 : exactInterval 9 435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_435 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 435) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_435 : oddCount 435 9 = 3 ∧ acceleratedOrbit 9 435 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_435 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 435) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_435.1, data_9_435.2]

/-- Complete interval computation for depth 9, residue 436. -/
theorem bounds_9_436 : exactInterval 9 436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_436 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 436) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_436 : oddCount 436 9 = 4 ∧ acceleratedOrbit 9 436 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_436 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 436) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_436.1, data_9_436.2]

/-- Complete interval computation for depth 9, residue 437. -/
theorem bounds_9_437 : exactInterval 9 437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_437 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 437) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_437 : oddCount 437 9 = 4 ∧ acceleratedOrbit 9 437 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_437 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 437) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_437.1, data_9_437.2]

/-- Complete interval computation for depth 9, residue 438. -/
theorem bounds_9_438 : exactInterval 9 438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_438 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 438) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_438 : oddCount 438 9 = 5 ∧ acceleratedOrbit 9 438 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_438 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 438) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_438.1, data_9_438.2]

/-- Complete interval computation for depth 9, residue 439. -/
theorem bounds_9_439 : exactInterval 9 439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_439 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 439) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_439 : oddCount 439 9 = 5 ∧ acceleratedOrbit 9 439 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_439 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 439) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_439.1, data_9_439.2]

end Collatz.Research.DescentIntervals.Batch093
