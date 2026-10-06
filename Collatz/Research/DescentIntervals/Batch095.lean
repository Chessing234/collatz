import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch095

/-- Complete interval computation for depth 9, residue 450. -/
theorem bounds_9_450 : exactInterval 9 450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_450 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 450) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_450 : oddCount 450 9 = 6 ∧ acceleratedOrbit 9 450 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_450 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 450) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_450.1, data_9_450.2]

/-- Complete interval computation for depth 9, residue 451. -/
theorem bounds_9_451 : exactInterval 9 451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_451 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 451) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_451 : oddCount 451 9 = 6 ∧ acceleratedOrbit 9 451 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_451 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 451) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_451.1, data_9_451.2]

/-- Complete interval computation for depth 9, residue 452. -/
theorem bounds_9_452 : exactInterval 9 452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_452 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 452) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_452 : oddCount 452 9 = 2 ∧ acceleratedOrbit 9 452 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_452 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 452) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_452.1, data_9_452.2]

/-- Complete interval computation for depth 9, residue 453. -/
theorem bounds_9_453 : exactInterval 9 453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_453 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 453) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_453 : oddCount 453 9 = 2 ∧ acceleratedOrbit 9 453 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_453 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 453) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_453.1, data_9_453.2]

/-- Complete interval computation for depth 9, residue 454. -/
theorem bounds_9_454 : exactInterval 9 454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_454 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 454) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_454 : oddCount 454 9 = 2 ∧ acceleratedOrbit 9 454 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_454 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 454) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_454.1, data_9_454.2]

/-- Complete interval computation for depth 9, residue 455. -/
theorem bounds_9_455 : exactInterval 9 455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_455 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 455) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_455 : oddCount 455 9 = 6 ∧ acceleratedOrbit 9 455 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_455 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 455) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_455.1, data_9_455.2]

/-- Complete interval computation for depth 9, residue 456. -/
theorem bounds_9_456 : exactInterval 9 456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_456 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 456) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_456 : oddCount 456 9 = 4 ∧ acceleratedOrbit 9 456 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_456 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 456) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_456.1, data_9_456.2]

/-- Complete interval computation for depth 9, residue 457. -/
theorem bounds_9_457 : exactInterval 9 457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_457 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 457) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_457 : oddCount 457 9 = 5 ∧ acceleratedOrbit 9 457 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_457 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 457) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_457.1, data_9_457.2]

/-- Complete interval computation for depth 9, residue 458. -/
theorem bounds_9_458 : exactInterval 9 458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_458 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 458) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_458 : oddCount 458 9 = 4 ∧ acceleratedOrbit 9 458 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_458 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 458) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_458.1, data_9_458.2]

/-- Complete interval computation for depth 9, residue 459. -/
theorem bounds_9_459 : exactInterval 9 459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_459 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 459) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_459 : oddCount 459 9 = 4 ∧ acceleratedOrbit 9 459 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_459 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 459) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_459.1, data_9_459.2]

end Collatz.Research.DescentIntervals.Batch095
