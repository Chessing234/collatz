import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0497

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 450. -/
theorem bounds_13_450 : exactInterval 13 450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_450 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 450) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_450 : oddCount 450 13 = 9 ∧ acceleratedOrbit 13 450 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_450 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 450) = 3 ^ 9 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_450.1, data_13_450.2]

/-- Complete interval computation for depth 13, residue 451. -/
theorem bounds_13_451 : exactInterval 13 451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_451 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 451) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_451 : oddCount 451 13 = 9 ∧ acceleratedOrbit 13 451 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_451 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 451) = 3 ^ 9 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_451.1, data_13_451.2]

/-- Complete interval computation for depth 13, residue 452. -/
theorem bounds_13_452 : exactInterval 13 452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_452 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 452) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_452 : oddCount 452 13 = 3 ∧ acceleratedOrbit 13 452 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_452 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 452) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_452.1, data_13_452.2]

/-- Complete interval computation for depth 13, residue 453. -/
theorem bounds_13_453 : exactInterval 13 453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_453 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 453) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_453 : oddCount 453 13 = 3 ∧ acceleratedOrbit 13 453 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_453 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 453) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_453.1, data_13_453.2]

/-- Complete interval computation for depth 13, residue 454. -/
theorem bounds_13_454 : exactInterval 13 454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_454 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 454) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_454 : oddCount 454 13 = 3 ∧ acceleratedOrbit 13 454 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_454 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 454) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_454.1, data_13_454.2]

/-- Complete interval computation for depth 13, residue 455. -/
theorem bounds_13_455 : exactInterval 13 455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_455 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 455) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_455 : oddCount 455 13 = 7 ∧ acceleratedOrbit 13 455 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_455 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 455) = 3 ^ 7 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_455.1, data_13_455.2]

/-- Complete interval computation for depth 13, residue 456. -/
theorem bounds_13_456 : exactInterval 13 456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_456 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 456) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_456 : oddCount 456 13 = 5 ∧ acceleratedOrbit 13 456 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_456 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 456) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_456.1, data_13_456.2]

/-- Complete interval computation for depth 13, residue 457. -/
theorem bounds_13_457 : exactInterval 13 457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_457 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 457) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_457 : oddCount 457 13 = 6 ∧ acceleratedOrbit 13 457 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_457 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 457) = 3 ^ 6 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_457.1, data_13_457.2]

/-- Complete interval computation for depth 13, residue 458. -/
theorem bounds_13_458 : exactInterval 13 458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_458 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 458) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_458 : oddCount 458 13 = 5 ∧ acceleratedOrbit 13 458 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_458 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 458) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_458.1, data_13_458.2]

/-- Complete interval computation for depth 13, residue 459. -/
theorem bounds_13_459 : exactInterval 13 459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_459 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 459) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_459 : oddCount 459 13 = 7 ∧ acceleratedOrbit 13 459 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_459 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 459) = 3 ^ 7 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_459.1, data_13_459.2]

/-- Complete interval computation for depth 13, residue 460. -/
theorem bounds_13_460 : exactInterval 13 460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_460 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 460) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_460 : oddCount 460 13 = 5 ∧ acceleratedOrbit 13 460 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_460 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 460) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_460.1, data_13_460.2]

/-- Complete interval computation for depth 13, residue 461. -/
theorem bounds_13_461 : exactInterval 13 461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_461 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 461) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_461 : oddCount 461 13 = 5 ∧ acceleratedOrbit 13 461 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_461 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 461) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_461.1, data_13_461.2]

/-- Complete interval computation for depth 13, residue 462. -/
theorem bounds_13_462 : exactInterval 13 462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_462 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 462) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_462 : oddCount 462 13 = 7 ∧ acceleratedOrbit 13 462 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_462 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 462) = 3 ^ 7 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_462.1, data_13_462.2]

/-- Complete interval computation for depth 13, residue 463. -/
theorem bounds_13_463 : exactInterval 13 463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_463 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 463) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_463 : oddCount 463 13 = 7 ∧ acceleratedOrbit 13 463 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_463 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 463) = 3 ^ 7 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_463.1, data_13_463.2]

/-- Complete interval computation for depth 13, residue 464. -/
theorem bounds_13_464 : exactInterval 13 464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_464 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 464) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_464 : oddCount 464 13 = 4 ∧ acceleratedOrbit 13 464 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_464 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 464) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_464.1, data_13_464.2]

end Collatz.Research.StoppingAtlas.Batch0497
