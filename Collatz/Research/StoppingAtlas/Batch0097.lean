import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0097

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 450. -/
theorem bounds_11_450 : exactInterval 11 450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_450 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 450) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_450 : oddCount 450 11 = 8 ∧ acceleratedOrbit 11 450 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_450 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 450) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_450.1, data_11_450.2]

/-- Complete interval computation for depth 11, residue 451. -/
theorem bounds_11_451 : exactInterval 11 451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_451 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 451) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_451 : oddCount 451 11 = 8 ∧ acceleratedOrbit 11 451 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_451 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 451) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_451.1, data_11_451.2]

/-- Complete interval computation for depth 11, residue 452. -/
theorem bounds_11_452 : exactInterval 11 452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_452 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 452) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_452 : oddCount 452 11 = 2 ∧ acceleratedOrbit 11 452 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_452 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 452) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_452.1, data_11_452.2]

/-- Complete interval computation for depth 11, residue 453. -/
theorem bounds_11_453 : exactInterval 11 453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_453 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 453) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_453 : oddCount 453 11 = 2 ∧ acceleratedOrbit 11 453 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_453 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 453) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_453.1, data_11_453.2]

/-- Complete interval computation for depth 11, residue 454. -/
theorem bounds_11_454 : exactInterval 11 454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_454 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 454) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_454 : oddCount 454 11 = 2 ∧ acceleratedOrbit 11 454 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_454 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 454) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_454.1, data_11_454.2]

/-- Complete interval computation for depth 11, residue 455. -/
theorem bounds_11_455 : exactInterval 11 455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_455 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 455) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_455 : oddCount 455 11 = 7 ∧ acceleratedOrbit 11 455 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_455 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 455) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_455.1, data_11_455.2]

/-- Complete interval computation for depth 11, residue 456. -/
theorem bounds_11_456 : exactInterval 11 456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_456 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 456) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_456 : oddCount 456 11 = 5 ∧ acceleratedOrbit 11 456 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_456 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 456) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_456.1, data_11_456.2]

/-- Complete interval computation for depth 11, residue 457. -/
theorem bounds_11_457 : exactInterval 11 457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_457 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 457) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_457 : oddCount 457 11 = 6 ∧ acceleratedOrbit 11 457 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_457 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 457) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_457.1, data_11_457.2]

/-- Complete interval computation for depth 11, residue 458. -/
theorem bounds_11_458 : exactInterval 11 458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_458 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 458) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_458 : oddCount 458 11 = 5 ∧ acceleratedOrbit 11 458 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_458 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 458) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_458.1, data_11_458.2]

/-- Complete interval computation for depth 11, residue 459. -/
theorem bounds_11_459 : exactInterval 11 459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_459 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 459) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_459 : oddCount 459 11 = 5 ∧ acceleratedOrbit 11 459 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_459 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 459) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_459.1, data_11_459.2]

/-- Complete interval computation for depth 11, residue 460. -/
theorem bounds_11_460 : exactInterval 11 460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_460 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 460) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_460 : oddCount 460 11 = 5 ∧ acceleratedOrbit 11 460 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_460 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 460) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_460.1, data_11_460.2]

/-- Complete interval computation for depth 11, residue 461. -/
theorem bounds_11_461 : exactInterval 11 461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_461 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 461) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_461 : oddCount 461 11 = 5 ∧ acceleratedOrbit 11 461 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_461 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 461) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_461.1, data_11_461.2]

/-- Complete interval computation for depth 11, residue 462. -/
theorem bounds_11_462 : exactInterval 11 462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_462 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 462) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_462 : oddCount 462 11 = 7 ∧ acceleratedOrbit 11 462 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_462 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 462) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_462.1, data_11_462.2]

/-- Complete interval computation for depth 11, residue 463. -/
theorem bounds_11_463 : exactInterval 11 463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_463 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 463) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_463 : oddCount 463 11 = 7 ∧ acceleratedOrbit 11 463 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_463 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 463) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_463.1, data_11_463.2]

/-- Complete interval computation for depth 11, residue 464. -/
theorem bounds_11_464 : exactInterval 11 464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_464 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 464) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_464 : oddCount 464 11 = 4 ∧ acceleratedOrbit 11 464 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_464 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 464) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_464.1, data_11_464.2]

end Collatz.Research.StoppingAtlas.Batch0097
