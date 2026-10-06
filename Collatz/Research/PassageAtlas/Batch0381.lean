import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0381

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12451. -/
theorem bounds_15_12451 : exactInterval 15 12451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12451 : oddCount 12451 15 = 7 ∧ acceleratedOrbit 15 12451 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12451) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12451.1, data_15_12451.2]

/-- Complete interval computation for depth 15, residue 12452. -/
theorem bounds_15_12452 : exactInterval 15 12452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12452 : oddCount 12452 15 = 8 ∧ acceleratedOrbit 15 12452 = 2495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12452) = 3 ^ 8 * m + 2495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12452.1, data_15_12452.2]

/-- Complete interval computation for depth 15, residue 12453. -/
theorem bounds_15_12453 : exactInterval 15 12453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12453 : oddCount 12453 15 = 8 ∧ acceleratedOrbit 15 12453 = 2495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12453) = 3 ^ 8 * m + 2495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12453.1, data_15_12453.2]

/-- Complete interval computation for depth 15, residue 12454. -/
theorem bounds_15_12454 : exactInterval 15 12454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12454 : oddCount 12454 15 = 8 ∧ acceleratedOrbit 15 12454 = 2495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12454) = 3 ^ 8 * m + 2495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12454.1, data_15_12454.2]

/-- Complete interval computation for depth 15, residue 12455. -/
theorem bounds_15_12455 : exactInterval 15 12455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12455 : oddCount 12455 15 = 10 ∧ acceleratedOrbit 15 12455 = 22447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12455) = 3 ^ 10 * m + 22447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12455.1, data_15_12455.2]

/-- Complete interval computation for depth 15, residue 12456. -/
theorem bounds_15_12456 : exactInterval 15 12456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12456 : oddCount 12456 15 = 5 ∧ acceleratedOrbit 15 12456 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12456) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12456.1, data_15_12456.2]

/-- Complete interval computation for depth 15, residue 12457. -/
theorem bounds_15_12457 : exactInterval 15 12457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12457 : oddCount 12457 15 = 10 ∧ acceleratedOrbit 15 12457 = 22451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12457) = 3 ^ 10 * m + 22451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12457.1, data_15_12457.2]

/-- Complete interval computation for depth 15, residue 12458. -/
theorem bounds_15_12458 : exactInterval 15 12458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12458 : oddCount 12458 15 = 5 ∧ acceleratedOrbit 15 12458 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12458) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12458.1, data_15_12458.2]

/-- Complete interval computation for depth 15, residue 12459. -/
theorem bounds_15_12459 : exactInterval 15 12459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12459 : oddCount 12459 15 = 7 ∧ acceleratedOrbit 15 12459 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12459) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12459.1, data_15_12459.2]

/-- Complete interval computation for depth 15, residue 12460. -/
theorem bounds_15_12460 : exactInterval 15 12460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12460 : oddCount 12460 15 = 6 ∧ acceleratedOrbit 15 12460 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12460) = 3 ^ 6 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12460.1, data_15_12460.2]

/-- Complete interval computation for depth 15, residue 12461. -/
theorem bounds_15_12461 : exactInterval 15 12461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12461 : oddCount 12461 15 = 6 ∧ acceleratedOrbit 15 12461 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12461) = 3 ^ 6 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12461.1, data_15_12461.2]

/-- Complete interval computation for depth 15, residue 12462. -/
theorem bounds_15_12462 : exactInterval 15 12462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12462 : oddCount 12462 15 = 6 ∧ acceleratedOrbit 15 12462 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12462) = 3 ^ 6 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12462.1, data_15_12462.2]

/-- Complete interval computation for depth 15, residue 12463. -/
theorem bounds_15_12463 : exactInterval 15 12463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12463 : oddCount 12463 15 = 10 ∧ acceleratedOrbit 15 12463 = 22463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12463) = 3 ^ 10 * m + 22463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12463.1, data_15_12463.2]

/-- Complete interval computation for depth 15, residue 12464. -/
theorem bounds_15_12464 : exactInterval 15 12464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12464 : oddCount 12464 15 = 7 ∧ acceleratedOrbit 15 12464 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12464) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12464.1, data_15_12464.2]

/-- Complete interval computation for depth 15, residue 12465. -/
theorem bounds_15_12465 : exactInterval 15 12465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12465 : oddCount 12465 15 = 6 ∧ acceleratedOrbit 15 12465 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12465) = 3 ^ 6 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12465.1, data_15_12465.2]

/-- Complete interval computation for depth 15, residue 12466. -/
theorem bounds_15_12466 : exactInterval 15 12466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12466 : oddCount 12466 15 = 6 ∧ acceleratedOrbit 15 12466 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12466) = 3 ^ 6 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12466.1, data_15_12466.2]

/-- Complete interval computation for depth 15, residue 12467. -/
theorem bounds_15_12467 : exactInterval 15 12467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12467 : oddCount 12467 15 = 6 ∧ acceleratedOrbit 15 12467 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12467) = 3 ^ 6 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12467.1, data_15_12467.2]

/-- Complete interval computation for depth 15, residue 12468. -/
theorem bounds_15_12468 : exactInterval 15 12468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12468 : oddCount 12468 15 = 7 ∧ acceleratedOrbit 15 12468 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12468) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12468.1, data_15_12468.2]

/-- Complete interval computation for depth 15, residue 12469. -/
theorem bounds_15_12469 : exactInterval 15 12469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12469 : oddCount 12469 15 = 7 ∧ acceleratedOrbit 15 12469 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12469) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12469.1, data_15_12469.2]

/-- Complete interval computation for depth 15, residue 12470. -/
theorem bounds_15_12470 : exactInterval 15 12470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12470 : oddCount 12470 15 = 11 ∧ acceleratedOrbit 15 12470 = 67432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12470) = 3 ^ 11 * m + 67432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12470.1, data_15_12470.2]

/-- Complete interval computation for depth 15, residue 12471. -/
theorem bounds_15_12471 : exactInterval 15 12471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12471 : oddCount 12471 15 = 11 ∧ acceleratedOrbit 15 12471 = 67432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12471) = 3 ^ 11 * m + 67432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12471.1, data_15_12471.2]

/-- Complete interval computation for depth 15, residue 12472. -/
theorem bounds_15_12472 : exactInterval 15 12472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12472 : oddCount 12472 15 = 7 ∧ acceleratedOrbit 15 12472 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12472) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12472.1, data_15_12472.2]

/-- Complete interval computation for depth 15, residue 12473. -/
theorem bounds_15_12473 : exactInterval 15 12473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12473 : oddCount 12473 15 = 9 ∧ acceleratedOrbit 15 12473 = 7496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12473) = 3 ^ 9 * m + 7496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12473.1, data_15_12473.2]

/-- Complete interval computation for depth 15, residue 12474. -/
theorem bounds_15_12474 : exactInterval 15 12474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12474 : oddCount 12474 15 = 7 ∧ acceleratedOrbit 15 12474 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12474) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12474.1, data_15_12474.2]

/-- Complete interval computation for depth 15, residue 12475. -/
theorem bounds_15_12475 : exactInterval 15 12475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12475 : oddCount 12475 15 = 9 ∧ acceleratedOrbit 15 12475 = 7496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12475) = 3 ^ 9 * m + 7496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12475.1, data_15_12475.2]

/-- Complete interval computation for depth 15, residue 12476. -/
theorem bounds_15_12476 : exactInterval 15 12476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12476 : oddCount 12476 15 = 7 ∧ acceleratedOrbit 15 12476 = 833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12476) = 3 ^ 7 * m + 833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12476.1, data_15_12476.2]

/-- Complete interval computation for depth 15, residue 12477. -/
theorem bounds_15_12477 : exactInterval 15 12477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12477 : oddCount 12477 15 = 7 ∧ acceleratedOrbit 15 12477 = 833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12477) = 3 ^ 7 * m + 833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12477.1, data_15_12477.2]

/-- Complete interval computation for depth 15, residue 12478. -/
theorem bounds_15_12478 : exactInterval 15 12478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12478 : oddCount 12478 15 = 7 ∧ acceleratedOrbit 15 12478 = 833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12478) = 3 ^ 7 * m + 833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12478.1, data_15_12478.2]

/-- Complete interval computation for depth 15, residue 12479. -/
theorem bounds_15_12479 : exactInterval 15 12479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12479 : oddCount 12479 15 = 11 ∧ acceleratedOrbit 15 12479 = 67472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12479) = 3 ^ 11 * m + 67472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12479.1, data_15_12479.2]

/-- Complete interval computation for depth 15, residue 12480. -/
theorem bounds_15_12480 : exactInterval 15 12480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12480 : oddCount 12480 15 = 5 ∧ acceleratedOrbit 15 12480 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12480) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12480.1, data_15_12480.2]

/-- Complete interval computation for depth 15, residue 12481. -/
theorem bounds_15_12481 : exactInterval 15 12481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12481 : oddCount 12481 15 = 8 ∧ acceleratedOrbit 15 12481 = 2501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12481) = 3 ^ 8 * m + 2501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12481.1, data_15_12481.2]

/-- Complete interval computation for depth 15, residue 12482. -/
theorem bounds_15_12482 : exactInterval 15 12482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12482 : oddCount 12482 15 = 8 ∧ acceleratedOrbit 15 12482 = 2501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12482) = 3 ^ 8 * m + 2501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12482.1, data_15_12482.2]

/-- Complete interval computation for depth 15, residue 12483. -/
theorem bounds_15_12483 : exactInterval 15 12483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12483 : oddCount 12483 15 = 8 ∧ acceleratedOrbit 15 12483 = 2501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12483) = 3 ^ 8 * m + 2501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12483.1, data_15_12483.2]

end Collatz.Research.PassageAtlas.Batch0381
