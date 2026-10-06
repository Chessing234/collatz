import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0320

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10452. -/
theorem bounds_15_10452 : exactInterval 15 10452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10452 : oddCount 10452 15 = 5 ∧ acceleratedOrbit 15 10452 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10452) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10452.1, data_15_10452.2]

/-- Complete interval computation for depth 15, residue 10453. -/
theorem bounds_15_10453 : exactInterval 15 10453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10453 : oddCount 10453 15 = 5 ∧ acceleratedOrbit 15 10453 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10453) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10453.1, data_15_10453.2]

/-- Complete interval computation for depth 15, residue 10454. -/
theorem bounds_15_10454 : exactInterval 15 10454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10454 : oddCount 10454 15 = 7 ∧ acceleratedOrbit 15 10454 = 698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10454) = 3 ^ 7 * m + 698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10454.1, data_15_10454.2]

/-- Complete interval computation for depth 15, residue 10455. -/
theorem bounds_15_10455 : exactInterval 15 10455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10455 : oddCount 10455 15 = 7 ∧ acceleratedOrbit 15 10455 = 698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10455) = 3 ^ 7 * m + 698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10455.1, data_15_10455.2]

/-- Complete interval computation for depth 15, residue 10456. -/
theorem bounds_15_10456 : exactInterval 15 10456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10456 : oddCount 10456 15 = 10 ∧ acceleratedOrbit 15 10456 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10456) = 3 ^ 10 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10456.1, data_15_10456.2]

/-- Complete interval computation for depth 15, residue 10457. -/
theorem bounds_15_10457 : exactInterval 15 10457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10457 : oddCount 10457 15 = 8 ∧ acceleratedOrbit 15 10457 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10457) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10457.1, data_15_10457.2]

/-- Complete interval computation for depth 15, residue 10458. -/
theorem bounds_15_10458 : exactInterval 15 10458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10458 : oddCount 10458 15 = 10 ∧ acceleratedOrbit 15 10458 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10458) = 3 ^ 10 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10458.1, data_15_10458.2]

/-- Complete interval computation for depth 15, residue 10459. -/
theorem bounds_15_10459 : exactInterval 15 10459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10459 : oddCount 10459 15 = 9 ∧ acceleratedOrbit 15 10459 = 6284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10459) = 3 ^ 9 * m + 6284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10459.1, data_15_10459.2]

/-- Complete interval computation for depth 15, residue 10460. -/
theorem bounds_15_10460 : exactInterval 15 10460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10460 : oddCount 10460 15 = 10 ∧ acceleratedOrbit 15 10460 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10460) = 3 ^ 10 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10460.1, data_15_10460.2]

/-- Complete interval computation for depth 15, residue 10461. -/
theorem bounds_15_10461 : exactInterval 15 10461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10461 : oddCount 10461 15 = 10 ∧ acceleratedOrbit 15 10461 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10461) = 3 ^ 10 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10461.1, data_15_10461.2]

/-- Complete interval computation for depth 15, residue 10462. -/
theorem bounds_15_10462 : exactInterval 15 10462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10462 : oddCount 10462 15 = 9 ∧ acceleratedOrbit 15 10462 = 6286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10462) = 3 ^ 9 * m + 6286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10462.1, data_15_10462.2]

/-- Complete interval computation for depth 15, residue 10463. -/
theorem bounds_15_10463 : exactInterval 15 10463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10463 : oddCount 10463 15 = 9 ∧ acceleratedOrbit 15 10463 = 6286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10463) = 3 ^ 9 * m + 6286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10463.1, data_15_10463.2]

/-- Complete interval computation for depth 15, residue 10464. -/
theorem bounds_15_10464 : exactInterval 15 10464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10464 : oddCount 10464 15 = 8 ∧ acceleratedOrbit 15 10464 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10464) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10464.1, data_15_10464.2]

/-- Complete interval computation for depth 15, residue 10465. -/
theorem bounds_15_10465 : exactInterval 15 10465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10465 : oddCount 10465 15 = 12 ∧ acceleratedOrbit 15 10465 = 169766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10465) = 3 ^ 12 * m + 169766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10465.1, data_15_10465.2]

/-- Complete interval computation for depth 15, residue 10466. -/
theorem bounds_15_10466 : exactInterval 15 10466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10466 : oddCount 10466 15 = 5 ∧ acceleratedOrbit 15 10466 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10466) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10466.1, data_15_10466.2]

/-- Complete interval computation for depth 15, residue 10467. -/
theorem bounds_15_10467 : exactInterval 15 10467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10467 : oddCount 10467 15 = 5 ∧ acceleratedOrbit 15 10467 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10467) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10467.1, data_15_10467.2]

/-- Complete interval computation for depth 15, residue 10468. -/
theorem bounds_15_10468 : exactInterval 15 10468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10468 : oddCount 10468 15 = 8 ∧ acceleratedOrbit 15 10468 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10468) = 3 ^ 8 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10468.1, data_15_10468.2]

/-- Complete interval computation for depth 15, residue 10469. -/
theorem bounds_15_10469 : exactInterval 15 10469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10469 : oddCount 10469 15 = 8 ∧ acceleratedOrbit 15 10469 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10469) = 3 ^ 8 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10469.1, data_15_10469.2]

/-- Complete interval computation for depth 15, residue 10470. -/
theorem bounds_15_10470 : exactInterval 15 10470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10470 : oddCount 10470 15 = 8 ∧ acceleratedOrbit 15 10470 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10470) = 3 ^ 8 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10470.1, data_15_10470.2]

/-- Complete interval computation for depth 15, residue 10471. -/
theorem bounds_15_10471 : exactInterval 15 10471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10471 : oddCount 10471 15 = 11 ∧ acceleratedOrbit 15 10471 = 56618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10471) = 3 ^ 11 * m + 56618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10471.1, data_15_10471.2]

/-- Complete interval computation for depth 15, residue 10472. -/
theorem bounds_15_10472 : exactInterval 15 10472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10472 : oddCount 10472 15 = 8 ∧ acceleratedOrbit 15 10472 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10472) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10472.1, data_15_10472.2]

/-- Complete interval computation for depth 15, residue 10473. -/
theorem bounds_15_10473 : exactInterval 15 10473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10473 : oddCount 10473 15 = 9 ∧ acceleratedOrbit 15 10473 = 6293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10473) = 3 ^ 9 * m + 6293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10473.1, data_15_10473.2]

/-- Complete interval computation for depth 15, residue 10474. -/
theorem bounds_15_10474 : exactInterval 15 10474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10474 : oddCount 10474 15 = 8 ∧ acceleratedOrbit 15 10474 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10474) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10474.1, data_15_10474.2]

/-- Complete interval computation for depth 15, residue 10475. -/
theorem bounds_15_10475 : exactInterval 15 10475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10475 : oddCount 10475 15 = 8 ∧ acceleratedOrbit 15 10475 = 2098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10475) = 3 ^ 8 * m + 2098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10475.1, data_15_10475.2]

/-- Complete interval computation for depth 15, residue 10476. -/
theorem bounds_15_10476 : exactInterval 15 10476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10476 : oddCount 10476 15 = 7 ∧ acceleratedOrbit 15 10476 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10476) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10476.1, data_15_10476.2]

/-- Complete interval computation for depth 15, residue 10477. -/
theorem bounds_15_10477 : exactInterval 15 10477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10477 : oddCount 10477 15 = 7 ∧ acceleratedOrbit 15 10477 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10477) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10477.1, data_15_10477.2]

/-- Complete interval computation for depth 15, residue 10478. -/
theorem bounds_15_10478 : exactInterval 15 10478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10478 : oddCount 10478 15 = 7 ∧ acceleratedOrbit 15 10478 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10478) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10478.1, data_15_10478.2]

/-- Complete interval computation for depth 15, residue 10479. -/
theorem bounds_15_10479 : exactInterval 15 10479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10479 : oddCount 10479 15 = 11 ∧ acceleratedOrbit 15 10479 = 56657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10479) = 3 ^ 11 * m + 56657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10479.1, data_15_10479.2]

/-- Complete interval computation for depth 15, residue 10480. -/
theorem bounds_15_10480 : exactInterval 15 10480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10480 : oddCount 10480 15 = 8 ∧ acceleratedOrbit 15 10480 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10480) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10480.1, data_15_10480.2]

/-- Complete interval computation for depth 15, residue 10481. -/
theorem bounds_15_10481 : exactInterval 15 10481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10481 : oddCount 10481 15 = 8 ∧ acceleratedOrbit 15 10481 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10481) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10481.1, data_15_10481.2]

/-- Complete interval computation for depth 15, residue 10482. -/
theorem bounds_15_10482 : exactInterval 15 10482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10482 : oddCount 10482 15 = 10 ∧ acceleratedOrbit 15 10482 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10482) = 3 ^ 10 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10482.1, data_15_10482.2]

/-- Complete interval computation for depth 15, residue 10483. -/
theorem bounds_15_10483 : exactInterval 15 10483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10483 : oddCount 10483 15 = 10 ∧ acceleratedOrbit 15 10483 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10483) = 3 ^ 10 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10483.1, data_15_10483.2]

/-- Complete interval computation for depth 15, residue 10484. -/
theorem bounds_15_10484 : exactInterval 15 10484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10484 : oddCount 10484 15 = 8 ∧ acceleratedOrbit 15 10484 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10484) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10484.1, data_15_10484.2]

end Collatz.Research.PassageAtlas.Batch0320
