import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0992

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32473. -/
theorem bounds_15_32473 : exactInterval 15 32473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32473 : oddCount 32473 15 = 8 ∧ acceleratedOrbit 15 32473 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32473) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32473.1, data_15_32473.2]

/-- Complete interval computation for depth 15, residue 32474. -/
theorem bounds_15_32474 : exactInterval 15 32474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32474 : oddCount 32474 15 = 8 ∧ acceleratedOrbit 15 32474 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32474) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32474.1, data_15_32474.2]

/-- Complete interval computation for depth 15, residue 32475. -/
theorem bounds_15_32475 : exactInterval 15 32475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32475 : oddCount 32475 15 = 10 ∧ acceleratedOrbit 15 32475 = 58526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32475) = 3 ^ 10 * m + 58526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32475.1, data_15_32475.2]

/-- Complete interval computation for depth 15, residue 32476. -/
theorem bounds_15_32476 : exactInterval 15 32476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32476 : oddCount 32476 15 = 8 ∧ acceleratedOrbit 15 32476 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32476) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32476.1, data_15_32476.2]

/-- Complete interval computation for depth 15, residue 32477. -/
theorem bounds_15_32477 : exactInterval 15 32477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32477 : oddCount 32477 15 = 8 ∧ acceleratedOrbit 15 32477 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32477) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32477.1, data_15_32477.2]

/-- Complete interval computation for depth 15, residue 32478. -/
theorem bounds_15_32478 : exactInterval 15 32478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32478 : oddCount 32478 15 = 9 ∧ acceleratedOrbit 15 32478 = 19511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32478) = 3 ^ 9 * m + 19511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32478.1, data_15_32478.2]

/-- Complete interval computation for depth 15, residue 32479. -/
theorem bounds_15_32479 : exactInterval 15 32479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32479 : oddCount 32479 15 = 9 ∧ acceleratedOrbit 15 32479 = 19511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32479) = 3 ^ 9 * m + 19511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32479.1, data_15_32479.2]

/-- Complete interval computation for depth 15, residue 32480. -/
theorem bounds_15_32480 : exactInterval 15 32480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32480 : oddCount 32480 15 = 6 ∧ acceleratedOrbit 15 32480 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32480) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32480.1, data_15_32480.2]

/-- Complete interval computation for depth 15, residue 32481. -/
theorem bounds_15_32481 : exactInterval 15 32481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32481 : oddCount 32481 15 = 7 ∧ acceleratedOrbit 15 32481 = 2168 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32481) = 3 ^ 7 * m + 2168 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32481.1, data_15_32481.2]

/-- Complete interval computation for depth 15, residue 32482. -/
theorem bounds_15_32482 : exactInterval 15 32482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32482 : oddCount 32482 15 = 6 ∧ acceleratedOrbit 15 32482 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32482) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32482.1, data_15_32482.2]

/-- Complete interval computation for depth 15, residue 32483. -/
theorem bounds_15_32483 : exactInterval 15 32483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32483 : oddCount 32483 15 = 6 ∧ acceleratedOrbit 15 32483 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32483) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32483.1, data_15_32483.2]

/-- Complete interval computation for depth 15, residue 32484. -/
theorem bounds_15_32484 : exactInterval 15 32484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32484 : oddCount 32484 15 = 5 ∧ acceleratedOrbit 15 32484 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32484) = 3 ^ 5 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32484.1, data_15_32484.2]

/-- Complete interval computation for depth 15, residue 32485. -/
theorem bounds_15_32485 : exactInterval 15 32485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32485 : oddCount 32485 15 = 5 ∧ acceleratedOrbit 15 32485 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32485) = 3 ^ 5 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32485.1, data_15_32485.2]

/-- Complete interval computation for depth 15, residue 32486. -/
theorem bounds_15_32486 : exactInterval 15 32486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32486 : oddCount 32486 15 = 5 ∧ acceleratedOrbit 15 32486 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32486) = 3 ^ 5 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32486.1, data_15_32486.2]

/-- Complete interval computation for depth 15, residue 32487. -/
theorem bounds_15_32487 : exactInterval 15 32487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32487 : oddCount 32487 15 = 8 ∧ acceleratedOrbit 15 32487 = 6505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32487) = 3 ^ 8 * m + 6505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32487.1, data_15_32487.2]

/-- Complete interval computation for depth 15, residue 32488. -/
theorem bounds_15_32488 : exactInterval 15 32488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32488 : oddCount 32488 15 = 6 ∧ acceleratedOrbit 15 32488 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32488) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32488.1, data_15_32488.2]

/-- Complete interval computation for depth 15, residue 32489. -/
theorem bounds_15_32489 : exactInterval 15 32489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32489 : oddCount 32489 15 = 8 ∧ acceleratedOrbit 15 32489 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32489) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32489.1, data_15_32489.2]

/-- Complete interval computation for depth 15, residue 32490. -/
theorem bounds_15_32490 : exactInterval 15 32490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32490 : oddCount 32490 15 = 6 ∧ acceleratedOrbit 15 32490 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32490) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32490.1, data_15_32490.2]

/-- Complete interval computation for depth 15, residue 32491. -/
theorem bounds_15_32491 : exactInterval 15 32491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32491 : oddCount 32491 15 = 9 ∧ acceleratedOrbit 15 32491 = 19520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32491) = 3 ^ 9 * m + 19520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32491.1, data_15_32491.2]

/-- Complete interval computation for depth 15, residue 32492. -/
theorem bounds_15_32492 : exactInterval 15 32492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32492 : oddCount 32492 15 = 5 ∧ acceleratedOrbit 15 32492 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32492) = 3 ^ 5 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32492.1, data_15_32492.2]

/-- Complete interval computation for depth 15, residue 32493. -/
theorem bounds_15_32493 : exactInterval 15 32493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32493 : oddCount 32493 15 = 5 ∧ acceleratedOrbit 15 32493 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32493) = 3 ^ 5 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32493.1, data_15_32493.2]

/-- Complete interval computation for depth 15, residue 32494. -/
theorem bounds_15_32494 : exactInterval 15 32494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32494 : oddCount 32494 15 = 5 ∧ acceleratedOrbit 15 32494 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32494) = 3 ^ 5 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32494.1, data_15_32494.2]

/-- Complete interval computation for depth 15, residue 32495. -/
theorem bounds_15_32495 : exactInterval 15 32495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32495 : oddCount 32495 15 = 11 ∧ acceleratedOrbit 15 32495 = 175679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32495) = 3 ^ 11 * m + 175679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32495.1, data_15_32495.2]

/-- Complete interval computation for depth 15, residue 32496. -/
theorem bounds_15_32496 : exactInterval 15 32496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32496 : oddCount 32496 15 = 7 ∧ acceleratedOrbit 15 32496 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32496) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32496.1, data_15_32496.2]

/-- Complete interval computation for depth 15, residue 32497. -/
theorem bounds_15_32497 : exactInterval 15 32497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32497 : oddCount 32497 15 = 6 ∧ acceleratedOrbit 15 32497 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32497) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32497.1, data_15_32497.2]

/-- Complete interval computation for depth 15, residue 32498. -/
theorem bounds_15_32498 : exactInterval 15 32498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32498 : oddCount 32498 15 = 8 ∧ acceleratedOrbit 15 32498 = 6508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32498) = 3 ^ 8 * m + 6508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32498.1, data_15_32498.2]

/-- Complete interval computation for depth 15, residue 32499. -/
theorem bounds_15_32499 : exactInterval 15 32499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32499 : oddCount 32499 15 = 8 ∧ acceleratedOrbit 15 32499 = 6508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32499) = 3 ^ 8 * m + 6508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32499.1, data_15_32499.2]

/-- Complete interval computation for depth 15, residue 32500. -/
theorem bounds_15_32500 : exactInterval 15 32500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32500 : oddCount 32500 15 = 7 ∧ acceleratedOrbit 15 32500 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32500) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32500.1, data_15_32500.2]

/-- Complete interval computation for depth 15, residue 32501. -/
theorem bounds_15_32501 : exactInterval 15 32501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32501 : oddCount 32501 15 = 7 ∧ acceleratedOrbit 15 32501 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32501) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32501.1, data_15_32501.2]

/-- Complete interval computation for depth 15, residue 32502. -/
theorem bounds_15_32502 : exactInterval 15 32502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32502 : oddCount 32502 15 = 8 ∧ acceleratedOrbit 15 32502 = 6509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32502) = 3 ^ 8 * m + 6509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32502.1, data_15_32502.2]

/-- Complete interval computation for depth 15, residue 32503. -/
theorem bounds_15_32503 : exactInterval 15 32503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32503 : oddCount 32503 15 = 8 ∧ acceleratedOrbit 15 32503 = 6509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32503) = 3 ^ 8 * m + 6509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32503.1, data_15_32503.2]

/-- Complete interval computation for depth 15, residue 32504. -/
theorem bounds_15_32504 : exactInterval 15 32504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32504 : oddCount 32504 15 = 7 ∧ acceleratedOrbit 15 32504 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32504) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32504.1, data_15_32504.2]

end Collatz.Research.PassageAtlas.Batch0992
