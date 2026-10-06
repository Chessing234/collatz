import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0534

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17465. -/
theorem bounds_15_17465 : exactInterval 15 17465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17465 : oddCount 17465 15 = 7 ∧ acceleratedOrbit 15 17465 = 1166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17465) = 3 ^ 7 * m + 1166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17465.1, data_15_17465.2]

/-- Complete interval computation for depth 15, residue 17466. -/
theorem bounds_15_17466 : exactInterval 15 17466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17466 : oddCount 17466 15 = 6 ∧ acceleratedOrbit 15 17466 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17466) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17466.1, data_15_17466.2]

/-- Complete interval computation for depth 15, residue 17467. -/
theorem bounds_15_17467 : exactInterval 15 17467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17467 : oddCount 17467 15 = 7 ∧ acceleratedOrbit 15 17467 = 1166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17467) = 3 ^ 7 * m + 1166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17467.1, data_15_17467.2]

/-- Complete interval computation for depth 15, residue 17468. -/
theorem bounds_15_17468 : exactInterval 15 17468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17468 : oddCount 17468 15 = 6 ∧ acceleratedOrbit 15 17468 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17468) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17468.1, data_15_17468.2]

/-- Complete interval computation for depth 15, residue 17469. -/
theorem bounds_15_17469 : exactInterval 15 17469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17469 : oddCount 17469 15 = 6 ∧ acceleratedOrbit 15 17469 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17469) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17469.1, data_15_17469.2]

/-- Complete interval computation for depth 15, residue 17470. -/
theorem bounds_15_17470 : exactInterval 15 17470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17470 : oddCount 17470 15 = 9 ∧ acceleratedOrbit 15 17470 = 10496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17470) = 3 ^ 9 * m + 10496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17470.1, data_15_17470.2]

/-- Complete interval computation for depth 15, residue 17471. -/
theorem bounds_15_17471 : exactInterval 15 17471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17471 : oddCount 17471 15 = 9 ∧ acceleratedOrbit 15 17471 = 10496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17471) = 3 ^ 9 * m + 10496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17471.1, data_15_17471.2]

/-- Complete interval computation for depth 15, residue 17472. -/
theorem bounds_15_17472 : exactInterval 15 17472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17472 : oddCount 17472 15 = 4 ∧ acceleratedOrbit 15 17472 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17472) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17472.1, data_15_17472.2]

/-- Complete interval computation for depth 15, residue 17473. -/
theorem bounds_15_17473 : exactInterval 15 17473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17473 : oddCount 17473 15 = 6 ∧ acceleratedOrbit 15 17473 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17473) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17473.1, data_15_17473.2]

/-- Complete interval computation for depth 15, residue 17474. -/
theorem bounds_15_17474 : exactInterval 15 17474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17474 : oddCount 17474 15 = 6 ∧ acceleratedOrbit 15 17474 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17474) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17474.1, data_15_17474.2]

/-- Complete interval computation for depth 15, residue 17475. -/
theorem bounds_15_17475 : exactInterval 15 17475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17475 : oddCount 17475 15 = 6 ∧ acceleratedOrbit 15 17475 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17475) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17475.1, data_15_17475.2]

/-- Complete interval computation for depth 15, residue 17476. -/
theorem bounds_15_17476 : exactInterval 15 17476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17476 : oddCount 17476 15 = 5 ∧ acceleratedOrbit 15 17476 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17476) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17476.1, data_15_17476.2]

/-- Complete interval computation for depth 15, residue 17477. -/
theorem bounds_15_17477 : exactInterval 15 17477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17477 : oddCount 17477 15 = 5 ∧ acceleratedOrbit 15 17477 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17477) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17477.1, data_15_17477.2]

/-- Complete interval computation for depth 15, residue 17478. -/
theorem bounds_15_17478 : exactInterval 15 17478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17478 : oddCount 17478 15 = 5 ∧ acceleratedOrbit 15 17478 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17478) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17478.1, data_15_17478.2]

/-- Complete interval computation for depth 15, residue 17479. -/
theorem bounds_15_17479 : exactInterval 15 17479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17479 : oddCount 17479 15 = 10 ∧ acceleratedOrbit 15 17479 = 31502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17479) = 3 ^ 10 * m + 31502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17479.1, data_15_17479.2]

/-- Complete interval computation for depth 15, residue 17480. -/
theorem bounds_15_17480 : exactInterval 15 17480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17480 : oddCount 17480 15 = 8 ∧ acceleratedOrbit 15 17480 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17480) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17480.1, data_15_17480.2]

/-- Complete interval computation for depth 15, residue 17481. -/
theorem bounds_15_17481 : exactInterval 15 17481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17481 : oddCount 17481 15 = 10 ∧ acceleratedOrbit 15 17481 = 31508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17481) = 3 ^ 10 * m + 31508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17481.1, data_15_17481.2]

/-- Complete interval computation for depth 15, residue 17482. -/
theorem bounds_15_17482 : exactInterval 15 17482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17482 : oddCount 17482 15 = 8 ∧ acceleratedOrbit 15 17482 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17482) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17482.1, data_15_17482.2]

/-- Complete interval computation for depth 15, residue 17483. -/
theorem bounds_15_17483 : exactInterval 15 17483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17483 : oddCount 17483 15 = 5 ∧ acceleratedOrbit 15 17483 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17483) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17483.1, data_15_17483.2]

/-- Complete interval computation for depth 15, residue 17484. -/
theorem bounds_15_17484 : exactInterval 15 17484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17484 : oddCount 17484 15 = 8 ∧ acceleratedOrbit 15 17484 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17484) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17484.1, data_15_17484.2]

/-- Complete interval computation for depth 15, residue 17485. -/
theorem bounds_15_17485 : exactInterval 15 17485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17485 : oddCount 17485 15 = 8 ∧ acceleratedOrbit 15 17485 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17485) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17485.1, data_15_17485.2]

/-- Complete interval computation for depth 15, residue 17486. -/
theorem bounds_15_17486 : exactInterval 15 17486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17486 : oddCount 17486 15 = 8 ∧ acceleratedOrbit 15 17486 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17486) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17486.1, data_15_17486.2]

/-- Complete interval computation for depth 15, residue 17487. -/
theorem bounds_15_17487 : exactInterval 15 17487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17487 : oddCount 17487 15 = 8 ∧ acceleratedOrbit 15 17487 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17487) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17487.1, data_15_17487.2]

/-- Complete interval computation for depth 15, residue 17488. -/
theorem bounds_15_17488 : exactInterval 15 17488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17488 : oddCount 17488 15 = 4 ∧ acceleratedOrbit 15 17488 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17488) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17488.1, data_15_17488.2]

/-- Complete interval computation for depth 15, residue 17489. -/
theorem bounds_15_17489 : exactInterval 15 17489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17489 : oddCount 17489 15 = 8 ∧ acceleratedOrbit 15 17489 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17489) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17489.1, data_15_17489.2]

/-- Complete interval computation for depth 15, residue 17490. -/
theorem bounds_15_17490 : exactInterval 15 17490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17490 : oddCount 17490 15 = 9 ∧ acceleratedOrbit 15 17490 = 10508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17490) = 3 ^ 9 * m + 10508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17490.1, data_15_17490.2]

/-- Complete interval computation for depth 15, residue 17491. -/
theorem bounds_15_17491 : exactInterval 15 17491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17491 : oddCount 17491 15 = 9 ∧ acceleratedOrbit 15 17491 = 10508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17491) = 3 ^ 9 * m + 10508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17491.1, data_15_17491.2]

/-- Complete interval computation for depth 15, residue 17492. -/
theorem bounds_15_17492 : exactInterval 15 17492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17492 : oddCount 17492 15 = 4 ∧ acceleratedOrbit 15 17492 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17492) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17492.1, data_15_17492.2]

/-- Complete interval computation for depth 15, residue 17493. -/
theorem bounds_15_17493 : exactInterval 15 17493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17493 : oddCount 17493 15 = 4 ∧ acceleratedOrbit 15 17493 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17493) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17493.1, data_15_17493.2]

/-- Complete interval computation for depth 15, residue 17494. -/
theorem bounds_15_17494 : exactInterval 15 17494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17494 : oddCount 17494 15 = 5 ∧ acceleratedOrbit 15 17494 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17494) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17494.1, data_15_17494.2]

/-- Complete interval computation for depth 15, residue 17495. -/
theorem bounds_15_17495 : exactInterval 15 17495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17495 : oddCount 17495 15 = 5 ∧ acceleratedOrbit 15 17495 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17495) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17495.1, data_15_17495.2]

/-- Complete interval computation for depth 15, residue 17496. -/
theorem bounds_15_17496 : exactInterval 15 17496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17496 : oddCount 17496 15 = 8 ∧ acceleratedOrbit 15 17496 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17496) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17496.1, data_15_17496.2]

/-- Complete interval computation for depth 15, residue 17497. -/
theorem bounds_15_17497 : exactInterval 15 17497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17497 : oddCount 17497 15 = 8 ∧ acceleratedOrbit 15 17497 = 3505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17497) = 3 ^ 8 * m + 3505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17497.1, data_15_17497.2]

end Collatz.Research.PassageAtlas.Batch0534
