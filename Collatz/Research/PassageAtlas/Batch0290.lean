import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0290

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9469. -/
theorem bounds_15_9469 : exactInterval 15 9469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9469 : oddCount 9469 15 = 9 ∧ acceleratedOrbit 15 9469 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9469) = 3 ^ 9 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9469.1, data_15_9469.2]

/-- Complete interval computation for depth 15, residue 9470. -/
theorem bounds_15_9470 : exactInterval 15 9470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9470 : oddCount 9470 15 = 10 ∧ acceleratedOrbit 15 9470 = 17069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9470) = 3 ^ 10 * m + 17069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9470.1, data_15_9470.2]

/-- Complete interval computation for depth 15, residue 9471. -/
theorem bounds_15_9471 : exactInterval 15 9471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9471 : oddCount 9471 15 = 10 ∧ acceleratedOrbit 15 9471 = 17069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9471) = 3 ^ 10 * m + 17069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9471.1, data_15_9471.2]

/-- Complete interval computation for depth 15, residue 9472. -/
theorem bounds_15_9472 : exactInterval 15 9472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9472 : oddCount 9472 15 = 4 ∧ acceleratedOrbit 15 9472 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9472) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9472.1, data_15_9472.2]

/-- Complete interval computation for depth 15, residue 9473. -/
theorem bounds_15_9473 : exactInterval 15 9473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9473 : oddCount 9473 15 = 9 ∧ acceleratedOrbit 15 9473 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9473) = 3 ^ 9 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9473.1, data_15_9473.2]

/-- Complete interval computation for depth 15, residue 9474. -/
theorem bounds_15_9474 : exactInterval 15 9474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9474 : oddCount 9474 15 = 9 ∧ acceleratedOrbit 15 9474 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9474) = 3 ^ 9 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9474.1, data_15_9474.2]

/-- Complete interval computation for depth 15, residue 9475. -/
theorem bounds_15_9475 : exactInterval 15 9475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9475 : oddCount 9475 15 = 9 ∧ acceleratedOrbit 15 9475 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9475) = 3 ^ 9 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9475.1, data_15_9475.2]

/-- Complete interval computation for depth 15, residue 9476. -/
theorem bounds_15_9476 : exactInterval 15 9476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9476 : oddCount 9476 15 = 5 ∧ acceleratedOrbit 15 9476 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9476) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9476.1, data_15_9476.2]

/-- Complete interval computation for depth 15, residue 9477. -/
theorem bounds_15_9477 : exactInterval 15 9477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9477 : oddCount 9477 15 = 5 ∧ acceleratedOrbit 15 9477 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9477) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9477.1, data_15_9477.2]

/-- Complete interval computation for depth 15, residue 9478. -/
theorem bounds_15_9478 : exactInterval 15 9478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9478 : oddCount 9478 15 = 5 ∧ acceleratedOrbit 15 9478 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9478) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9478.1, data_15_9478.2]

/-- Complete interval computation for depth 15, residue 9479. -/
theorem bounds_15_9479 : exactInterval 15 9479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9479 : oddCount 9479 15 = 10 ∧ acceleratedOrbit 15 9479 = 17086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9479) = 3 ^ 10 * m + 17086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9479.1, data_15_9479.2]

/-- Complete interval computation for depth 15, residue 9480. -/
theorem bounds_15_9480 : exactInterval 15 9480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9480 : oddCount 9480 15 = 8 ∧ acceleratedOrbit 15 9480 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9480) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9480.1, data_15_9480.2]

/-- Complete interval computation for depth 15, residue 9481. -/
theorem bounds_15_9481 : exactInterval 15 9481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9481 : oddCount 9481 15 = 11 ∧ acceleratedOrbit 15 9481 = 51272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9481) = 3 ^ 11 * m + 51272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9481.1, data_15_9481.2]

/-- Complete interval computation for depth 15, residue 9482. -/
theorem bounds_15_9482 : exactInterval 15 9482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9482 : oddCount 9482 15 = 8 ∧ acceleratedOrbit 15 9482 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9482) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9482.1, data_15_9482.2]

/-- Complete interval computation for depth 15, residue 9483. -/
theorem bounds_15_9483 : exactInterval 15 9483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9483 : oddCount 9483 15 = 8 ∧ acceleratedOrbit 15 9483 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9483) = 3 ^ 8 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9483.1, data_15_9483.2]

/-- Complete interval computation for depth 15, residue 9484. -/
theorem bounds_15_9484 : exactInterval 15 9484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9484 : oddCount 9484 15 = 8 ∧ acceleratedOrbit 15 9484 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9484) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9484.1, data_15_9484.2]

/-- Complete interval computation for depth 15, residue 9485. -/
theorem bounds_15_9485 : exactInterval 15 9485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9485 : oddCount 9485 15 = 8 ∧ acceleratedOrbit 15 9485 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9485) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9485.1, data_15_9485.2]

/-- Complete interval computation for depth 15, residue 9486. -/
theorem bounds_15_9486 : exactInterval 15 9486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9486 : oddCount 9486 15 = 7 ∧ acceleratedOrbit 15 9486 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9486) = 3 ^ 7 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9486.1, data_15_9486.2]

/-- Complete interval computation for depth 15, residue 9487. -/
theorem bounds_15_9487 : exactInterval 15 9487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9487 : oddCount 9487 15 = 7 ∧ acceleratedOrbit 15 9487 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9487) = 3 ^ 7 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9487.1, data_15_9487.2]

/-- Complete interval computation for depth 15, residue 9488. -/
theorem bounds_15_9488 : exactInterval 15 9488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9488 : oddCount 9488 15 = 7 ∧ acceleratedOrbit 15 9488 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9488) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9488.1, data_15_9488.2]

/-- Complete interval computation for depth 15, residue 9489. -/
theorem bounds_15_9489 : exactInterval 15 9489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9489 : oddCount 9489 15 = 8 ∧ acceleratedOrbit 15 9489 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9489) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9489.1, data_15_9489.2]

/-- Complete interval computation for depth 15, residue 9490. -/
theorem bounds_15_9490 : exactInterval 15 9490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9490 : oddCount 9490 15 = 8 ∧ acceleratedOrbit 15 9490 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9490) = 3 ^ 8 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9490.1, data_15_9490.2]

/-- Complete interval computation for depth 15, residue 9491. -/
theorem bounds_15_9491 : exactInterval 15 9491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9491 : oddCount 9491 15 = 8 ∧ acceleratedOrbit 15 9491 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9491) = 3 ^ 8 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9491.1, data_15_9491.2]

/-- Complete interval computation for depth 15, residue 9492. -/
theorem bounds_15_9492 : exactInterval 15 9492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9492 : oddCount 9492 15 = 7 ∧ acceleratedOrbit 15 9492 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9492) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9492.1, data_15_9492.2]

/-- Complete interval computation for depth 15, residue 9493. -/
theorem bounds_15_9493 : exactInterval 15 9493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9493 : oddCount 9493 15 = 7 ∧ acceleratedOrbit 15 9493 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9493) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9493.1, data_15_9493.2]

/-- Complete interval computation for depth 15, residue 9494. -/
theorem bounds_15_9494 : exactInterval 15 9494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9494 : oddCount 9494 15 = 8 ∧ acceleratedOrbit 15 9494 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9494) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9494.1, data_15_9494.2]

/-- Complete interval computation for depth 15, residue 9495. -/
theorem bounds_15_9495 : exactInterval 15 9495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9495 : oddCount 9495 15 = 8 ∧ acceleratedOrbit 15 9495 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9495) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9495.1, data_15_9495.2]

/-- Complete interval computation for depth 15, residue 9496. -/
theorem bounds_15_9496 : exactInterval 15 9496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9496 : oddCount 9496 15 = 7 ∧ acceleratedOrbit 15 9496 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9496) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9496.1, data_15_9496.2]

/-- Complete interval computation for depth 15, residue 9497. -/
theorem bounds_15_9497 : exactInterval 15 9497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9497 : oddCount 9497 15 = 9 ∧ acceleratedOrbit 15 9497 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9497) = 3 ^ 9 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9497.1, data_15_9497.2]

/-- Complete interval computation for depth 15, residue 9498. -/
theorem bounds_15_9498 : exactInterval 15 9498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9498 : oddCount 9498 15 = 7 ∧ acceleratedOrbit 15 9498 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9498) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9498.1, data_15_9498.2]

/-- Complete interval computation for depth 15, residue 9499. -/
theorem bounds_15_9499 : exactInterval 15 9499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9499 : oddCount 9499 15 = 12 ∧ acceleratedOrbit 15 9499 = 154082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9499) = 3 ^ 12 * m + 154082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9499.1, data_15_9499.2]

/-- Complete interval computation for depth 15, residue 9500. -/
theorem bounds_15_9500 : exactInterval 15 9500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9500 : oddCount 9500 15 = 10 ∧ acceleratedOrbit 15 9500 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9500) = 3 ^ 10 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9500.1, data_15_9500.2]

/-- Complete interval computation for depth 15, residue 9501. -/
theorem bounds_15_9501 : exactInterval 15 9501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9501 : oddCount 9501 15 = 10 ∧ acceleratedOrbit 15 9501 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9501) = 3 ^ 10 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9501.1, data_15_9501.2]

end Collatz.Research.PassageAtlas.Batch0290
