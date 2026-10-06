import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0351

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11468. -/
theorem bounds_15_11468 : exactInterval 15 11468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11468 : oddCount 11468 15 = 6 ∧ acceleratedOrbit 15 11468 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11468) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11468.1, data_15_11468.2]

/-- Complete interval computation for depth 15, residue 11469. -/
theorem bounds_15_11469 : exactInterval 15 11469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11469 : oddCount 11469 15 = 6 ∧ acceleratedOrbit 15 11469 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11469) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11469.1, data_15_11469.2]

/-- Complete interval computation for depth 15, residue 11470. -/
theorem bounds_15_11470 : exactInterval 15 11470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11470 : oddCount 11470 15 = 10 ∧ acceleratedOrbit 15 11470 = 20675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11470) = 3 ^ 10 * m + 20675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11470.1, data_15_11470.2]

/-- Complete interval computation for depth 15, residue 11471. -/
theorem bounds_15_11471 : exactInterval 15 11471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11471 : oddCount 11471 15 = 10 ∧ acceleratedOrbit 15 11471 = 20675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11471) = 3 ^ 10 * m + 20675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11471.1, data_15_11471.2]

/-- Complete interval computation for depth 15, residue 11472. -/
theorem bounds_15_11472 : exactInterval 15 11472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11472 : oddCount 11472 15 = 4 ∧ acceleratedOrbit 15 11472 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11472) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11472.1, data_15_11472.2]

/-- Complete interval computation for depth 15, residue 11473. -/
theorem bounds_15_11473 : exactInterval 15 11473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11473 : oddCount 11473 15 = 9 ∧ acceleratedOrbit 15 11473 = 6895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11473) = 3 ^ 9 * m + 6895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11473.1, data_15_11473.2]

/-- Complete interval computation for depth 15, residue 11474. -/
theorem bounds_15_11474 : exactInterval 15 11474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11474 : oddCount 11474 15 = 9 ∧ acceleratedOrbit 15 11474 = 6895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11474) = 3 ^ 9 * m + 6895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11474.1, data_15_11474.2]

/-- Complete interval computation for depth 15, residue 11475. -/
theorem bounds_15_11475 : exactInterval 15 11475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11475 : oddCount 11475 15 = 9 ∧ acceleratedOrbit 15 11475 = 6895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11475) = 3 ^ 9 * m + 6895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11475.1, data_15_11475.2]

/-- Complete interval computation for depth 15, residue 11476. -/
theorem bounds_15_11476 : exactInterval 15 11476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11476 : oddCount 11476 15 = 4 ∧ acceleratedOrbit 15 11476 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11476) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11476.1, data_15_11476.2]

/-- Complete interval computation for depth 15, residue 11477. -/
theorem bounds_15_11477 : exactInterval 15 11477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11477 : oddCount 11477 15 = 4 ∧ acceleratedOrbit 15 11477 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11477) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11477.1, data_15_11477.2]

/-- Complete interval computation for depth 15, residue 11478. -/
theorem bounds_15_11478 : exactInterval 15 11478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11478 : oddCount 11478 15 = 9 ∧ acceleratedOrbit 15 11478 = 6898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11478) = 3 ^ 9 * m + 6898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11478.1, data_15_11478.2]

/-- Complete interval computation for depth 15, residue 11479. -/
theorem bounds_15_11479 : exactInterval 15 11479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11479 : oddCount 11479 15 = 9 ∧ acceleratedOrbit 15 11479 = 6898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11479) = 3 ^ 9 * m + 6898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11479.1, data_15_11479.2]

/-- Complete interval computation for depth 15, residue 11480. -/
theorem bounds_15_11480 : exactInterval 15 11480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11480 : oddCount 11480 15 = 7 ∧ acceleratedOrbit 15 11480 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11480) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11480.1, data_15_11480.2]

/-- Complete interval computation for depth 15, residue 11481. -/
theorem bounds_15_11481 : exactInterval 15 11481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11481 : oddCount 11481 15 = 7 ∧ acceleratedOrbit 15 11481 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11481) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11481.1, data_15_11481.2]

/-- Complete interval computation for depth 15, residue 11482. -/
theorem bounds_15_11482 : exactInterval 15 11482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11482 : oddCount 11482 15 = 7 ∧ acceleratedOrbit 15 11482 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11482) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11482.1, data_15_11482.2]

/-- Complete interval computation for depth 15, residue 11483. -/
theorem bounds_15_11483 : exactInterval 15 11483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11483 : oddCount 11483 15 = 7 ∧ acceleratedOrbit 15 11483 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11483) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11483.1, data_15_11483.2]

/-- Complete interval computation for depth 15, residue 11484. -/
theorem bounds_15_11484 : exactInterval 15 11484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11484 : oddCount 11484 15 = 7 ∧ acceleratedOrbit 15 11484 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11484) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11484.1, data_15_11484.2]

/-- Complete interval computation for depth 15, residue 11485. -/
theorem bounds_15_11485 : exactInterval 15 11485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11485 : oddCount 11485 15 = 7 ∧ acceleratedOrbit 15 11485 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11485) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11485.1, data_15_11485.2]

/-- Complete interval computation for depth 15, residue 11486. -/
theorem bounds_15_11486 : exactInterval 15 11486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11486 : oddCount 11486 15 = 9 ∧ acceleratedOrbit 15 11486 = 6902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11486) = 3 ^ 9 * m + 6902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11486.1, data_15_11486.2]

/-- Complete interval computation for depth 15, residue 11487. -/
theorem bounds_15_11487 : exactInterval 15 11487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11487 : oddCount 11487 15 = 9 ∧ acceleratedOrbit 15 11487 = 6902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11487) = 3 ^ 9 * m + 6902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11487.1, data_15_11487.2]

/-- Complete interval computation for depth 15, residue 11488. -/
theorem bounds_15_11488 : exactInterval 15 11488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11488 : oddCount 11488 15 = 8 ∧ acceleratedOrbit 15 11488 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11488) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11488.1, data_15_11488.2]

/-- Complete interval computation for depth 15, residue 11489. -/
theorem bounds_15_11489 : exactInterval 15 11489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11489 : oddCount 11489 15 = 11 ∧ acceleratedOrbit 15 11489 = 62126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11489) = 3 ^ 11 * m + 62126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11489.1, data_15_11489.2]

/-- Complete interval computation for depth 15, residue 11490. -/
theorem bounds_15_11490 : exactInterval 15 11490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11490 : oddCount 11490 15 = 4 ∧ acceleratedOrbit 15 11490 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11490) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11490.1, data_15_11490.2]

/-- Complete interval computation for depth 15, residue 11491. -/
theorem bounds_15_11491 : exactInterval 15 11491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11491 : oddCount 11491 15 = 4 ∧ acceleratedOrbit 15 11491 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11491) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11491.1, data_15_11491.2]

/-- Complete interval computation for depth 15, residue 11492. -/
theorem bounds_15_11492 : exactInterval 15 11492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11492 : oddCount 11492 15 = 9 ∧ acceleratedOrbit 15 11492 = 6911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11492) = 3 ^ 9 * m + 6911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11492.1, data_15_11492.2]

/-- Complete interval computation for depth 15, residue 11493. -/
theorem bounds_15_11493 : exactInterval 15 11493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11493 : oddCount 11493 15 = 9 ∧ acceleratedOrbit 15 11493 = 6911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11493) = 3 ^ 9 * m + 6911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11493.1, data_15_11493.2]

/-- Complete interval computation for depth 15, residue 11494. -/
theorem bounds_15_11494 : exactInterval 15 11494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11494 : oddCount 11494 15 = 9 ∧ acceleratedOrbit 15 11494 = 6911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11494) = 3 ^ 9 * m + 6911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11494.1, data_15_11494.2]

/-- Complete interval computation for depth 15, residue 11495. -/
theorem bounds_15_11495 : exactInterval 15 11495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11495 : oddCount 11495 15 = 11 ∧ acceleratedOrbit 15 11495 = 62153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11495) = 3 ^ 11 * m + 62153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11495.1, data_15_11495.2]

/-- Complete interval computation for depth 15, residue 11496. -/
theorem bounds_15_11496 : exactInterval 15 11496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11496 : oddCount 11496 15 = 8 ∧ acceleratedOrbit 15 11496 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11496) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11496.1, data_15_11496.2]

/-- Complete interval computation for depth 15, residue 11497. -/
theorem bounds_15_11497 : exactInterval 15 11497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11497 : oddCount 11497 15 = 8 ∧ acceleratedOrbit 15 11497 = 2303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11497) = 3 ^ 8 * m + 2303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11497.1, data_15_11497.2]

/-- Complete interval computation for depth 15, residue 11498. -/
theorem bounds_15_11498 : exactInterval 15 11498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11498 : oddCount 11498 15 = 8 ∧ acceleratedOrbit 15 11498 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11498) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11498.1, data_15_11498.2]

/-- Complete interval computation for depth 15, residue 11499. -/
theorem bounds_15_11499 : exactInterval 15 11499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11499 : oddCount 11499 15 = 10 ∧ acceleratedOrbit 15 11499 = 20726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11499) = 3 ^ 10 * m + 20726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11499.1, data_15_11499.2]

/-- Complete interval computation for depth 15, residue 11500. -/
theorem bounds_15_11500 : exactInterval 15 11500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11500 : oddCount 11500 15 = 7 ∧ acceleratedOrbit 15 11500 = 769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11500) = 3 ^ 7 * m + 769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11500.1, data_15_11500.2]

end Collatz.Research.PassageAtlas.Batch0351
