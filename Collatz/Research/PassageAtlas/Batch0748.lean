import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0748

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24477. -/
theorem bounds_15_24477 : exactInterval 15 24477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24477 : oddCount 24477 15 = 7 ∧ acceleratedOrbit 15 24477 = 1634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24477) = 3 ^ 7 * m + 1634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24477.1, data_15_24477.2]

/-- Complete interval computation for depth 15, residue 24478. -/
theorem bounds_15_24478 : exactInterval 15 24478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24478 : oddCount 24478 15 = 7 ∧ acceleratedOrbit 15 24478 = 1634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24478) = 3 ^ 7 * m + 1634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24478.1, data_15_24478.2]

/-- Complete interval computation for depth 15, residue 24479. -/
theorem bounds_15_24479 : exactInterval 15 24479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24479 : oddCount 24479 15 = 11 ∧ acceleratedOrbit 15 24479 = 132344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24479) = 3 ^ 11 * m + 132344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24479.1, data_15_24479.2]

/-- Complete interval computation for depth 15, residue 24480. -/
theorem bounds_15_24480 : exactInterval 15 24480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24480 : oddCount 24480 15 = 7 ∧ acceleratedOrbit 15 24480 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24480) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24480.1, data_15_24480.2]

/-- Complete interval computation for depth 15, residue 24481. -/
theorem bounds_15_24481 : exactInterval 15 24481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24481 : oddCount 24481 15 = 8 ∧ acceleratedOrbit 15 24481 = 4904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24481) = 3 ^ 8 * m + 4904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24481.1, data_15_24481.2]

/-- Complete interval computation for depth 15, residue 24482. -/
theorem bounds_15_24482 : exactInterval 15 24482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24482 : oddCount 24482 15 = 6 ∧ acceleratedOrbit 15 24482 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24482) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24482.1, data_15_24482.2]

/-- Complete interval computation for depth 15, residue 24483. -/
theorem bounds_15_24483 : exactInterval 15 24483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24483 : oddCount 24483 15 = 6 ∧ acceleratedOrbit 15 24483 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24483) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24483.1, data_15_24483.2]

/-- Complete interval computation for depth 15, residue 24484. -/
theorem bounds_15_24484 : exactInterval 15 24484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24484 : oddCount 24484 15 = 10 ∧ acceleratedOrbit 15 24484 = 44135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24484) = 3 ^ 10 * m + 44135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24484.1, data_15_24484.2]

/-- Complete interval computation for depth 15, residue 24485. -/
theorem bounds_15_24485 : exactInterval 15 24485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24485 : oddCount 24485 15 = 10 ∧ acceleratedOrbit 15 24485 = 44135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24485) = 3 ^ 10 * m + 44135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24485.1, data_15_24485.2]

/-- Complete interval computation for depth 15, residue 24486. -/
theorem bounds_15_24486 : exactInterval 15 24486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24486 : oddCount 24486 15 = 10 ∧ acceleratedOrbit 15 24486 = 44135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24486) = 3 ^ 10 * m + 44135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24486.1, data_15_24486.2]

/-- Complete interval computation for depth 15, residue 24487. -/
theorem bounds_15_24487 : exactInterval 15 24487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24487 : oddCount 24487 15 = 9 ∧ acceleratedOrbit 15 24487 = 14710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24487) = 3 ^ 9 * m + 14710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24487.1, data_15_24487.2]

/-- Complete interval computation for depth 15, residue 24488. -/
theorem bounds_15_24488 : exactInterval 15 24488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24488 : oddCount 24488 15 = 7 ∧ acceleratedOrbit 15 24488 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24488) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24488.1, data_15_24488.2]

/-- Complete interval computation for depth 15, residue 24489. -/
theorem bounds_15_24489 : exactInterval 15 24489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24489 : oddCount 24489 15 = 9 ∧ acceleratedOrbit 15 24489 = 14711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24489) = 3 ^ 9 * m + 14711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24489.1, data_15_24489.2]

/-- Complete interval computation for depth 15, residue 24490. -/
theorem bounds_15_24490 : exactInterval 15 24490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24490 : oddCount 24490 15 = 7 ∧ acceleratedOrbit 15 24490 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24490) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24490.1, data_15_24490.2]

/-- Complete interval computation for depth 15, residue 24491. -/
theorem bounds_15_24491 : exactInterval 15 24491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24491 : oddCount 24491 15 = 9 ∧ acceleratedOrbit 15 24491 = 14714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24491) = 3 ^ 9 * m + 14714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24491.1, data_15_24491.2]

/-- Complete interval computation for depth 15, residue 24492. -/
theorem bounds_15_24492 : exactInterval 15 24492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24492 : oddCount 24492 15 = 9 ∧ acceleratedOrbit 15 24492 = 14717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24492) = 3 ^ 9 * m + 14717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24492.1, data_15_24492.2]

/-- Complete interval computation for depth 15, residue 24493. -/
theorem bounds_15_24493 : exactInterval 15 24493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24493 : oddCount 24493 15 = 9 ∧ acceleratedOrbit 15 24493 = 14717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24493) = 3 ^ 9 * m + 14717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24493.1, data_15_24493.2]

/-- Complete interval computation for depth 15, residue 24494. -/
theorem bounds_15_24494 : exactInterval 15 24494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24494 : oddCount 24494 15 = 9 ∧ acceleratedOrbit 15 24494 = 14717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24494) = 3 ^ 9 * m + 14717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24494.1, data_15_24494.2]

/-- Complete interval computation for depth 15, residue 24495. -/
theorem bounds_15_24495 : exactInterval 15 24495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24495 : oddCount 24495 15 = 6 ∧ acceleratedOrbit 15 24495 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24495) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24495.1, data_15_24495.2]

/-- Complete interval computation for depth 15, residue 24496. -/
theorem bounds_15_24496 : exactInterval 15 24496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24496 : oddCount 24496 15 = 7 ∧ acceleratedOrbit 15 24496 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24496) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24496.1, data_15_24496.2]

/-- Complete interval computation for depth 15, residue 24497. -/
theorem bounds_15_24497 : exactInterval 15 24497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24497 : oddCount 24497 15 = 5 ∧ acceleratedOrbit 15 24497 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24497) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24497.1, data_15_24497.2]

/-- Complete interval computation for depth 15, residue 24498. -/
theorem bounds_15_24498 : exactInterval 15 24498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24498 : oddCount 24498 15 = 5 ∧ acceleratedOrbit 15 24498 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24498) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24498.1, data_15_24498.2]

/-- Complete interval computation for depth 15, residue 24499. -/
theorem bounds_15_24499 : exactInterval 15 24499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24499 : oddCount 24499 15 = 5 ∧ acceleratedOrbit 15 24499 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24499) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24499.1, data_15_24499.2]

/-- Complete interval computation for depth 15, residue 24500. -/
theorem bounds_15_24500 : exactInterval 15 24500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24500 : oddCount 24500 15 = 7 ∧ acceleratedOrbit 15 24500 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24500) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24500.1, data_15_24500.2]

/-- Complete interval computation for depth 15, residue 24501. -/
theorem bounds_15_24501 : exactInterval 15 24501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24501 : oddCount 24501 15 = 7 ∧ acceleratedOrbit 15 24501 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24501) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24501.1, data_15_24501.2]

/-- Complete interval computation for depth 15, residue 24502. -/
theorem bounds_15_24502 : exactInterval 15 24502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24502 : oddCount 24502 15 = 8 ∧ acceleratedOrbit 15 24502 = 4907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24502) = 3 ^ 8 * m + 4907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24502.1, data_15_24502.2]

/-- Complete interval computation for depth 15, residue 24503. -/
theorem bounds_15_24503 : exactInterval 15 24503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24503 : oddCount 24503 15 = 8 ∧ acceleratedOrbit 15 24503 = 4907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24503) = 3 ^ 8 * m + 4907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24503.1, data_15_24503.2]

/-- Complete interval computation for depth 15, residue 24504. -/
theorem bounds_15_24504 : exactInterval 15 24504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24504 : oddCount 24504 15 = 7 ∧ acceleratedOrbit 15 24504 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24504) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24504.1, data_15_24504.2]

/-- Complete interval computation for depth 15, residue 24505. -/
theorem bounds_15_24505 : exactInterval 15 24505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24505 : oddCount 24505 15 = 7 ∧ acceleratedOrbit 15 24505 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24505) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24505.1, data_15_24505.2]

/-- Complete interval computation for depth 15, residue 24506. -/
theorem bounds_15_24506 : exactInterval 15 24506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24506 : oddCount 24506 15 = 7 ∧ acceleratedOrbit 15 24506 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24506) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24506.1, data_15_24506.2]

/-- Complete interval computation for depth 15, residue 24507. -/
theorem bounds_15_24507 : exactInterval 15 24507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24507 : oddCount 24507 15 = 7 ∧ acceleratedOrbit 15 24507 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24507) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24507.1, data_15_24507.2]

/-- Complete interval computation for depth 15, residue 24508. -/
theorem bounds_15_24508 : exactInterval 15 24508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24508 : oddCount 24508 15 = 7 ∧ acceleratedOrbit 15 24508 = 1636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24508) = 3 ^ 7 * m + 1636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24508.1, data_15_24508.2]

/-- Complete interval computation for depth 15, residue 24509. -/
theorem bounds_15_24509 : exactInterval 15 24509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24509 : oddCount 24509 15 = 7 ∧ acceleratedOrbit 15 24509 = 1636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24509) = 3 ^ 7 * m + 1636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24509.1, data_15_24509.2]

end Collatz.Research.PassageAtlas.Batch0748
