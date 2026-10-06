import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0626

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20480. -/
theorem bounds_15_20480 : exactInterval 15 20480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20480 : oddCount 20480 15 = 1 ∧ acceleratedOrbit 15 20480 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20480) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20480.1, data_15_20480.2]

/-- Complete interval computation for depth 15, residue 20481. -/
theorem bounds_15_20481 : exactInterval 15 20481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20481 : oddCount 20481 15 = 8 ∧ acceleratedOrbit 15 20481 = 4103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20481) = 3 ^ 8 * m + 4103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20481.1, data_15_20481.2]

/-- Complete interval computation for depth 15, residue 20482. -/
theorem bounds_15_20482 : exactInterval 15 20482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20482 : oddCount 20482 15 = 9 ∧ acceleratedOrbit 15 20482 = 12311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20482) = 3 ^ 9 * m + 12311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20482.1, data_15_20482.2]

/-- Complete interval computation for depth 15, residue 20483. -/
theorem bounds_15_20483 : exactInterval 15 20483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20483 : oddCount 20483 15 = 9 ∧ acceleratedOrbit 15 20483 = 12311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20483) = 3 ^ 9 * m + 12311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20483.1, data_15_20483.2]

/-- Complete interval computation for depth 15, residue 20484. -/
theorem bounds_15_20484 : exactInterval 15 20484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20484 : oddCount 20484 15 = 5 ∧ acceleratedOrbit 15 20484 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20484) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20484.1, data_15_20484.2]

/-- Complete interval computation for depth 15, residue 20485. -/
theorem bounds_15_20485 : exactInterval 15 20485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20485 : oddCount 20485 15 = 5 ∧ acceleratedOrbit 15 20485 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20485) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20485.1, data_15_20485.2]

/-- Complete interval computation for depth 15, residue 20486. -/
theorem bounds_15_20486 : exactInterval 15 20486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20486 : oddCount 20486 15 = 5 ∧ acceleratedOrbit 15 20486 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20486) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20486.1, data_15_20486.2]

/-- Complete interval computation for depth 15, residue 20487. -/
theorem bounds_15_20487 : exactInterval 15 20487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20487 : oddCount 20487 15 = 9 ∧ acceleratedOrbit 15 20487 = 12311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20487) = 3 ^ 9 * m + 12311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20487.1, data_15_20487.2]

/-- Complete interval computation for depth 15, residue 20488. -/
theorem bounds_15_20488 : exactInterval 15 20488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20488 : oddCount 20488 15 = 7 ∧ acceleratedOrbit 15 20488 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20488) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20488.1, data_15_20488.2]

/-- Complete interval computation for depth 15, residue 20489. -/
theorem bounds_15_20489 : exactInterval 15 20489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20489 : oddCount 20489 15 = 9 ∧ acceleratedOrbit 15 20489 = 12311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20489) = 3 ^ 9 * m + 12311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20489.1, data_15_20489.2]

/-- Complete interval computation for depth 15, residue 20490. -/
theorem bounds_15_20490 : exactInterval 15 20490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20490 : oddCount 20490 15 = 7 ∧ acceleratedOrbit 15 20490 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20490) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20490.1, data_15_20490.2]

/-- Complete interval computation for depth 15, residue 20491. -/
theorem bounds_15_20491 : exactInterval 15 20491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20491 : oddCount 20491 15 = 5 ∧ acceleratedOrbit 15 20491 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20491) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20491.1, data_15_20491.2]

/-- Complete interval computation for depth 15, residue 20492. -/
theorem bounds_15_20492 : exactInterval 15 20492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20492 : oddCount 20492 15 = 7 ∧ acceleratedOrbit 15 20492 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20492) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20492.1, data_15_20492.2]

/-- Complete interval computation for depth 15, residue 20493. -/
theorem bounds_15_20493 : exactInterval 15 20493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20493 : oddCount 20493 15 = 7 ∧ acceleratedOrbit 15 20493 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20493) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20493.1, data_15_20493.2]

/-- Complete interval computation for depth 15, residue 20494. -/
theorem bounds_15_20494 : exactInterval 15 20494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20494 : oddCount 20494 15 = 5 ∧ acceleratedOrbit 15 20494 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20494) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20494.1, data_15_20494.2]

/-- Complete interval computation for depth 15, residue 20495. -/
theorem bounds_15_20495 : exactInterval 15 20495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20495 : oddCount 20495 15 = 5 ∧ acceleratedOrbit 15 20495 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20495) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20495.1, data_15_20495.2]

/-- Complete interval computation for depth 15, residue 20496. -/
theorem bounds_15_20496 : exactInterval 15 20496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20496 : oddCount 20496 15 = 6 ∧ acceleratedOrbit 15 20496 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20496) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20496.1, data_15_20496.2]

/-- Complete interval computation for depth 15, residue 20497. -/
theorem bounds_15_20497 : exactInterval 15 20497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20497 : oddCount 20497 15 = 7 ∧ acceleratedOrbit 15 20497 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20497) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20497.1, data_15_20497.2]

/-- Complete interval computation for depth 15, residue 20498. -/
theorem bounds_15_20498 : exactInterval 15 20498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20498 : oddCount 20498 15 = 8 ∧ acceleratedOrbit 15 20498 = 4106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20498) = 3 ^ 8 * m + 4106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20498.1, data_15_20498.2]

/-- Complete interval computation for depth 15, residue 20499. -/
theorem bounds_15_20499 : exactInterval 15 20499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20499 : oddCount 20499 15 = 8 ∧ acceleratedOrbit 15 20499 = 4106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20499) = 3 ^ 8 * m + 4106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20499.1, data_15_20499.2]

/-- Complete interval computation for depth 15, residue 20500. -/
theorem bounds_15_20500 : exactInterval 15 20500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20500 : oddCount 20500 15 = 6 ∧ acceleratedOrbit 15 20500 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20500) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20500.1, data_15_20500.2]

/-- Complete interval computation for depth 15, residue 20501. -/
theorem bounds_15_20501 : exactInterval 15 20501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20501 : oddCount 20501 15 = 6 ∧ acceleratedOrbit 15 20501 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20501) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20501.1, data_15_20501.2]

/-- Complete interval computation for depth 15, residue 20502. -/
theorem bounds_15_20502 : exactInterval 15 20502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20502 : oddCount 20502 15 = 7 ∧ acceleratedOrbit 15 20502 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20502) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20502.1, data_15_20502.2]

/-- Complete interval computation for depth 15, residue 20503. -/
theorem bounds_15_20503 : exactInterval 15 20503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20503 : oddCount 20503 15 = 7 ∧ acceleratedOrbit 15 20503 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20503) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20503.1, data_15_20503.2]

/-- Complete interval computation for depth 15, residue 20504. -/
theorem bounds_15_20504 : exactInterval 15 20504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20504 : oddCount 20504 15 = 6 ∧ acceleratedOrbit 15 20504 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20504) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20504.1, data_15_20504.2]

/-- Complete interval computation for depth 15, residue 20505. -/
theorem bounds_15_20505 : exactInterval 15 20505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20505 : oddCount 20505 15 = 7 ∧ acceleratedOrbit 15 20505 = 1369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20505) = 3 ^ 7 * m + 1369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20505.1, data_15_20505.2]

/-- Complete interval computation for depth 15, residue 20506. -/
theorem bounds_15_20506 : exactInterval 15 20506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20506 : oddCount 20506 15 = 6 ∧ acceleratedOrbit 15 20506 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20506) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20506.1, data_15_20506.2]

/-- Complete interval computation for depth 15, residue 20507. -/
theorem bounds_15_20507 : exactInterval 15 20507 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20507) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20507 : oddCount 20507 15 = 9 ∧ acceleratedOrbit 15 20507 = 12319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20507) = 3 ^ 9 * m + 12319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20507.1, data_15_20507.2]

/-- Complete interval computation for depth 15, residue 20508. -/
theorem bounds_15_20508 : exactInterval 15 20508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20508 : oddCount 20508 15 = 7 ∧ acceleratedOrbit 15 20508 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20508) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20508.1, data_15_20508.2]

/-- Complete interval computation for depth 15, residue 20509. -/
theorem bounds_15_20509 : exactInterval 15 20509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20509 : oddCount 20509 15 = 7 ∧ acceleratedOrbit 15 20509 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20509) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20509.1, data_15_20509.2]

/-- Complete interval computation for depth 15, residue 20510. -/
theorem bounds_15_20510 : exactInterval 15 20510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20510 : oddCount 20510 15 = 7 ∧ acceleratedOrbit 15 20510 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20510) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20510.1, data_15_20510.2]

/-- Complete interval computation for depth 15, residue 20511. -/
theorem bounds_15_20511 : exactInterval 15 20511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20511 : oddCount 20511 15 = 10 ∧ acceleratedOrbit 15 20511 = 36964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20511) = 3 ^ 10 * m + 36964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20511.1, data_15_20511.2]

end Collatz.Research.PassageAtlas.Batch0626
