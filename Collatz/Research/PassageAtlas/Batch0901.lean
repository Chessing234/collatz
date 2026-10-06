import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0901

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29491. -/
theorem bounds_15_29491 : exactInterval 15 29491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29491 : oddCount 29491 15 = 7 ∧ acceleratedOrbit 15 29491 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29491) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29491.1, data_15_29491.2]

/-- Complete interval computation for depth 15, residue 29492. -/
theorem bounds_15_29492 : exactInterval 15 29492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29492 : oddCount 29492 15 = 4 ∧ acceleratedOrbit 15 29492 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29492) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29492.1, data_15_29492.2]

/-- Complete interval computation for depth 15, residue 29493. -/
theorem bounds_15_29493 : exactInterval 15 29493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29493 : oddCount 29493 15 = 4 ∧ acceleratedOrbit 15 29493 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29493) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29493.1, data_15_29493.2]

/-- Complete interval computation for depth 15, residue 29494. -/
theorem bounds_15_29494 : exactInterval 15 29494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29494 : oddCount 29494 15 = 10 ∧ acceleratedOrbit 15 29494 = 53156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29494) = 3 ^ 10 * m + 53156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29494.1, data_15_29494.2]

/-- Complete interval computation for depth 15, residue 29495. -/
theorem bounds_15_29495 : exactInterval 15 29495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29495 : oddCount 29495 15 = 10 ∧ acceleratedOrbit 15 29495 = 53156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29495) = 3 ^ 10 * m + 53156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29495.1, data_15_29495.2]

/-- Complete interval computation for depth 15, residue 29496. -/
theorem bounds_15_29496 : exactInterval 15 29496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29496 : oddCount 29496 15 = 8 ∧ acceleratedOrbit 15 29496 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29496) = 3 ^ 8 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29496.1, data_15_29496.2]

/-- Complete interval computation for depth 15, residue 29497. -/
theorem bounds_15_29497 : exactInterval 15 29497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29497 : oddCount 29497 15 = 10 ∧ acceleratedOrbit 15 29497 = 53162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29497) = 3 ^ 10 * m + 53162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29497.1, data_15_29497.2]

/-- Complete interval computation for depth 15, residue 29498. -/
theorem bounds_15_29498 : exactInterval 15 29498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29498 : oddCount 29498 15 = 8 ∧ acceleratedOrbit 15 29498 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29498) = 3 ^ 8 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29498.1, data_15_29498.2]

/-- Complete interval computation for depth 15, residue 29499. -/
theorem bounds_15_29499 : exactInterval 15 29499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29499 : oddCount 29499 15 = 8 ∧ acceleratedOrbit 15 29499 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29499) = 3 ^ 8 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29499.1, data_15_29499.2]

/-- Complete interval computation for depth 15, residue 29500. -/
theorem bounds_15_29500 : exactInterval 15 29500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29500 : oddCount 29500 15 = 8 ∧ acceleratedOrbit 15 29500 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29500) = 3 ^ 8 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29500.1, data_15_29500.2]

/-- Complete interval computation for depth 15, residue 29501. -/
theorem bounds_15_29501 : exactInterval 15 29501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29501 : oddCount 29501 15 = 8 ∧ acceleratedOrbit 15 29501 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29501) = 3 ^ 8 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29501.1, data_15_29501.2]

/-- Complete interval computation for depth 15, residue 29502. -/
theorem bounds_15_29502 : exactInterval 15 29502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29502 : oddCount 29502 15 = 9 ∧ acceleratedOrbit 15 29502 = 17723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29502) = 3 ^ 9 * m + 17723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29502.1, data_15_29502.2]

/-- Complete interval computation for depth 15, residue 29503. -/
theorem bounds_15_29503 : exactInterval 15 29503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29503 : oddCount 29503 15 = 9 ∧ acceleratedOrbit 15 29503 = 17723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29503) = 3 ^ 9 * m + 17723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29503.1, data_15_29503.2]

/-- Complete interval computation for depth 15, residue 29504. -/
theorem bounds_15_29504 : exactInterval 15 29504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29504 : oddCount 29504 15 = 4 ∧ acceleratedOrbit 15 29504 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29504) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29504.1, data_15_29504.2]

/-- Complete interval computation for depth 15, residue 29505. -/
theorem bounds_15_29505 : exactInterval 15 29505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29505 : oddCount 29505 15 = 4 ∧ acceleratedOrbit 15 29505 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29505) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29505.1, data_15_29505.2]

/-- Complete interval computation for depth 15, residue 29506. -/
theorem bounds_15_29506 : exactInterval 15 29506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29506 : oddCount 29506 15 = 9 ∧ acceleratedOrbit 15 29506 = 17729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29506) = 3 ^ 9 * m + 17729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29506.1, data_15_29506.2]

/-- Complete interval computation for depth 15, residue 29507. -/
theorem bounds_15_29507 : exactInterval 15 29507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29507 : oddCount 29507 15 = 9 ∧ acceleratedOrbit 15 29507 = 17729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29507) = 3 ^ 9 * m + 17729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29507.1, data_15_29507.2]

/-- Complete interval computation for depth 15, residue 29508. -/
theorem bounds_15_29508 : exactInterval 15 29508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29508 : oddCount 29508 15 = 9 ∧ acceleratedOrbit 15 29508 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29508) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29508.1, data_15_29508.2]

/-- Complete interval computation for depth 15, residue 29509. -/
theorem bounds_15_29509 : exactInterval 15 29509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29509 : oddCount 29509 15 = 9 ∧ acceleratedOrbit 15 29509 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29509) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29509.1, data_15_29509.2]

/-- Complete interval computation for depth 15, residue 29510. -/
theorem bounds_15_29510 : exactInterval 15 29510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29510 : oddCount 29510 15 = 9 ∧ acceleratedOrbit 15 29510 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29510) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29510.1, data_15_29510.2]

/-- Complete interval computation for depth 15, residue 29511. -/
theorem bounds_15_29511 : exactInterval 15 29511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29511 : oddCount 29511 15 = 10 ∧ acceleratedOrbit 15 29511 = 53183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29511) = 3 ^ 10 * m + 53183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29511.1, data_15_29511.2]

/-- Complete interval computation for depth 15, residue 29512. -/
theorem bounds_15_29512 : exactInterval 15 29512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29512 : oddCount 29512 15 = 9 ∧ acceleratedOrbit 15 29512 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29512) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29512.1, data_15_29512.2]

/-- Complete interval computation for depth 15, residue 29513. -/
theorem bounds_15_29513 : exactInterval 15 29513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29513 : oddCount 29513 15 = 8 ∧ acceleratedOrbit 15 29513 = 5912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29513) = 3 ^ 8 * m + 5912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29513.1, data_15_29513.2]

/-- Complete interval computation for depth 15, residue 29514. -/
theorem bounds_15_29514 : exactInterval 15 29514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29514 : oddCount 29514 15 = 9 ∧ acceleratedOrbit 15 29514 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29514) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29514.1, data_15_29514.2]

/-- Complete interval computation for depth 15, residue 29515. -/
theorem bounds_15_29515 : exactInterval 15 29515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29515 : oddCount 29515 15 = 9 ∧ acceleratedOrbit 15 29515 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29515) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29515.1, data_15_29515.2]

/-- Complete interval computation for depth 15, residue 29516. -/
theorem bounds_15_29516 : exactInterval 15 29516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29516 : oddCount 29516 15 = 9 ∧ acceleratedOrbit 15 29516 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29516) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29516.1, data_15_29516.2]

/-- Complete interval computation for depth 15, residue 29517. -/
theorem bounds_15_29517 : exactInterval 15 29517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29517 : oddCount 29517 15 = 9 ∧ acceleratedOrbit 15 29517 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29517) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29517.1, data_15_29517.2]

/-- Complete interval computation for depth 15, residue 29518. -/
theorem bounds_15_29518 : exactInterval 15 29518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29518 : oddCount 29518 15 = 8 ∧ acceleratedOrbit 15 29518 = 5912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29518) = 3 ^ 8 * m + 5912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29518.1, data_15_29518.2]

/-- Complete interval computation for depth 15, residue 29519. -/
theorem bounds_15_29519 : exactInterval 15 29519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29519 : oddCount 29519 15 = 8 ∧ acceleratedOrbit 15 29519 = 5912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29519) = 3 ^ 8 * m + 5912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29519.1, data_15_29519.2]

/-- Complete interval computation for depth 15, residue 29520. -/
theorem bounds_15_29520 : exactInterval 15 29520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29520 : oddCount 29520 15 = 4 ∧ acceleratedOrbit 15 29520 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29520) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29520.1, data_15_29520.2]

/-- Complete interval computation for depth 15, residue 29521. -/
theorem bounds_15_29521 : exactInterval 15 29521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29521 : oddCount 29521 15 = 10 ∧ acceleratedOrbit 15 29521 = 53207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29521) = 3 ^ 10 * m + 53207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29521.1, data_15_29521.2]

/-- Complete interval computation for depth 15, residue 29522. -/
theorem bounds_15_29522 : exactInterval 15 29522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29522 : oddCount 29522 15 = 10 ∧ acceleratedOrbit 15 29522 = 53207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29522) = 3 ^ 10 * m + 53207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29522.1, data_15_29522.2]

end Collatz.Research.PassageAtlas.Batch0901
