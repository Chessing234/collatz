import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0840

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27492. -/
theorem bounds_15_27492 : exactInterval 15 27492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27492 : oddCount 27492 15 = 4 ∧ acceleratedOrbit 15 27492 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27492) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27492.1, data_15_27492.2]

/-- Complete interval computation for depth 15, residue 27493. -/
theorem bounds_15_27493 : exactInterval 15 27493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27493 : oddCount 27493 15 = 4 ∧ acceleratedOrbit 15 27493 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27493) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27493.1, data_15_27493.2]

/-- Complete interval computation for depth 15, residue 27494. -/
theorem bounds_15_27494 : exactInterval 15 27494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27494 : oddCount 27494 15 = 4 ∧ acceleratedOrbit 15 27494 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27494) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27494.1, data_15_27494.2]

/-- Complete interval computation for depth 15, residue 27495. -/
theorem bounds_15_27495 : exactInterval 15 27495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27495 : oddCount 27495 15 = 11 ∧ acceleratedOrbit 15 27495 = 148648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27495) = 3 ^ 11 * m + 148648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27495.1, data_15_27495.2]

/-- Complete interval computation for depth 15, residue 27496. -/
theorem bounds_15_27496 : exactInterval 15 27496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27496 : oddCount 27496 15 = 7 ∧ acceleratedOrbit 15 27496 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27496) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27496.1, data_15_27496.2]

/-- Complete interval computation for depth 15, residue 27497. -/
theorem bounds_15_27497 : exactInterval 15 27497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27497 : oddCount 27497 15 = 9 ∧ acceleratedOrbit 15 27497 = 16519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27497) = 3 ^ 9 * m + 16519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27497.1, data_15_27497.2]

/-- Complete interval computation for depth 15, residue 27498. -/
theorem bounds_15_27498 : exactInterval 15 27498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27498 : oddCount 27498 15 = 7 ∧ acceleratedOrbit 15 27498 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27498) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27498.1, data_15_27498.2]

/-- Complete interval computation for depth 15, residue 27499. -/
theorem bounds_15_27499 : exactInterval 15 27499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27499 : oddCount 27499 15 = 9 ∧ acceleratedOrbit 15 27499 = 16523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27499) = 3 ^ 9 * m + 16523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27499.1, data_15_27499.2]

/-- Complete interval computation for depth 15, residue 27500. -/
theorem bounds_15_27500 : exactInterval 15 27500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27500 : oddCount 27500 15 = 10 ∧ acceleratedOrbit 15 27500 = 49571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27500) = 3 ^ 10 * m + 49571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27500.1, data_15_27500.2]

/-- Complete interval computation for depth 15, residue 27501. -/
theorem bounds_15_27501 : exactInterval 15 27501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27501 : oddCount 27501 15 = 10 ∧ acceleratedOrbit 15 27501 = 49571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27501) = 3 ^ 10 * m + 49571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27501.1, data_15_27501.2]

/-- Complete interval computation for depth 15, residue 27502. -/
theorem bounds_15_27502 : exactInterval 15 27502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27502 : oddCount 27502 15 = 10 ∧ acceleratedOrbit 15 27502 = 49571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27502) = 3 ^ 10 * m + 49571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27502.1, data_15_27502.2]

/-- Complete interval computation for depth 15, residue 27503. -/
theorem bounds_15_27503 : exactInterval 15 27503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27503 : oddCount 27503 15 = 10 ∧ acceleratedOrbit 15 27503 = 49565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27503) = 3 ^ 10 * m + 49565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27503.1, data_15_27503.2]

/-- Complete interval computation for depth 15, residue 27504. -/
theorem bounds_15_27504 : exactInterval 15 27504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27504 : oddCount 27504 15 = 7 ∧ acceleratedOrbit 15 27504 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27504) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27504.1, data_15_27504.2]

/-- Complete interval computation for depth 15, residue 27505. -/
theorem bounds_15_27505 : exactInterval 15 27505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27505 : oddCount 27505 15 = 7 ∧ acceleratedOrbit 15 27505 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27505) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27505.1, data_15_27505.2]

/-- Complete interval computation for depth 15, residue 27506. -/
theorem bounds_15_27506 : exactInterval 15 27506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27506 : oddCount 27506 15 = 4 ∧ acceleratedOrbit 15 27506 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27506) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27506.1, data_15_27506.2]

/-- Complete interval computation for depth 15, residue 27507. -/
theorem bounds_15_27507 : exactInterval 15 27507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27507 : oddCount 27507 15 = 4 ∧ acceleratedOrbit 15 27507 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27507) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27507.1, data_15_27507.2]

/-- Complete interval computation for depth 15, residue 27508. -/
theorem bounds_15_27508 : exactInterval 15 27508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27508 : oddCount 27508 15 = 7 ∧ acceleratedOrbit 15 27508 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27508) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27508.1, data_15_27508.2]

/-- Complete interval computation for depth 15, residue 27509. -/
theorem bounds_15_27509 : exactInterval 15 27509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27509 : oddCount 27509 15 = 7 ∧ acceleratedOrbit 15 27509 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27509) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27509.1, data_15_27509.2]

/-- Complete interval computation for depth 15, residue 27510. -/
theorem bounds_15_27510 : exactInterval 15 27510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27510 : oddCount 27510 15 = 8 ∧ acceleratedOrbit 15 27510 = 5510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27510) = 3 ^ 8 * m + 5510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27510.1, data_15_27510.2]

/-- Complete interval computation for depth 15, residue 27511. -/
theorem bounds_15_27511 : exactInterval 15 27511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27511 : oddCount 27511 15 = 8 ∧ acceleratedOrbit 15 27511 = 5510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27511) = 3 ^ 8 * m + 5510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27511.1, data_15_27511.2]

/-- Complete interval computation for depth 15, residue 27512. -/
theorem bounds_15_27512 : exactInterval 15 27512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27512 : oddCount 27512 15 = 7 ∧ acceleratedOrbit 15 27512 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27512) = 3 ^ 7 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27512.1, data_15_27512.2]

/-- Complete interval computation for depth 15, residue 27513. -/
theorem bounds_15_27513 : exactInterval 15 27513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27513 : oddCount 27513 15 = 9 ∧ acceleratedOrbit 15 27513 = 16528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27513) = 3 ^ 9 * m + 16528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27513.1, data_15_27513.2]

/-- Complete interval computation for depth 15, residue 27514. -/
theorem bounds_15_27514 : exactInterval 15 27514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27514 : oddCount 27514 15 = 7 ∧ acceleratedOrbit 15 27514 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27514) = 3 ^ 7 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27514.1, data_15_27514.2]

/-- Complete interval computation for depth 15, residue 27515. -/
theorem bounds_15_27515 : exactInterval 15 27515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27515 : oddCount 27515 15 = 9 ∧ acceleratedOrbit 15 27515 = 16529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27515) = 3 ^ 9 * m + 16529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27515.1, data_15_27515.2]

/-- Complete interval computation for depth 15, residue 27516. -/
theorem bounds_15_27516 : exactInterval 15 27516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27516 : oddCount 27516 15 = 7 ∧ acceleratedOrbit 15 27516 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27516) = 3 ^ 7 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27516.1, data_15_27516.2]

/-- Complete interval computation for depth 15, residue 27517. -/
theorem bounds_15_27517 : exactInterval 15 27517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27517 : oddCount 27517 15 = 7 ∧ acceleratedOrbit 15 27517 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27517) = 3 ^ 7 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27517.1, data_15_27517.2]

/-- Complete interval computation for depth 15, residue 27518. -/
theorem bounds_15_27518 : exactInterval 15 27518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27518 : oddCount 27518 15 = 12 ∧ acceleratedOrbit 15 27518 = 446330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27518) = 3 ^ 12 * m + 446330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27518.1, data_15_27518.2]

/-- Complete interval computation for depth 15, residue 27519. -/
theorem bounds_15_27519 : exactInterval 15 27519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27519 : oddCount 27519 15 = 12 ∧ acceleratedOrbit 15 27519 = 446330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27519) = 3 ^ 12 * m + 446330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27519.1, data_15_27519.2]

/-- Complete interval computation for depth 15, residue 27520. -/
theorem bounds_15_27520 : exactInterval 15 27520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27520 : oddCount 27520 15 = 5 ∧ acceleratedOrbit 15 27520 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27520) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27520.1, data_15_27520.2]

/-- Complete interval computation for depth 15, residue 27521. -/
theorem bounds_15_27521 : exactInterval 15 27521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27521 : oddCount 27521 15 = 9 ∧ acceleratedOrbit 15 27521 = 16534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27521) = 3 ^ 9 * m + 16534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27521.1, data_15_27521.2]

/-- Complete interval computation for depth 15, residue 27522. -/
theorem bounds_15_27522 : exactInterval 15 27522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27522 : oddCount 27522 15 = 7 ∧ acceleratedOrbit 15 27522 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27522) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27522.1, data_15_27522.2]

/-- Complete interval computation for depth 15, residue 27523. -/
theorem bounds_15_27523 : exactInterval 15 27523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27523 : oddCount 27523 15 = 7 ∧ acceleratedOrbit 15 27523 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27523) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27523.1, data_15_27523.2]

/-- Complete interval computation for depth 15, residue 27524. -/
theorem bounds_15_27524 : exactInterval 15 27524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27524 : oddCount 27524 15 = 8 ∧ acceleratedOrbit 15 27524 = 5513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27524) = 3 ^ 8 * m + 5513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27524.1, data_15_27524.2]

end Collatz.Research.PassageAtlas.Batch0840
