import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0718

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23494. -/
theorem bounds_15_23494 : exactInterval 15 23494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23494 : oddCount 23494 15 = 5 ∧ acceleratedOrbit 15 23494 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23494) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23494.1, data_15_23494.2]

/-- Complete interval computation for depth 15, residue 23495. -/
theorem bounds_15_23495 : exactInterval 15 23495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23495 : oddCount 23495 15 = 11 ∧ acceleratedOrbit 15 23495 = 127028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23495) = 3 ^ 11 * m + 127028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23495.1, data_15_23495.2]

/-- Complete interval computation for depth 15, residue 23496. -/
theorem bounds_15_23496 : exactInterval 15 23496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23496 : oddCount 23496 15 = 8 ∧ acceleratedOrbit 15 23496 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23496) = 3 ^ 8 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23496.1, data_15_23496.2]

/-- Complete interval computation for depth 15, residue 23497. -/
theorem bounds_15_23497 : exactInterval 15 23497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23497 : oddCount 23497 15 = 8 ∧ acceleratedOrbit 15 23497 = 4706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23497) = 3 ^ 8 * m + 4706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23497.1, data_15_23497.2]

/-- Complete interval computation for depth 15, residue 23498. -/
theorem bounds_15_23498 : exactInterval 15 23498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23498 : oddCount 23498 15 = 8 ∧ acceleratedOrbit 15 23498 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23498) = 3 ^ 8 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23498.1, data_15_23498.2]

/-- Complete interval computation for depth 15, residue 23499. -/
theorem bounds_15_23499 : exactInterval 15 23499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23499 : oddCount 23499 15 = 6 ∧ acceleratedOrbit 15 23499 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23499) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23499.1, data_15_23499.2]

/-- Complete interval computation for depth 15, residue 23500. -/
theorem bounds_15_23500 : exactInterval 15 23500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23500 : oddCount 23500 15 = 8 ∧ acceleratedOrbit 15 23500 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23500) = 3 ^ 8 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23500.1, data_15_23500.2]

/-- Complete interval computation for depth 15, residue 23501. -/
theorem bounds_15_23501 : exactInterval 15 23501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23501 : oddCount 23501 15 = 8 ∧ acceleratedOrbit 15 23501 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23501) = 3 ^ 8 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23501.1, data_15_23501.2]

/-- Complete interval computation for depth 15, residue 23502. -/
theorem bounds_15_23502 : exactInterval 15 23502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23502 : oddCount 23502 15 = 9 ∧ acceleratedOrbit 15 23502 = 14120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23502) = 3 ^ 9 * m + 14120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23502.1, data_15_23502.2]

/-- Complete interval computation for depth 15, residue 23503. -/
theorem bounds_15_23503 : exactInterval 15 23503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23503 : oddCount 23503 15 = 9 ∧ acceleratedOrbit 15 23503 = 14120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23503) = 3 ^ 9 * m + 14120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23503.1, data_15_23503.2]

/-- Complete interval computation for depth 15, residue 23504. -/
theorem bounds_15_23504 : exactInterval 15 23504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23504 : oddCount 23504 15 = 6 ∧ acceleratedOrbit 15 23504 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23504) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23504.1, data_15_23504.2]

/-- Complete interval computation for depth 15, residue 23505. -/
theorem bounds_15_23505 : exactInterval 15 23505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23505 : oddCount 23505 15 = 8 ∧ acceleratedOrbit 15 23505 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23505) = 3 ^ 8 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23505.1, data_15_23505.2]

/-- Complete interval computation for depth 15, residue 23506. -/
theorem bounds_15_23506 : exactInterval 15 23506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23506 : oddCount 23506 15 = 9 ∧ acceleratedOrbit 15 23506 = 14122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23506) = 3 ^ 9 * m + 14122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23506.1, data_15_23506.2]

/-- Complete interval computation for depth 15, residue 23507. -/
theorem bounds_15_23507 : exactInterval 15 23507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23507 : oddCount 23507 15 = 9 ∧ acceleratedOrbit 15 23507 = 14122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23507) = 3 ^ 9 * m + 14122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23507.1, data_15_23507.2]

/-- Complete interval computation for depth 15, residue 23508. -/
theorem bounds_15_23508 : exactInterval 15 23508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23508 : oddCount 23508 15 = 6 ∧ acceleratedOrbit 15 23508 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23508) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23508.1, data_15_23508.2]

/-- Complete interval computation for depth 15, residue 23509. -/
theorem bounds_15_23509 : exactInterval 15 23509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23509 : oddCount 23509 15 = 6 ∧ acceleratedOrbit 15 23509 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23509) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23509.1, data_15_23509.2]

/-- Complete interval computation for depth 15, residue 23510. -/
theorem bounds_15_23510 : exactInterval 15 23510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23510 : oddCount 23510 15 = 10 ∧ acceleratedOrbit 15 23510 = 42373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23510) = 3 ^ 10 * m + 42373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23510.1, data_15_23510.2]

/-- Complete interval computation for depth 15, residue 23511. -/
theorem bounds_15_23511 : exactInterval 15 23511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23511 : oddCount 23511 15 = 10 ∧ acceleratedOrbit 15 23511 = 42373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23511) = 3 ^ 10 * m + 42373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23511.1, data_15_23511.2]

/-- Complete interval computation for depth 15, residue 23512. -/
theorem bounds_15_23512 : exactInterval 15 23512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23512 : oddCount 23512 15 = 8 ∧ acceleratedOrbit 15 23512 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23512) = 3 ^ 8 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23512.1, data_15_23512.2]

/-- Complete interval computation for depth 15, residue 23513. -/
theorem bounds_15_23513 : exactInterval 15 23513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23513 : oddCount 23513 15 = 5 ∧ acceleratedOrbit 15 23513 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23513) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23513.1, data_15_23513.2]

/-- Complete interval computation for depth 15, residue 23514. -/
theorem bounds_15_23514 : exactInterval 15 23514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23514 : oddCount 23514 15 = 8 ∧ acceleratedOrbit 15 23514 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23514) = 3 ^ 8 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23514.1, data_15_23514.2]

/-- Complete interval computation for depth 15, residue 23515. -/
theorem bounds_15_23515 : exactInterval 15 23515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23515 : oddCount 23515 15 = 8 ∧ acceleratedOrbit 15 23515 = 4709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23515) = 3 ^ 8 * m + 4709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23515.1, data_15_23515.2]

/-- Complete interval computation for depth 15, residue 23516. -/
theorem bounds_15_23516 : exactInterval 15 23516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23516 : oddCount 23516 15 = 8 ∧ acceleratedOrbit 15 23516 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23516) = 3 ^ 8 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23516.1, data_15_23516.2]

/-- Complete interval computation for depth 15, residue 23517. -/
theorem bounds_15_23517 : exactInterval 15 23517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23517 : oddCount 23517 15 = 8 ∧ acceleratedOrbit 15 23517 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23517) = 3 ^ 8 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23517.1, data_15_23517.2]

/-- Complete interval computation for depth 15, residue 23518. -/
theorem bounds_15_23518 : exactInterval 15 23518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23518 : oddCount 23518 15 = 10 ∧ acceleratedOrbit 15 23518 = 42385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23518) = 3 ^ 10 * m + 42385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23518.1, data_15_23518.2]

/-- Complete interval computation for depth 15, residue 23519. -/
theorem bounds_15_23519 : exactInterval 15 23519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23519 : oddCount 23519 15 = 10 ∧ acceleratedOrbit 15 23519 = 42385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23519) = 3 ^ 10 * m + 42385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23519.1, data_15_23519.2]

/-- Complete interval computation for depth 15, residue 23520. -/
theorem bounds_15_23520 : exactInterval 15 23520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23520 : oddCount 23520 15 = 6 ∧ acceleratedOrbit 15 23520 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23520) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23520.1, data_15_23520.2]

/-- Complete interval computation for depth 15, residue 23521. -/
theorem bounds_15_23521 : exactInterval 15 23521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23521 : oddCount 23521 15 = 7 ∧ acceleratedOrbit 15 23521 = 1570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23521) = 3 ^ 7 * m + 1570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23521.1, data_15_23521.2]

/-- Complete interval computation for depth 15, residue 23522. -/
theorem bounds_15_23522 : exactInterval 15 23522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23522 : oddCount 23522 15 = 6 ∧ acceleratedOrbit 15 23522 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23522) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23522.1, data_15_23522.2]

/-- Complete interval computation for depth 15, residue 23523. -/
theorem bounds_15_23523 : exactInterval 15 23523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23523 : oddCount 23523 15 = 6 ∧ acceleratedOrbit 15 23523 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23523) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23523.1, data_15_23523.2]

/-- Complete interval computation for depth 15, residue 23524. -/
theorem bounds_15_23524 : exactInterval 15 23524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23524 : oddCount 23524 15 = 6 ∧ acceleratedOrbit 15 23524 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23524) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23524.1, data_15_23524.2]

/-- Complete interval computation for depth 15, residue 23525. -/
theorem bounds_15_23525 : exactInterval 15 23525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23525 : oddCount 23525 15 = 6 ∧ acceleratedOrbit 15 23525 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23525) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23525.1, data_15_23525.2]

/-- Complete interval computation for depth 15, residue 23526. -/
theorem bounds_15_23526 : exactInterval 15 23526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23526 : oddCount 23526 15 = 6 ∧ acceleratedOrbit 15 23526 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23526) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23526.1, data_15_23526.2]

end Collatz.Research.PassageAtlas.Batch0718
