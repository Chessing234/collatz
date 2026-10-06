import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0596

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19496. -/
theorem bounds_15_19496 : exactInterval 15 19496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19496 : oddCount 19496 15 = 5 ∧ acceleratedOrbit 15 19496 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19496) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19496.1, data_15_19496.2]

/-- Complete interval computation for depth 15, residue 19497. -/
theorem bounds_15_19497 : exactInterval 15 19497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19497 : oddCount 19497 15 = 9 ∧ acceleratedOrbit 15 19497 = 11713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19497) = 3 ^ 9 * m + 11713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19497.1, data_15_19497.2]

/-- Complete interval computation for depth 15, residue 19498. -/
theorem bounds_15_19498 : exactInterval 15 19498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19498 : oddCount 19498 15 = 5 ∧ acceleratedOrbit 15 19498 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19498) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19498.1, data_15_19498.2]

/-- Complete interval computation for depth 15, residue 19499. -/
theorem bounds_15_19499 : exactInterval 15 19499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19499 : oddCount 19499 15 = 6 ∧ acceleratedOrbit 15 19499 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19499) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19499.1, data_15_19499.2]

/-- Complete interval computation for depth 15, residue 19500. -/
theorem bounds_15_19500 : exactInterval 15 19500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19500 : oddCount 19500 15 = 8 ∧ acceleratedOrbit 15 19500 = 3908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19500) = 3 ^ 8 * m + 3908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19500.1, data_15_19500.2]

/-- Complete interval computation for depth 15, residue 19501. -/
theorem bounds_15_19501 : exactInterval 15 19501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19501 : oddCount 19501 15 = 8 ∧ acceleratedOrbit 15 19501 = 3908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19501) = 3 ^ 8 * m + 3908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19501.1, data_15_19501.2]

/-- Complete interval computation for depth 15, residue 19502. -/
theorem bounds_15_19502 : exactInterval 15 19502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19502 : oddCount 19502 15 = 8 ∧ acceleratedOrbit 15 19502 = 3908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19502) = 3 ^ 8 * m + 3908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19502.1, data_15_19502.2]

/-- Complete interval computation for depth 15, residue 19503. -/
theorem bounds_15_19503 : exactInterval 15 19503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19503 : oddCount 19503 15 = 9 ∧ acceleratedOrbit 15 19503 = 11717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19503) = 3 ^ 9 * m + 11717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19503.1, data_15_19503.2]

/-- Complete interval computation for depth 15, residue 19504. -/
theorem bounds_15_19504 : exactInterval 15 19504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19504 : oddCount 19504 15 = 5 ∧ acceleratedOrbit 15 19504 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19504) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19504.1, data_15_19504.2]

/-- Complete interval computation for depth 15, residue 19505. -/
theorem bounds_15_19505 : exactInterval 15 19505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19505 : oddCount 19505 15 = 8 ∧ acceleratedOrbit 15 19505 = 3908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19505) = 3 ^ 8 * m + 3908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19505.1, data_15_19505.2]

/-- Complete interval computation for depth 15, residue 19506. -/
theorem bounds_15_19506 : exactInterval 15 19506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19506 : oddCount 19506 15 = 8 ∧ acceleratedOrbit 15 19506 = 3908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19506) = 3 ^ 8 * m + 3908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19506.1, data_15_19506.2]

/-- Complete interval computation for depth 15, residue 19507. -/
theorem bounds_15_19507 : exactInterval 15 19507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19507 : oddCount 19507 15 = 8 ∧ acceleratedOrbit 15 19507 = 3908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19507) = 3 ^ 8 * m + 3908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19507.1, data_15_19507.2]

/-- Complete interval computation for depth 15, residue 19508. -/
theorem bounds_15_19508 : exactInterval 15 19508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19508 : oddCount 19508 15 = 5 ∧ acceleratedOrbit 15 19508 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19508) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19508.1, data_15_19508.2]

/-- Complete interval computation for depth 15, residue 19509. -/
theorem bounds_15_19509 : exactInterval 15 19509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19509 : oddCount 19509 15 = 5 ∧ acceleratedOrbit 15 19509 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19509) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19509.1, data_15_19509.2]

/-- Complete interval computation for depth 15, residue 19510. -/
theorem bounds_15_19510 : exactInterval 15 19510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19510 : oddCount 19510 15 = 8 ∧ acceleratedOrbit 15 19510 = 3907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19510) = 3 ^ 8 * m + 3907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19510.1, data_15_19510.2]

/-- Complete interval computation for depth 15, residue 19511. -/
theorem bounds_15_19511 : exactInterval 15 19511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19511 : oddCount 19511 15 = 8 ∧ acceleratedOrbit 15 19511 = 3907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19511) = 3 ^ 8 * m + 3907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19511.1, data_15_19511.2]

/-- Complete interval computation for depth 15, residue 19512. -/
theorem bounds_15_19512 : exactInterval 15 19512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19512 : oddCount 19512 15 = 5 ∧ acceleratedOrbit 15 19512 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19512) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19512.1, data_15_19512.2]

/-- Complete interval computation for depth 15, residue 19513. -/
theorem bounds_15_19513 : exactInterval 15 19513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19513 : oddCount 19513 15 = 8 ∧ acceleratedOrbit 15 19513 = 3908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19513) = 3 ^ 8 * m + 3908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19513.1, data_15_19513.2]

/-- Complete interval computation for depth 15, residue 19514. -/
theorem bounds_15_19514 : exactInterval 15 19514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19514 : oddCount 19514 15 = 5 ∧ acceleratedOrbit 15 19514 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19514) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19514.1, data_15_19514.2]

/-- Complete interval computation for depth 15, residue 19515. -/
theorem bounds_15_19515 : exactInterval 15 19515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19515 : oddCount 19515 15 = 10 ∧ acceleratedOrbit 15 19515 = 35174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19515) = 3 ^ 10 * m + 35174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19515.1, data_15_19515.2]

/-- Complete interval computation for depth 15, residue 19516. -/
theorem bounds_15_19516 : exactInterval 15 19516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19516 : oddCount 19516 15 = 5 ∧ acceleratedOrbit 15 19516 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19516) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19516.1, data_15_19516.2]

/-- Complete interval computation for depth 15, residue 19517. -/
theorem bounds_15_19517 : exactInterval 15 19517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19517 : oddCount 19517 15 = 5 ∧ acceleratedOrbit 15 19517 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19517) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19517.1, data_15_19517.2]

/-- Complete interval computation for depth 15, residue 19518. -/
theorem bounds_15_19518 : exactInterval 15 19518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19518 : oddCount 19518 15 = 9 ∧ acceleratedOrbit 15 19518 = 11726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19518) = 3 ^ 9 * m + 11726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19518.1, data_15_19518.2]

/-- Complete interval computation for depth 15, residue 19519. -/
theorem bounds_15_19519 : exactInterval 15 19519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19519 : oddCount 19519 15 = 9 ∧ acceleratedOrbit 15 19519 = 11726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19519) = 3 ^ 9 * m + 11726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19519.1, data_15_19519.2]

/-- Complete interval computation for depth 15, residue 19520. -/
theorem bounds_15_19520 : exactInterval 15 19520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19520 : oddCount 19520 15 = 4 ∧ acceleratedOrbit 15 19520 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19520) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19520.1, data_15_19520.2]

/-- Complete interval computation for depth 15, residue 19521. -/
theorem bounds_15_19521 : exactInterval 15 19521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19521 : oddCount 19521 15 = 7 ∧ acceleratedOrbit 15 19521 = 1304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19521) = 3 ^ 7 * m + 1304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19521.1, data_15_19521.2]

/-- Complete interval computation for depth 15, residue 19522. -/
theorem bounds_15_19522 : exactInterval 15 19522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19522 : oddCount 19522 15 = 7 ∧ acceleratedOrbit 15 19522 = 1304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19522) = 3 ^ 7 * m + 1304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19522.1, data_15_19522.2]

/-- Complete interval computation for depth 15, residue 19523. -/
theorem bounds_15_19523 : exactInterval 15 19523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19523 : oddCount 19523 15 = 7 ∧ acceleratedOrbit 15 19523 = 1304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19523) = 3 ^ 7 * m + 1304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19523.1, data_15_19523.2]

/-- Complete interval computation for depth 15, residue 19524. -/
theorem bounds_15_19524 : exactInterval 15 19524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19524 : oddCount 19524 15 = 5 ∧ acceleratedOrbit 15 19524 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19524) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19524.1, data_15_19524.2]

/-- Complete interval computation for depth 15, residue 19525. -/
theorem bounds_15_19525 : exactInterval 15 19525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19525 : oddCount 19525 15 = 5 ∧ acceleratedOrbit 15 19525 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19525) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19525.1, data_15_19525.2]

/-- Complete interval computation for depth 15, residue 19526. -/
theorem bounds_15_19526 : exactInterval 15 19526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19526 : oddCount 19526 15 = 5 ∧ acceleratedOrbit 15 19526 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19526) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19526.1, data_15_19526.2]

/-- Complete interval computation for depth 15, residue 19527. -/
theorem bounds_15_19527 : exactInterval 15 19527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19527 : oddCount 19527 15 = 9 ∧ acceleratedOrbit 15 19527 = 11731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19527) = 3 ^ 9 * m + 11731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19527.1, data_15_19527.2]

/-- Complete interval computation for depth 15, residue 19528. -/
theorem bounds_15_19528 : exactInterval 15 19528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19528 : oddCount 19528 15 = 8 ∧ acceleratedOrbit 15 19528 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19528) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19528.1, data_15_19528.2]

end Collatz.Research.PassageAtlas.Batch0596
