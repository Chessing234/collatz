import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0871

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28508. -/
theorem bounds_15_28508 : exactInterval 15 28508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28508 : oddCount 28508 15 = 9 ∧ acceleratedOrbit 15 28508 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28508) = 3 ^ 9 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28508.1, data_15_28508.2]

/-- Complete interval computation for depth 15, residue 28509. -/
theorem bounds_15_28509 : exactInterval 15 28509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28509 : oddCount 28509 15 = 9 ∧ acceleratedOrbit 15 28509 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28509) = 3 ^ 9 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28509.1, data_15_28509.2]

/-- Complete interval computation for depth 15, residue 28510. -/
theorem bounds_15_28510 : exactInterval 15 28510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28510 : oddCount 28510 15 = 8 ∧ acceleratedOrbit 15 28510 = 5710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28510) = 3 ^ 8 * m + 5710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28510.1, data_15_28510.2]

/-- Complete interval computation for depth 15, residue 28511. -/
theorem bounds_15_28511 : exactInterval 15 28511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28511 : oddCount 28511 15 = 8 ∧ acceleratedOrbit 15 28511 = 5710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28511) = 3 ^ 8 * m + 5710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28511.1, data_15_28511.2]

/-- Complete interval computation for depth 15, residue 28512. -/
theorem bounds_15_28512 : exactInterval 15 28512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28512 : oddCount 28512 15 = 7 ∧ acceleratedOrbit 15 28512 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28512) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28512.1, data_15_28512.2]

/-- Complete interval computation for depth 15, residue 28513. -/
theorem bounds_15_28513 : exactInterval 15 28513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28513 : oddCount 28513 15 = 9 ∧ acceleratedOrbit 15 28513 = 17129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28513) = 3 ^ 9 * m + 17129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28513.1, data_15_28513.2]

/-- Complete interval computation for depth 15, residue 28514. -/
theorem bounds_15_28514 : exactInterval 15 28514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28514 : oddCount 28514 15 = 4 ∧ acceleratedOrbit 15 28514 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28514) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28514.1, data_15_28514.2]

/-- Complete interval computation for depth 15, residue 28515. -/
theorem bounds_15_28515 : exactInterval 15 28515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28515 : oddCount 28515 15 = 4 ∧ acceleratedOrbit 15 28515 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28515) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28515.1, data_15_28515.2]

/-- Complete interval computation for depth 15, residue 28516. -/
theorem bounds_15_28516 : exactInterval 15 28516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28516 : oddCount 28516 15 = 4 ∧ acceleratedOrbit 15 28516 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28516) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28516.1, data_15_28516.2]

/-- Complete interval computation for depth 15, residue 28517. -/
theorem bounds_15_28517 : exactInterval 15 28517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28517 : oddCount 28517 15 = 4 ∧ acceleratedOrbit 15 28517 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28517) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28517.1, data_15_28517.2]

/-- Complete interval computation for depth 15, residue 28518. -/
theorem bounds_15_28518 : exactInterval 15 28518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28518 : oddCount 28518 15 = 4 ∧ acceleratedOrbit 15 28518 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28518) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28518.1, data_15_28518.2]

/-- Complete interval computation for depth 15, residue 28519. -/
theorem bounds_15_28519 : exactInterval 15 28519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28519 : oddCount 28519 15 = 13 ∧ acceleratedOrbit 15 28519 = 1387651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28519) = 3 ^ 13 * m + 1387651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28519.1, data_15_28519.2]

/-- Complete interval computation for depth 15, residue 28520. -/
theorem bounds_15_28520 : exactInterval 15 28520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28520 : oddCount 28520 15 = 7 ∧ acceleratedOrbit 15 28520 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28520) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28520.1, data_15_28520.2]

/-- Complete interval computation for depth 15, residue 28521. -/
theorem bounds_15_28521 : exactInterval 15 28521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28521 : oddCount 28521 15 = 9 ∧ acceleratedOrbit 15 28521 = 17135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28521) = 3 ^ 9 * m + 17135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28521.1, data_15_28521.2]

/-- Complete interval computation for depth 15, residue 28522. -/
theorem bounds_15_28522 : exactInterval 15 28522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28522 : oddCount 28522 15 = 7 ∧ acceleratedOrbit 15 28522 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28522) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28522.1, data_15_28522.2]

/-- Complete interval computation for depth 15, residue 28523. -/
theorem bounds_15_28523 : exactInterval 15 28523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28523 : oddCount 28523 15 = 7 ∧ acceleratedOrbit 15 28523 = 1904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28523) = 3 ^ 7 * m + 1904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28523.1, data_15_28523.2]

/-- Complete interval computation for depth 15, residue 28524. -/
theorem bounds_15_28524 : exactInterval 15 28524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28524 : oddCount 28524 15 = 8 ∧ acceleratedOrbit 15 28524 = 5714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28524) = 3 ^ 8 * m + 5714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28524.1, data_15_28524.2]

/-- Complete interval computation for depth 15, residue 28525. -/
theorem bounds_15_28525 : exactInterval 15 28525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28525 : oddCount 28525 15 = 8 ∧ acceleratedOrbit 15 28525 = 5714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28525) = 3 ^ 8 * m + 5714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28525.1, data_15_28525.2]

/-- Complete interval computation for depth 15, residue 28526. -/
theorem bounds_15_28526 : exactInterval 15 28526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28526 : oddCount 28526 15 = 8 ∧ acceleratedOrbit 15 28526 = 5714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28526) = 3 ^ 8 * m + 5714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28526.1, data_15_28526.2]

/-- Complete interval computation for depth 15, residue 28527. -/
theorem bounds_15_28527 : exactInterval 15 28527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28527 : oddCount 28527 15 = 10 ∧ acceleratedOrbit 15 28527 = 51410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28527) = 3 ^ 10 * m + 51410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28527.1, data_15_28527.2]

/-- Complete interval computation for depth 15, residue 28528. -/
theorem bounds_15_28528 : exactInterval 15 28528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28528 : oddCount 28528 15 = 7 ∧ acceleratedOrbit 15 28528 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28528) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28528.1, data_15_28528.2]

/-- Complete interval computation for depth 15, residue 28529. -/
theorem bounds_15_28529 : exactInterval 15 28529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28529 : oddCount 28529 15 = 7 ∧ acceleratedOrbit 15 28529 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28529) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28529.1, data_15_28529.2]

/-- Complete interval computation for depth 15, residue 28530. -/
theorem bounds_15_28530 : exactInterval 15 28530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28530 : oddCount 28530 15 = 6 ∧ acceleratedOrbit 15 28530 = 635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28530) = 3 ^ 6 * m + 635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28530.1, data_15_28530.2]

/-- Complete interval computation for depth 15, residue 28531. -/
theorem bounds_15_28531 : exactInterval 15 28531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28531 : oddCount 28531 15 = 6 ∧ acceleratedOrbit 15 28531 = 635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28531) = 3 ^ 6 * m + 635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28531.1, data_15_28531.2]

/-- Complete interval computation for depth 15, residue 28532. -/
theorem bounds_15_28532 : exactInterval 15 28532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28532 : oddCount 28532 15 = 7 ∧ acceleratedOrbit 15 28532 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28532) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28532.1, data_15_28532.2]

/-- Complete interval computation for depth 15, residue 28533. -/
theorem bounds_15_28533 : exactInterval 15 28533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28533 : oddCount 28533 15 = 7 ∧ acceleratedOrbit 15 28533 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28533) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28533.1, data_15_28533.2]

/-- Complete interval computation for depth 15, residue 28534. -/
theorem bounds_15_28534 : exactInterval 15 28534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28534 : oddCount 28534 15 = 6 ∧ acceleratedOrbit 15 28534 = 635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28534) = 3 ^ 6 * m + 635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28534.1, data_15_28534.2]

/-- Complete interval computation for depth 15, residue 28535. -/
theorem bounds_15_28535 : exactInterval 15 28535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28535 : oddCount 28535 15 = 6 ∧ acceleratedOrbit 15 28535 = 635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28535) = 3 ^ 6 * m + 635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28535.1, data_15_28535.2]

/-- Complete interval computation for depth 15, residue 28536. -/
theorem bounds_15_28536 : exactInterval 15 28536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28536 : oddCount 28536 15 = 9 ∧ acceleratedOrbit 15 28536 = 17147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28536) = 3 ^ 9 * m + 17147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28536.1, data_15_28536.2]

/-- Complete interval computation for depth 15, residue 28537. -/
theorem bounds_15_28537 : exactInterval 15 28537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28537 : oddCount 28537 15 = 9 ∧ acceleratedOrbit 15 28537 = 17144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28537) = 3 ^ 9 * m + 17144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28537.1, data_15_28537.2]

/-- Complete interval computation for depth 15, residue 28538. -/
theorem bounds_15_28538 : exactInterval 15 28538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28538 : oddCount 28538 15 = 9 ∧ acceleratedOrbit 15 28538 = 17147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28538) = 3 ^ 9 * m + 17147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28538.1, data_15_28538.2]

/-- Complete interval computation for depth 15, residue 28539. -/
theorem bounds_15_28539 : exactInterval 15 28539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28539 : oddCount 28539 15 = 10 ∧ acceleratedOrbit 15 28539 = 51434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28539) = 3 ^ 10 * m + 51434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28539.1, data_15_28539.2]

end Collatz.Research.PassageAtlas.Batch0871
