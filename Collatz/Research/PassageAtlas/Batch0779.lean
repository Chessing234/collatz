import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0779

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25493. -/
theorem bounds_15_25493 : exactInterval 15 25493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25493 : oddCount 25493 15 = 6 ∧ acceleratedOrbit 15 25493 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25493) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25493.1, data_15_25493.2]

/-- Complete interval computation for depth 15, residue 25494. -/
theorem bounds_15_25494 : exactInterval 15 25494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25494 : oddCount 25494 15 = 7 ∧ acceleratedOrbit 15 25494 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25494) = 3 ^ 7 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25494.1, data_15_25494.2]

/-- Complete interval computation for depth 15, residue 25495. -/
theorem bounds_15_25495 : exactInterval 15 25495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25495 : oddCount 25495 15 = 7 ∧ acceleratedOrbit 15 25495 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25495) = 3 ^ 7 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25495.1, data_15_25495.2]

/-- Complete interval computation for depth 15, residue 25496. -/
theorem bounds_15_25496 : exactInterval 15 25496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25496 : oddCount 25496 15 = 6 ∧ acceleratedOrbit 15 25496 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25496) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25496.1, data_15_25496.2]

/-- Complete interval computation for depth 15, residue 25497. -/
theorem bounds_15_25497 : exactInterval 15 25497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25497 : oddCount 25497 15 = 7 ∧ acceleratedOrbit 15 25497 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25497) = 3 ^ 7 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25497.1, data_15_25497.2]

/-- Complete interval computation for depth 15, residue 25498. -/
theorem bounds_15_25498 : exactInterval 15 25498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25498 : oddCount 25498 15 = 6 ∧ acceleratedOrbit 15 25498 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25498) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25498.1, data_15_25498.2]

/-- Complete interval computation for depth 15, residue 25499. -/
theorem bounds_15_25499 : exactInterval 15 25499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25499 : oddCount 25499 15 = 7 ∧ acceleratedOrbit 15 25499 = 1702 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25499) = 3 ^ 7 * m + 1702 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25499.1, data_15_25499.2]

/-- Complete interval computation for depth 15, residue 25500. -/
theorem bounds_15_25500 : exactInterval 15 25500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25500 : oddCount 25500 15 = 8 ∧ acceleratedOrbit 15 25500 = 5107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25500) = 3 ^ 8 * m + 5107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25500.1, data_15_25500.2]

/-- Complete interval computation for depth 15, residue 25501. -/
theorem bounds_15_25501 : exactInterval 15 25501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25501 : oddCount 25501 15 = 8 ∧ acceleratedOrbit 15 25501 = 5107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25501) = 3 ^ 8 * m + 5107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25501.1, data_15_25501.2]

/-- Complete interval computation for depth 15, residue 25502. -/
theorem bounds_15_25502 : exactInterval 15 25502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25502 : oddCount 25502 15 = 8 ∧ acceleratedOrbit 15 25502 = 5107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25502) = 3 ^ 8 * m + 5107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25502.1, data_15_25502.2]

/-- Complete interval computation for depth 15, residue 25503. -/
theorem bounds_15_25503 : exactInterval 15 25503 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25503) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25503 : oddCount 25503 15 = 9 ∧ acceleratedOrbit 15 25503 = 15320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25503) = 3 ^ 9 * m + 15320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25503.1, data_15_25503.2]

/-- Complete interval computation for depth 15, residue 25504. -/
theorem bounds_15_25504 : exactInterval 15 25504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25504 : oddCount 25504 15 = 5 ∧ acceleratedOrbit 15 25504 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25504) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25504.1, data_15_25504.2]

/-- Complete interval computation for depth 15, residue 25505. -/
theorem bounds_15_25505 : exactInterval 15 25505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25505 : oddCount 25505 15 = 7 ∧ acceleratedOrbit 15 25505 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25505) = 3 ^ 7 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25505.1, data_15_25505.2]

/-- Complete interval computation for depth 15, residue 25506. -/
theorem bounds_15_25506 : exactInterval 15 25506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25506 : oddCount 25506 15 = 6 ∧ acceleratedOrbit 15 25506 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25506) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25506.1, data_15_25506.2]

/-- Complete interval computation for depth 15, residue 25507. -/
theorem bounds_15_25507 : exactInterval 15 25507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25507 : oddCount 25507 15 = 6 ∧ acceleratedOrbit 15 25507 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25507) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25507.1, data_15_25507.2]

/-- Complete interval computation for depth 15, residue 25508. -/
theorem bounds_15_25508 : exactInterval 15 25508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25508 : oddCount 25508 15 = 7 ∧ acceleratedOrbit 15 25508 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25508) = 3 ^ 7 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25508.1, data_15_25508.2]

/-- Complete interval computation for depth 15, residue 25509. -/
theorem bounds_15_25509 : exactInterval 15 25509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25509 : oddCount 25509 15 = 7 ∧ acceleratedOrbit 15 25509 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25509) = 3 ^ 7 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25509.1, data_15_25509.2]

/-- Complete interval computation for depth 15, residue 25510. -/
theorem bounds_15_25510 : exactInterval 15 25510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25510 : oddCount 25510 15 = 7 ∧ acceleratedOrbit 15 25510 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25510) = 3 ^ 7 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25510.1, data_15_25510.2]

/-- Complete interval computation for depth 15, residue 25511. -/
theorem bounds_15_25511 : exactInterval 15 25511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25511 : oddCount 25511 15 = 9 ∧ acceleratedOrbit 15 25511 = 15326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25511) = 3 ^ 9 * m + 15326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25511.1, data_15_25511.2]

/-- Complete interval computation for depth 15, residue 25512. -/
theorem bounds_15_25512 : exactInterval 15 25512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25512 : oddCount 25512 15 = 5 ∧ acceleratedOrbit 15 25512 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25512) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25512.1, data_15_25512.2]

/-- Complete interval computation for depth 15, residue 25513. -/
theorem bounds_15_25513 : exactInterval 15 25513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25513 : oddCount 25513 15 = 11 ∧ acceleratedOrbit 15 25513 = 137936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25513) = 3 ^ 11 * m + 137936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25513.1, data_15_25513.2]

/-- Complete interval computation for depth 15, residue 25514. -/
theorem bounds_15_25514 : exactInterval 15 25514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25514 : oddCount 25514 15 = 5 ∧ acceleratedOrbit 15 25514 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25514) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25514.1, data_15_25514.2]

/-- Complete interval computation for depth 15, residue 25515. -/
theorem bounds_15_25515 : exactInterval 15 25515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25515 : oddCount 25515 15 = 9 ∧ acceleratedOrbit 15 25515 = 15329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25515) = 3 ^ 9 * m + 15329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25515.1, data_15_25515.2]

/-- Complete interval computation for depth 15, residue 25516. -/
theorem bounds_15_25516 : exactInterval 15 25516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25516 : oddCount 25516 15 = 8 ∧ acceleratedOrbit 15 25516 = 5111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25516) = 3 ^ 8 * m + 5111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25516.1, data_15_25516.2]

/-- Complete interval computation for depth 15, residue 25517. -/
theorem bounds_15_25517 : exactInterval 15 25517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25517 : oddCount 25517 15 = 8 ∧ acceleratedOrbit 15 25517 = 5111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25517) = 3 ^ 8 * m + 5111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25517.1, data_15_25517.2]

/-- Complete interval computation for depth 15, residue 25518. -/
theorem bounds_15_25518 : exactInterval 15 25518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25518 : oddCount 25518 15 = 8 ∧ acceleratedOrbit 15 25518 = 5111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25518) = 3 ^ 8 * m + 5111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25518.1, data_15_25518.2]

/-- Complete interval computation for depth 15, residue 25519. -/
theorem bounds_15_25519 : exactInterval 15 25519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25519 : oddCount 25519 15 = 6 ∧ acceleratedOrbit 15 25519 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25519) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25519.1, data_15_25519.2]

/-- Complete interval computation for depth 15, residue 25520. -/
theorem bounds_15_25520 : exactInterval 15 25520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25520 : oddCount 25520 15 = 6 ∧ acceleratedOrbit 15 25520 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25520) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25520.1, data_15_25520.2]

/-- Complete interval computation for depth 15, residue 25521. -/
theorem bounds_15_25521 : exactInterval 15 25521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25521 : oddCount 25521 15 = 6 ∧ acceleratedOrbit 15 25521 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25521) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25521.1, data_15_25521.2]

/-- Complete interval computation for depth 15, residue 25522. -/
theorem bounds_15_25522 : exactInterval 15 25522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25522 : oddCount 25522 15 = 6 ∧ acceleratedOrbit 15 25522 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25522) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25522.1, data_15_25522.2]

/-- Complete interval computation for depth 15, residue 25523. -/
theorem bounds_15_25523 : exactInterval 15 25523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25523 : oddCount 25523 15 = 6 ∧ acceleratedOrbit 15 25523 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25523) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25523.1, data_15_25523.2]

/-- Complete interval computation for depth 15, residue 25524. -/
theorem bounds_15_25524 : exactInterval 15 25524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25524 : oddCount 25524 15 = 6 ∧ acceleratedOrbit 15 25524 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25524) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25524.1, data_15_25524.2]

/-- Complete interval computation for depth 15, residue 25525. -/
theorem bounds_15_25525 : exactInterval 15 25525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25525 : oddCount 25525 15 = 6 ∧ acceleratedOrbit 15 25525 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25525) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25525.1, data_15_25525.2]

end Collatz.Research.PassageAtlas.Batch0779
