import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0108

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3506. -/
theorem bounds_15_3506 : exactInterval 15 3506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3506 : oddCount 3506 15 = 7 ∧ acceleratedOrbit 15 3506 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3506) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3506.1, data_15_3506.2]

/-- Complete interval computation for depth 15, residue 3507. -/
theorem bounds_15_3507 : exactInterval 15 3507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3507 : oddCount 3507 15 = 7 ∧ acceleratedOrbit 15 3507 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3507) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3507.1, data_15_3507.2]

/-- Complete interval computation for depth 15, residue 3508. -/
theorem bounds_15_3508 : exactInterval 15 3508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3508 : oddCount 3508 15 = 7 ∧ acceleratedOrbit 15 3508 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3508) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3508.1, data_15_3508.2]

/-- Complete interval computation for depth 15, residue 3509. -/
theorem bounds_15_3509 : exactInterval 15 3509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3509 : oddCount 3509 15 = 7 ∧ acceleratedOrbit 15 3509 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3509) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3509.1, data_15_3509.2]

/-- Complete interval computation for depth 15, residue 3510. -/
theorem bounds_15_3510 : exactInterval 15 3510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3510 : oddCount 3510 15 = 8 ∧ acceleratedOrbit 15 3510 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3510) = 3 ^ 8 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3510.1, data_15_3510.2]

/-- Complete interval computation for depth 15, residue 3511. -/
theorem bounds_15_3511 : exactInterval 15 3511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3511 : oddCount 3511 15 = 8 ∧ acceleratedOrbit 15 3511 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3511) = 3 ^ 8 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3511.1, data_15_3511.2]

/-- Complete interval computation for depth 15, residue 3512. -/
theorem bounds_15_3512 : exactInterval 15 3512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3512 : oddCount 3512 15 = 7 ∧ acceleratedOrbit 15 3512 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3512) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3512.1, data_15_3512.2]

/-- Complete interval computation for depth 15, residue 3513. -/
theorem bounds_15_3513 : exactInterval 15 3513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3513 : oddCount 3513 15 = 7 ∧ acceleratedOrbit 15 3513 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3513) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3513.1, data_15_3513.2]

/-- Complete interval computation for depth 15, residue 3514. -/
theorem bounds_15_3514 : exactInterval 15 3514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3514 : oddCount 3514 15 = 7 ∧ acceleratedOrbit 15 3514 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3514) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3514.1, data_15_3514.2]

/-- Complete interval computation for depth 15, residue 3515. -/
theorem bounds_15_3515 : exactInterval 15 3515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3515 : oddCount 3515 15 = 7 ∧ acceleratedOrbit 15 3515 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3515) = 3 ^ 7 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3515.1, data_15_3515.2]

/-- Complete interval computation for depth 15, residue 3516. -/
theorem bounds_15_3516 : exactInterval 15 3516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3516 : oddCount 3516 15 = 7 ∧ acceleratedOrbit 15 3516 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3516) = 3 ^ 7 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3516.1, data_15_3516.2]

/-- Complete interval computation for depth 15, residue 3517. -/
theorem bounds_15_3517 : exactInterval 15 3517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3517 : oddCount 3517 15 = 7 ∧ acceleratedOrbit 15 3517 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3517) = 3 ^ 7 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3517.1, data_15_3517.2]

/-- Complete interval computation for depth 15, residue 3518. -/
theorem bounds_15_3518 : exactInterval 15 3518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3518 : oddCount 3518 15 = 7 ∧ acceleratedOrbit 15 3518 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3518) = 3 ^ 7 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3518.1, data_15_3518.2]

/-- Complete interval computation for depth 15, residue 3519. -/
theorem bounds_15_3519 : exactInterval 15 3519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3519 : oddCount 3519 15 = 11 ∧ acceleratedOrbit 15 3519 = 19030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3519) = 3 ^ 11 * m + 19030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3519.1, data_15_3519.2]

/-- Complete interval computation for depth 15, residue 3520. -/
theorem bounds_15_3520 : exactInterval 15 3520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3520 : oddCount 3520 15 = 7 ∧ acceleratedOrbit 15 3520 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3520) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3520.1, data_15_3520.2]

/-- Complete interval computation for depth 15, residue 3521. -/
theorem bounds_15_3521 : exactInterval 15 3521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3521 : oddCount 3521 15 = 9 ∧ acceleratedOrbit 15 3521 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3521) = 3 ^ 9 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3521.1, data_15_3521.2]

/-- Complete interval computation for depth 15, residue 3522. -/
theorem bounds_15_3522 : exactInterval 15 3522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3522 : oddCount 3522 15 = 9 ∧ acceleratedOrbit 15 3522 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3522) = 3 ^ 9 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3522.1, data_15_3522.2]

/-- Complete interval computation for depth 15, residue 3523. -/
theorem bounds_15_3523 : exactInterval 15 3523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3523 : oddCount 3523 15 = 9 ∧ acceleratedOrbit 15 3523 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3523) = 3 ^ 9 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3523.1, data_15_3523.2]

/-- Complete interval computation for depth 15, residue 3524. -/
theorem bounds_15_3524 : exactInterval 15 3524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3524 : oddCount 3524 15 = 7 ∧ acceleratedOrbit 15 3524 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3524) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3524.1, data_15_3524.2]

/-- Complete interval computation for depth 15, residue 3525. -/
theorem bounds_15_3525 : exactInterval 15 3525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3525 : oddCount 3525 15 = 7 ∧ acceleratedOrbit 15 3525 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3525) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3525.1, data_15_3525.2]

/-- Complete interval computation for depth 15, residue 3526. -/
theorem bounds_15_3526 : exactInterval 15 3526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3526 : oddCount 3526 15 = 7 ∧ acceleratedOrbit 15 3526 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3526) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3526.1, data_15_3526.2]

/-- Complete interval computation for depth 15, residue 3527. -/
theorem bounds_15_3527 : exactInterval 15 3527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3527 : oddCount 3527 15 = 7 ∧ acceleratedOrbit 15 3527 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3527) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3527.1, data_15_3527.2]

/-- Complete interval computation for depth 15, residue 3528. -/
theorem bounds_15_3528 : exactInterval 15 3528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3528 : oddCount 3528 15 = 6 ∧ acceleratedOrbit 15 3528 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3528) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3528.1, data_15_3528.2]

/-- Complete interval computation for depth 15, residue 3529. -/
theorem bounds_15_3529 : exactInterval 15 3529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3529 : oddCount 3529 15 = 7 ∧ acceleratedOrbit 15 3529 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3529) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3529.1, data_15_3529.2]

/-- Complete interval computation for depth 15, residue 3530. -/
theorem bounds_15_3530 : exactInterval 15 3530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3530 : oddCount 3530 15 = 6 ∧ acceleratedOrbit 15 3530 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3530) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3530.1, data_15_3530.2]

/-- Complete interval computation for depth 15, residue 3531. -/
theorem bounds_15_3531 : exactInterval 15 3531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3531 : oddCount 3531 15 = 9 ∧ acceleratedOrbit 15 3531 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3531) = 3 ^ 9 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3531.1, data_15_3531.2]

/-- Complete interval computation for depth 15, residue 3532. -/
theorem bounds_15_3532 : exactInterval 15 3532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3532 : oddCount 3532 15 = 6 ∧ acceleratedOrbit 15 3532 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3532) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3532.1, data_15_3532.2]

/-- Complete interval computation for depth 15, residue 3533. -/
theorem bounds_15_3533 : exactInterval 15 3533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3533 : oddCount 3533 15 = 6 ∧ acceleratedOrbit 15 3533 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3533) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3533.1, data_15_3533.2]

/-- Complete interval computation for depth 15, residue 3534. -/
theorem bounds_15_3534 : exactInterval 15 3534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3534 : oddCount 3534 15 = 10 ∧ acceleratedOrbit 15 3534 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3534) = 3 ^ 10 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3534.1, data_15_3534.2]

/-- Complete interval computation for depth 15, residue 3535. -/
theorem bounds_15_3535 : exactInterval 15 3535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3535 : oddCount 3535 15 = 10 ∧ acceleratedOrbit 15 3535 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3535) = 3 ^ 10 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3535.1, data_15_3535.2]

/-- Complete interval computation for depth 15, residue 3536. -/
theorem bounds_15_3536 : exactInterval 15 3536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3536 : oddCount 3536 15 = 7 ∧ acceleratedOrbit 15 3536 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3536) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3536.1, data_15_3536.2]

/-- Complete interval computation for depth 15, residue 3537. -/
theorem bounds_15_3537 : exactInterval 15 3537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3537 : oddCount 3537 15 = 6 ∧ acceleratedOrbit 15 3537 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3537) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3537.1, data_15_3537.2]

end Collatz.Research.PassageAtlas.Batch0108
